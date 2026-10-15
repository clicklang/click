//! Click project configuration: the root `click.project.json`.
//!
//! The project file sits at a project's root and is found from any sidecar
//! beneath it as the nearest ancestor directory that contains one. Besides
//! the project's target and runtime, it declares the project's *units*: the
//! code under verification, each with a language, a source root and Click's
//! own description of how it is built. A unit's root may be the project
//! itself or an external tree the user manages, such as a git submodule;
//! Click reads it in place, imposes no layout or names on it, and never
//! writes into it. `click import lock` prepares every unit into one lock
//! beside the project file, with the artifacts under `.click/`, and
//! verification loads them offline.
//!
//! A sidecar selects a unit's source with an ordinary `verifying` path,
//! relative to the sidecar, that names a file the unit lists.
//!
//! A C unit lists translation units that its compiler preprocesses. A Rust
//! unit is one crate and lists its root; the pinned Charon named by
//! `CLICK_CHARON` extracts it at lock time, and the crate's `roots` are the
//! entry points every sidecar verifying it sees.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::languages::PreparedProgram;
use crate::languages::c::compiler_import::{self, PreparedCImport, UnitConfig, UnitSource};
use crate::languages::c::target::CTarget;
use crate::languages::rust::{self as rust_import, CrateConfig};

/// The project file's name.
pub const FILE_NAME: &str = "click.project.json";
/// The project lock's name, beside the project file.
pub const LOCK_NAME: &str = "click.project.lock.json";
/// The directory, beside the project file, that holds prepared artifacts.
pub const ARTIFACT_DIRECTORY: &str = ".click";

const LOCK_SCHEMA: u32 = 1;
const MAX_PROJECT_FILE_BYTES: u64 = 1 << 20;
const MAX_LOCK_BYTES: u64 = 16 << 20;
const MAX_UNITS: usize = 256;

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct UnitJson {
    language: String,
    #[serde(default = "project_directory")]
    root: String,
    compiler: Option<String>,
    #[serde(default)]
    environment: BTreeMap<String, String>,
    option_profile: Option<String>,
    /// Arguments every source of the unit is prepared with, before its own.
    #[serde(default)]
    args: Vec<String>,
    /// A Rust unit's crate description.
    #[serde(default, rename = "crate")]
    crate_config: Option<CrateConfig>,
    sources: BTreeMap<String, SourceJson>,
}

/// The prepared inputs a sidecar selects from a project's units.
#[derive(Clone, Debug)]
pub enum UnitSelection {
    /// C translation units, one per `verifying` source.
    C(Vec<PreparedCImport>),
    /// One crate.
    Program(PreparedProgram),
}

fn project_directory() -> String {
    ".".to_string()
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceJson {
    #[serde(default)]
    args: Vec<String>,
    projection: Option<String>,
}

#[derive(Clone, Debug)]
struct Unit {
    /// The unit's description as written, which its digest covers.
    description: serde_json::Value,
    spec: UnitJson,
}

/// A loaded `click.project.json`.
#[derive(Clone, Debug)]
pub struct Project {
    /// The project file, absolute and canonical.
    file: PathBuf,
    /// The project root: the project file's directory.
    root: PathBuf,
    target: Option<String>,
    units: BTreeMap<String, Unit>,
}

impl Project {
    /// The project whose file is in `directory` or its nearest ancestor that
    /// has one, if any.
    pub fn find(directory: &Path) -> Result<Option<Self>, String> {
        let start = match fs::canonicalize(directory) {
            Ok(start) => start,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(format!(
                    "failed to resolve `{}`: {error}",
                    directory.display()
                ));
            }
        };
        for candidate in start.ancestors() {
            let file = candidate.join(FILE_NAME);
            match fs::symlink_metadata(&file) {
                Ok(_) => return Self::load(&file).map(Some),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(format!("failed to inspect `{}`: {error}", file.display()));
                }
            }
        }
        Ok(None)
    }

    /// Loads the project file at `file`.
    pub fn load(file: &Path) -> Result<Self, String> {
        let file = fs::canonicalize(file)
            .map_err(|error| format!("failed to resolve `{}`: {error}", file.display()))?;
        let bytes = read_bounded(&file, MAX_PROJECT_FILE_BYTES)?;
        let value: serde_json::Value = serde_json::from_slice(&bytes).map_err(|error| {
            format!("invalid Click project config `{}`: {error}", file.display())
        })?;
        let target = value
            .get("target")
            .and_then(serde_json::Value::as_str)
            .map(str::to_string);
        let mut units = BTreeMap::new();
        if let Some(described) = value.get("units") {
            let described = described
                .as_object()
                .ok_or_else(|| format!("`units` in `{}` must be an object", file.display()))?;
            if described.len() > MAX_UNITS {
                return Err(format!(
                    "`{}` declares more than {MAX_UNITS} units",
                    file.display()
                ));
            }
            for (name, description) in described {
                validate_unit_name(name)?;
                let spec = UnitJson::deserialize(description)
                    .map_err(|error| format!("unit `{name}` in `{}`: {error}", file.display()))?;
                validate_unit(name, &spec)?;
                units.insert(
                    name.clone(),
                    Unit {
                        description: description.clone(),
                        spec,
                    },
                );
            }
        }
        let root = file
            .parent()
            .ok_or("project file has no parent directory")?
            .to_path_buf();
        Ok(Self {
            file,
            root,
            target,
            units,
        })
    }

    /// The project root: the directory of the project file.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Whether the project declares any units.
    pub fn has_units(&self) -> bool {
        !self.units.is_empty()
    }

    fn lock_path(&self) -> PathBuf {
        self.root.join(LOCK_NAME)
    }

    fn target_name(&self) -> String {
        self.target
            .clone()
            .unwrap_or_else(|| CTarget::SUPPORTED.name().to_string())
    }

    /// The digest of unit `name`'s description and the project target it is
    /// prepared for. A unit's lock entry records it.
    pub(crate) fn unit_digest(&self, name: &str) -> Result<String, String> {
        let unit = self
            .units
            .get(name)
            .ok_or_else(|| format!("`{}` has no unit `{name}`", self.file.display()))?;
        let data = serde_json::to_vec(&serde_json::json!({
            "target": self.target_name(),
            "unit": unit.description,
        }))
        .expect("a unit description serializes");
        Ok(hex_digest(&data))
    }

    pub(crate) fn c_unit(&self, name: &str) -> Result<UnitConfig, String> {
        let unit = &self.units[name];
        let compiler = unit.spec.compiler.as_ref().ok_or_else(|| {
            format!(
                "C unit `{name}` needs a `compiler`; plain C that Click preprocesses itself needs no unit"
            )
        })?;
        Ok(UnitConfig {
            project_file: self.file.clone(),
            lock_path: self.lock_path(),
            unit_name: name.to_string(),
            unit_digest: self.unit_digest(name)?,
            target: self.target_name(),
            compiler: PathBuf::from(compiler),
            root: unit.spec.root.clone(),
            environment: unit.spec.environment.clone(),
            option_profile: unit.spec.option_profile.clone(),
            sources: unit
                .spec
                .sources
                .iter()
                .map(|(path, source)| UnitSource {
                    path: path.clone(),
                    args: unit.spec.args.iter().chain(&source.args).cloned().collect(),
                    artifact: format!("{ARTIFACT_DIRECTORY}/{name}/{path}.i"),
                    projection: source.projection.clone(),
                })
                .collect(),
        })
    }

    pub(crate) fn rust_unit(&self, name: &str) -> Result<rust_import::UnitConfig, String> {
        let unit = &self.units[name];
        let source = unit
            .spec
            .sources
            .keys()
            .next()
            .expect("a validated Rust unit lists its crate root")
            .clone();
        Ok(rust_import::UnitConfig {
            unit_name: name.to_string(),
            project_file: self.file.clone(),
            unit_digest: self.unit_digest(name)?,
            root: self.root.join(&unit.spec.root),
            artifact: self
                .root
                .join(format!("{ARTIFACT_DIRECTORY}/{name}/{source}.ullbc")),
            source,
            crate_config: unit
                .spec
                .crate_config
                .clone()
                .expect("a validated Rust unit has a crate"),
            lock_path: self.lock_path(),
        })
    }

    /// Prepares every unit and writes the project lock and its artifacts.
    pub fn lock(&self) -> Result<(), String> {
        if !self.has_units() {
            return Err(format!(
                "`{}` declares no units to prepare",
                self.file.display()
            ));
        }
        let mut entries = serde_json::Map::new();
        let mut artifacts = Vec::new();
        for (name, unit) in &self.units {
            let (language, lock, unit_artifacts) = match unit.spec.language.as_str() {
                "rust" => {
                    let unit = self.rust_unit(name)?;
                    let exporter = std::env::var_os("CLICK_CHARON").ok_or_else(|| {
                        format!(
                            "set CLICK_CHARON to the pinned Charon executable to prepare Rust unit `{name}`"
                        )
                    })?;
                    create_parent(&unit.artifact)?;
                    let (lock, artifacts) = rust_import::prepare_unit(&unit, Path::new(&exporter))
                        .map_err(|error| format!("unit `{name}`: {error}"))?;
                    ("rust", lock, artifacts)
                }
                _ => {
                    let unit = self.c_unit(name)?;
                    for source in &unit.sources {
                        create_parent(&self.root.join(&source.artifact))?;
                    }
                    let (lock, artifacts) = compiler_import::prepare_unit(&unit)
                        .map_err(|error| format!("unit `{name}`: {error}"))?;
                    ("c", lock, artifacts)
                }
            };
            entries.insert(
                name.clone(),
                serde_json::json!({ "language": language, "lock": lock }),
            );
            artifacts.extend(unit_artifacts);
        }
        let lock = serde_json::json!({ "schema": LOCK_SCHEMA, "units": entries });
        let mut encoded = serde_json::to_vec_pretty(&lock)
            .map_err(|error| format!("encode project lock: {error}"))?;
        encoded.push(b'\n');
        if encoded.len() as u64 > MAX_LOCK_BYTES {
            return Err("project lock exceeds its 16 MiB limit".into());
        }
        for (path, bytes) in &artifacts {
            crate::cli::write_file_atomically(path, bytes)?;
        }
        crate::cli::write_file_atomically(&self.lock_path(), &encoded)
    }

    /// The prepared inputs a sidecar's `verifying` declarations select, given
    /// as `(spelling, canonical path)` pairs, or `None` when no unit lists any
    /// of them.
    pub fn prepared_sources(
        &self,
        requested: &[(String, Option<PathBuf>)],
    ) -> Result<Option<UnitSelection>, String> {
        let mut selected = Vec::with_capacity(requested.len());
        let mut unlisted = Vec::new();
        for (spelling, path) in requested {
            match path.as_deref().and_then(|path| self.unit_source(path)) {
                Some((unit, relative)) => selected.push((spelling, unit, relative)),
                None => unlisted.push(spelling.as_str()),
            }
        }
        if selected.is_empty() {
            return Ok(None);
        }
        if let Some(spelling) = unlisted.first() {
            return Err(format!(
                "`verifying \"{spelling}\"` names no source of a unit in `{}`, but the sidecar's other sources are unit sources; list it in a unit",
                self.file.display()
            ));
        }
        let lock = self.read_lock()?;
        if let Some((spelling, unit, _)) = selected
            .iter()
            .find(|(_, unit, _)| self.units[*unit].spec.language == "rust")
        {
            if selected.len() != 1 {
                return Err(format!(
                    "`verifying \"{spelling}\"` selects the crate of Rust unit `{unit}`, which a sidecar verifies on its own"
                ));
            }
            let import = self.load_rust_unit(unit, &lock)?;
            return Ok(Some(UnitSelection::Program(import.named(spelling).into())));
        }
        let mut loaded = BTreeMap::<&str, BTreeMap<String, PreparedCImport>>::new();
        let mut prepared = Vec::with_capacity(selected.len());
        for (spelling, unit, relative) in selected {
            if !loaded.contains_key(unit) {
                let imports = self.load_c_unit(unit, &lock)?;
                loaded.insert(
                    unit,
                    imports
                        .into_iter()
                        .map(|import| (import.logical_source().to_string(), import))
                        .collect(),
                );
            }
            let import = loaded[unit].get(&relative).ok_or_else(|| {
                format!("the project lock for unit `{unit}` has no source `{relative}`")
            })?;
            prepared.push(import.named(spelling));
        }
        Ok(Some(UnitSelection::C(prepared)))
    }

    /// Whether a unit lists any of the requested sources.
    pub fn lists_any(&self, requested: &[(String, Option<PathBuf>)]) -> bool {
        requested
            .iter()
            .filter_map(|(_, path)| path.as_deref())
            .any(|path| self.unit_source(path).is_some())
    }

    /// The unit that lists the file at canonical `path`, with its path in the
    /// unit.
    fn unit_source(&self, path: &Path) -> Option<(&str, String)> {
        for (name, unit) in &self.units {
            let root = self.root.join(&unit.spec.root);
            let Ok(root) = fs::canonicalize(&root) else {
                continue;
            };
            let Ok(relative) = path.strip_prefix(&root) else {
                continue;
            };
            let relative = relative.to_string_lossy().replace('\\', "/");
            if unit.spec.sources.contains_key(&relative) {
                return Some((name.as_str(), relative));
            }
        }
        None
    }

    fn read_lock(&self) -> Result<serde_json::Value, String> {
        let path = self.lock_path();
        if !path.exists() {
            return Err(format!(
                "project `{}` has no lock; run `click import lock {}`",
                self.root.display(),
                self.root.display()
            ));
        }
        let bytes = read_bounded(&path, MAX_LOCK_BYTES)?;
        let lock: serde_json::Value = serde_json::from_slice(&bytes)
            .map_err(|error| format!("parse project lock `{}`: {error}", path.display()))?;
        if lock.get("schema").and_then(serde_json::Value::as_u64) != Some(u64::from(LOCK_SCHEMA)) {
            return Err(format!(
                "project lock `{}` has an unsupported schema",
                path.display()
            ));
        }
        Ok(lock)
    }

    /// The lock entry of unit `name`, which must be of `language`.
    fn lock_entry<'l>(
        &self,
        name: &str,
        language: &str,
        lock: &'l serde_json::Value,
    ) -> Result<&'l serde_json::Value, String> {
        let entry = lock
            .get("units")
            .and_then(|units| units.get(name))
            .ok_or_else(|| {
                format!(
                    "the project lock has no entry for unit `{name}`; run `click import lock {}`",
                    self.root.display()
                )
            })?;
        if entry.get("language").and_then(serde_json::Value::as_str) != Some(language) {
            return Err(format!(
                "the project lock entry for unit `{name}` is not a `{language}` unit; run `click import lock {}`",
                self.root.display()
            ));
        }
        entry
            .get("lock")
            .ok_or_else(|| format!("the project lock entry for unit `{name}` has no lock"))
    }

    fn load_c_unit(
        &self,
        name: &str,
        lock: &serde_json::Value,
    ) -> Result<Vec<PreparedCImport>, String> {
        let unit_lock = self.lock_entry(name, "c", lock)?;
        compiler_import::load_unit(&self.c_unit(name)?, unit_lock)
            .map_err(|error| format!("unit `{name}`: {error}"))
    }

    fn load_rust_unit(
        &self,
        name: &str,
        lock: &serde_json::Value,
    ) -> Result<rust_import::PreparedRustImport, String> {
        let unit_lock = self.lock_entry(name, "rust", lock)?;
        rust_import::load_unit(&self.rust_unit(name)?, unit_lock)
            .map_err(|error| format!("unit `{name}`: {error}"))
    }
}

fn validate_unit_name(name: &str) -> Result<(), String> {
    if name.is_empty()
        || name.len() > 64
        || !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
    {
        return Err(format!(
            "unit name `{name}` must be 1 to 64 ASCII letters, digits, `_` or `-`"
        ));
    }
    Ok(())
}

fn validate_unit(name: &str, unit: &UnitJson) -> Result<(), String> {
    match unit.language.as_str() {
        "c" => {
            if unit.crate_config.is_some() {
                return Err(format!("C unit `{name}` cannot describe a `crate`"));
            }
        }
        "rust" => {
            if unit.crate_config.is_none() {
                return Err(format!("Rust unit `{name}` needs a `crate` description"));
            }
            if unit.compiler.is_some()
                || !unit.environment.is_empty()
                || unit.option_profile.is_some()
                || !unit.args.is_empty()
            {
                return Err(format!(
                    "Rust unit `{name}` takes no `compiler`, `environment`, `option_profile` or `args`; the pinned Charon prepares it"
                ));
            }
            if unit.sources.len() != 1
                || unit
                    .sources
                    .values()
                    .any(|source| !source.args.is_empty() || source.projection.is_some())
            {
                return Err(format!(
                    "Rust unit `{name}` lists exactly its crate root in `sources`, with no arguments"
                ));
            }
        }
        "c++" => {
            return Err(format!(
                "unit `{name}`: C++ units are not supported in `click.project.json` yet; use a per-sidecar import config"
            ));
        }
        other => return Err(format!("unit `{name}` has unsupported language `{other}`")),
    }
    if unit.root.is_empty() {
        return Err(format!("unit `{name}` has an empty `root`"));
    }
    if unit.sources.is_empty() {
        return Err(format!("unit `{name}` lists no sources"));
    }
    for path in unit.sources.keys() {
        let relative = Path::new(path);
        if path.is_empty()
            || path.contains('\\')
            || relative
                .components()
                .any(|component| !matches!(component, std::path::Component::Normal(_)))
        {
            return Err(format!(
                "unit `{name}` source `{path}` must be a relative path inside the unit root"
            ));
        }
    }
    Ok(())
}

fn create_parent(path: &Path) -> Result<(), String> {
    let parent = path.parent().expect("an artifact path has a parent");
    fs::create_dir_all(parent)
        .map_err(|error| format!("create directory `{}`: {error}", parent.display()))
}

fn read_bounded(path: &Path, max: u64) -> Result<Vec<u8>, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    if !metadata.is_file() || metadata.len() > max {
        return Err(format!(
            "`{}` must be a regular file of at most {max} bytes",
            path.display()
        ));
    }
    fs::read(path).map_err(|error| format!("failed to read `{}`: {error}", path.display()))
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Scratch(PathBuf);

    impl Scratch {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let root = std::env::temp_dir().join(format!(
                "click-project-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&root).unwrap();
            Self(fs::canonicalize(root).unwrap())
        }

        fn write(&self, path: &str, contents: &str) -> PathBuf {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, contents).unwrap();
            path
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn project_with(units: &str) -> (Scratch, Result<Project, String>) {
        let scratch = Scratch::new();
        let file = scratch.write(
            "proofs/click.project.json",
            &format!("{{\"units\": {units}}}"),
        );
        let project = Project::load(&file);
        (scratch, project)
    }

    #[test]
    fn units_refuse_unsupported_descriptions() {
        for (units, expected) in [
            (
                r#"{"cpp": {"language": "c++", "sources": {"a.cpp": {}}}}"#,
                "not supported in `click.project.json` yet",
            ),
            (
                r#"{"rs": {"language": "rust", "sources": {"src/lib.rs": {}}}}"#,
                "needs a `crate` description",
            ),
            (
                r#"{"rs": {"language": "rust", "compiler": "/usr/bin/gcc",
                    "crate": {"name": "a", "edition": "2021", "features": [],
                        "roots": ["a::f"], "files": ["src/lib.rs"]},
                    "sources": {"src/lib.rs": {}}}}"#,
                "takes no `compiler`",
            ),
            (
                r#"{"bad name": {"language": "c", "sources": {"a.c": {}}}}"#,
                "unit name `bad name`",
            ),
            (
                r#"{"up": {"language": "c", "sources": {"../a.c": {}}}}"#,
                "must be a relative path inside the unit root",
            ),
            (
                r#"{"none": {"language": "c", "sources": {}}}"#,
                "lists no sources",
            ),
            (
                r#"{"typo": {"language": "c", "source": {"a.c": {}}}}"#,
                "unknown field `source`",
            ),
        ] {
            let (_scratch, project) = project_with(units);
            let error = project.unwrap_err();
            assert!(error.contains(expected), "{expected}: {error}");
        }
    }

    #[test]
    fn found_from_a_nested_directory_and_selects_unit_sources() {
        let scratch = Scratch::new();
        let source = scratch.write("upstream/src/lib/add.c", "int add(int a, int b);\n");
        let other = scratch.write("proofs/local.c", "int local(void);\n");
        scratch.write(
            "proofs/click.project.json",
            r#"{"units": {"up": {"language": "c", "root": "../upstream",
                "compiler": "/usr/bin/gcc", "sources": {"src/lib/add.c": {}}}}}"#,
        );
        fs::create_dir_all(scratch.0.join("proofs/checks/deep")).unwrap();
        let project = Project::find(&scratch.0.join("proofs/checks/deep"))
            .unwrap()
            .expect("the ancestor project file");
        assert_eq!(project.root(), scratch.0.join("proofs"));
        let listed = [("add.c".to_string(), Some(source))];
        assert!(project.lists_any(&listed));
        assert!(!project.lists_any(&[("local.c".to_string(), Some(other.clone()))]));
        let error = project.prepared_sources(&listed).unwrap_err();
        assert!(
            error.contains("has no lock; run `click import lock"),
            "{error}"
        );
        let mixed = [listed[0].clone(), ("local.c".to_string(), Some(other))];
        let error = project.prepared_sources(&mixed).unwrap_err();
        assert!(
            error.contains("`verifying \"local.c\"` names no source"),
            "{error}"
        );
    }

    #[test]
    fn unit_digest_covers_the_description_and_target() {
        let (_scratch, project) = project_with(
            r#"{"up": {"language": "c", "compiler": "/usr/bin/gcc", "sources": {"a.c": {}}}}"#,
        );
        let project = project.unwrap();
        let digest = project.unit_digest("up").unwrap();
        let mut retargeted = project.clone();
        retargeted.target = Some("x86_64-linux-kernel".into());
        assert_ne!(retargeted.unit_digest("up").unwrap(), digest);
        assert_eq!(project.unit_digest("up").unwrap(), digest);
    }
}
