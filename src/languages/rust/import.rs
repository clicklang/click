//! Refresh runs the pinned exporter; ordinary loading only checks locked inputs.
use super::schema::RustExport;
use crate::languages::envelope::{self, Entry, SourceParts};
use crate::languages::inputs::{Leaf, hex_digest};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct PreparedRustImport {
    inner: Arc<Inner>,
}
#[derive(Debug)]
struct Inner {
    export: RustExport,
    function_index: std::collections::BTreeMap<String, Option<usize>>,
    identity: String,
    execution: crate::languages::ExecutionCache,
}
impl PreparedRustImport {
    /// Check a selected local-reference frontier against this immutable,
    /// locked compiler import. This evidence does not grant memory authority.
    pub fn certify_scalar_reference_end(
        &self,
        function_name: &str,
        borrow: super::borrow_frontiers::MirPoint,
        end: super::borrow_frontiers::MirPoint,
    ) -> Result<
        super::borrow_frontiers::CheckedScalarReferenceEnd<'_>,
        super::borrow_frontiers::FrontierRefusal,
    > {
        let index = self
            .inner
            .function_index
            .get(function_name)
            .and_then(|index| *index)
            .ok_or(super::borrow_frontiers::FrontierRefusal::UnsupportedBorrow)?;
        let function = &self.inner.export.functions[index];
        super::borrow_frontiers::certify_scalar_reference_end(
            function,
            &self.inner.identity,
            borrow,
            end,
        )
    }

    pub fn logical_source(&self) -> &str {
        &self.inner.export.logical_source
    }
    /// This import under the name a sidecar's `verifying` declaration gives
    /// its crate root; a project unit's crate root is named by its path in
    /// the unit.
    pub(crate) fn named(&self, logical_source: &str) -> Self {
        if self.logical_source() == logical_source {
            return self.clone();
        }
        let mut export = self.inner.export.clone();
        export.logical_source = logical_source.to_string();
        Self {
            inner: Arc::new(Inner {
                function_index: index_functions(&export),
                export,
                identity: self.inner.identity.clone(),
                execution: Default::default(),
            }),
        }
    }
    pub fn identity(&self) -> &str {
        &self.inner.identity
    }
    pub fn export(&self) -> &RustExport {
        &self.inner.export
    }
    pub(crate) fn prepared_execution(
        &self,
    ) -> Result<Arc<crate::languages::PreparedExecution>, String> {
        self.inner
            .execution
            .get_or_lower(|| super::prepare_execution(self))
    }
}
fn index_functions(export: &RustExport) -> std::collections::BTreeMap<String, Option<usize>> {
    let mut index = std::collections::BTreeMap::new();
    for (position, function) in export.functions.iter().enumerate() {
        index
            .entry(function.name.clone())
            .and_modify(|value| *value = None)
            .or_insert(Some(position));
    }
    index
}

#[cfg(test)]
pub(super) fn prepared_for_test(export: RustExport) -> Result<PreparedRustImport, String> {
    super::lowering::lower(&export)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            function_index: index_functions(&export),
            export,
            identity: "charon-authority-test".into(),
            execution: Default::default(),
        }),
    })
}
/// A unit's extraction: its source and, for a crate, the crate description.
struct Config {
    source: String,
    crate_config: Option<super::crate_inputs::CrateConfig>,
}
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config: String,
    source: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    exporter: String,
    artifact: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    frontend: Option<super::profile::FrontendIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    charon_driver: Option<String>,
    /// A project unit's crate files with their digests, so a changed file
    /// can be named; `source` remains the authoritative digest.
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    source_files: std::collections::BTreeMap<String, String>,
}
/// A Rust unit's section of its project lock entry: what the envelope's
/// common fields do not record (`crate::languages::envelope`).
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Section {
    schema: u32,
    /// The digest of the crate's source closure, which loading recomputes.
    source: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    frontend: Option<super::profile::FrontendIdentity>,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    exporter: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    charon_driver: Option<String>,
    /// For a lock in the earlier schema, the semantic profile it was
    /// extracted under, which loading compares with the current one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    semantic_profile: Option<String>,
}

const LANGUAGE: &str = "rust";

/// The envelope entry recording `lock` for `unit`, whose artifact has
/// `bytes` bytes. The crate root's inputs are the crate files.
fn lock_entry(
    unit: &UnitConfig,
    lock: &Lock,
    bytes: usize,
    semantic_profile: Option<String>,
) -> Result<Entry, String> {
    let project = unit
        .project_file
        .parent()
        .ok_or("project file has no parent directory")?;
    let artifact = unit
        .artifact
        .strip_prefix(project)
        .map_err(|_| "a Rust artifact lies in its project".to_string())?
        .to_string_lossy()
        .into_owned();
    let frontend = match &lock.frontend {
        Some(frontend) => hex_digest(serde_json::to_string(frontend).unwrap().as_bytes()),
        None => hex_digest(
            format!(
                "{}\n{}",
                lock.exporter,
                lock.charon_driver.as_deref().unwrap_or_default()
            )
            .as_bytes(),
        ),
    };
    let section = Section {
        schema: lock.schema,
        source: lock.source.clone(),
        frontend: lock.frontend.clone(),
        exporter: lock.exporter.clone(),
        charon_driver: lock.charon_driver.clone(),
        semantic_profile,
    };
    Ok(Entry::new(
        LANGUAGE,
        lock.config.clone(),
        envelope::Frontend {
            name: "charon".into(),
            identity: frontend,
        },
        std::collections::BTreeMap::from([(
            unit.source.clone(),
            SourceParts {
                inputs: lock.source_files.clone(),
                artifact: envelope::Artifact {
                    path: artifact,
                    sha256: lock.artifact.clone(),
                    bytes,
                },
            },
        )]),
        serde_json::to_value(section).expect("a Rust lock section serializes"),
    ))
}

/// The lock `entry` records for `unit`, and the semantic profile an earlier
/// lock was extracted under.
fn entry_lock(unit: &UnitConfig, entry: &Entry) -> Result<(Lock, Option<String>), String> {
    let section = Section::deserialize(entry.section(LANGUAGE).expect("parsed for Rust"))
        .map_err(|error| format!("parse the Rust lock section: {error}"))?;
    let recorded = entry.sources.get(&unit.source).ok_or_else(|| {
        format!(
            "the project lock has no source `{}`; run `click import lock`",
            unit.source
        )
    })?;
    let lock = Lock {
        schema: section.schema,
        config: entry.unit.clone(),
        source: section.source,
        exporter: section.exporter,
        artifact: recorded.artifact.sha256.clone(),
        frontend: section.frontend,
        charon_driver: section.charon_driver,
        source_files: recorded.inputs.clone(),
    };
    Ok((lock, section.semantic_profile))
}

// The artifact schema is independent of the Rust lock's schema.
const LEGACY_LOCK_SCHEMA: u32 = 8;
const RELEASE_LOCK_SCHEMA: u32 = 9;
impl Lock {
    /// Whether the front end that extracted the lock is the current one: the
    /// current release for a release lock, and for a lock in the earlier
    /// schema, the current semantic profile, which its entry records.
    fn frontend_matches(&self, semantic_profile: Option<&str>) -> bool {
        match (self.schema, &self.frontend) {
            (RELEASE_LOCK_SCHEMA, Some(frontend)) => {
                self.exporter.is_empty()
                    && self.charon_driver.is_none()
                    && semantic_profile.is_none()
                    && frontend == &super::profile::FrontendIdentity::current()
            }
            (LEGACY_LOCK_SCHEMA, None) => {
                self.charon_driver.is_some()
                    && semantic_profile == Some(super::profile::get().semantic_identity().as_str())
            }
            _ => false,
        }
    }
}

/// Reads a Rust input or artifact, which must itself be a regular file.
fn read(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    crate::languages::inputs::read_regular(path, limit, "Rust input", Leaf::Refuse)
}
fn local_file(root: &Path, name: &str) -> Result<PathBuf, String> {
    let path = Path::new(name);
    if path.components().count() != 1
        || !matches!(path.components().next(), Some(Component::Normal(_)))
    {
        return Err("Rust source/artifact must name files in the import directory".into());
    }
    Ok(root.join(path))
}
fn sources(c: &Config, root: &Path) -> Result<super::crate_inputs::SourceFiles, String> {
    let names = c
        .crate_config
        .as_ref()
        .map_or_else(|| vec![c.source.clone()], |c| c.files.clone());
    let mut files = std::collections::BTreeMap::new();
    let mut total = 0;
    for name in names {
        let path = if c.crate_config.is_some() {
            super::crate_inputs::file(root, &name)?
        } else {
            local_file(root, &name)?
        };
        let bytes = read(&path, 1 << 20)?;
        total += bytes.len();
        if total > 4 << 20 {
            return Err("Rust crate source closure exceeds its byte bound".into());
        }
        files.insert(name, bytes);
    }
    Ok(files)
}
fn source_digest(c: &Config, files: &super::crate_inputs::SourceFiles) -> String {
    if c.crate_config.is_none() {
        return hex_digest(&files[&c.source]);
    }
    let hashes: Vec<_> = files
        .iter()
        .map(|(name, bytes)| (name, hex_digest(bytes)))
        .collect();
    hex_digest(
        format!(
            "{}\n{}",
            super::crate_inputs::PROFILE_ID,
            serde_json::to_string(&hashes).unwrap()
        )
        .as_bytes(),
    )
}
fn decode(
    bytes: &[u8],
    c: &Config,
    files: &super::crate_inputs::SourceFiles,
) -> Result<RustExport, String> {
    let export = if c.crate_config.is_some() {
        super::charon::decode_crate(
            bytes,
            &c.source,
            &files[&c.source],
            c.crate_config.as_ref(),
            Some(files),
        )?
    } else {
        super::charon::decode(bytes, &c.source, &files[&c.source])?
    };
    super::lowering::lower(&export)?;
    Ok(export)
}
/// A Rust import's inputs, from a per-sidecar config or a project unit.
struct Inputs<'a> {
    config: &'a Config,
    /// The digest of the configuration the lock records.
    config_digest: String,
    /// The directory crate files are relative to.
    root: &'a Path,
    source: &'a Path,
    /// The artifact and lock outputs, which no input may be.
    outputs: [PathBuf; 2],
}

/// Runs the pinned exporter on `inputs` and returns the lock and artifact,
/// without writing either. `config_digest` re-reads the configuration to
/// detect a change during extraction.
fn extract(
    inputs: &Inputs<'_>,
    runtime: &super::runtime::Runtime,
    config_digest: &dyn Fn() -> Result<String, String>,
) -> Result<(Lock, Vec<u8>), String> {
    let c = inputs.config;
    let root = inputs.root;
    let exporter = &runtime.executable;
    let source_files = sources(c, root)?;
    let driver = &runtime.driver;
    let crate_files = source_files
        .keys()
        .map(|name| root.join(name))
        .collect::<Vec<_>>();
    crate::languages::inputs::reject_output_collisions(
        &[
            ("Rust artifact", &inputs.outputs[0]),
            ("Rust lock", &inputs.outputs[1]),
        ],
        [
            ("exporter", exporter.as_path()),
            ("Charon driver", driver.as_path()),
            ("source", inputs.source),
        ]
        .into_iter()
        .chain(
            crate_files
                .iter()
                .map(|path| ("crate file", path.as_path())),
        ),
    )?;
    let exporter_bytes = read(exporter, 128 << 20)?;
    let driver_bytes = read(driver, 128 << 20)?;
    let output_bytes = super::charon::extract_crate(
        runtime,
        inputs.source,
        root,
        c.crate_config.as_ref(),
        c.crate_config.as_ref().map(|_| &source_files),
    )?;
    if driver_bytes != read(driver, 128 << 20)? {
        return Err("Charon driver changed during extraction".into());
    }
    decode(&output_bytes, c, &source_files)?;
    if inputs.config_digest != config_digest()?
        || source_files != sources(c, root)?
        || exporter_bytes != read(exporter, 128 << 20)?
    {
        return Err("Rust inputs changed during compiler extraction".into());
    }
    let config_hash = inputs.config_digest.clone();
    let source_hash = source_digest(c, &source_files);
    let artifact_hash = hex_digest(&output_bytes);
    let frontend = super::profile::FrontendIdentity::current();
    let lock = Lock {
        schema: RELEASE_LOCK_SCHEMA,
        frontend: Some(frontend),
        charon_driver: None,
        config: config_hash,
        source: source_hash,
        exporter: String::new(),
        artifact: artifact_hash,
        source_files: Default::default(),
    };
    Ok((lock, output_bytes))
}

fn load_locked(
    c: &Config,
    config_digest: &str,
    root: &Path,
    artifact_path: &Path,
    lock: Lock,
    semantic_profile: Option<&str>,
) -> Result<PreparedRustImport, String> {
    let artifact = read(artifact_path, 4 << 20)?;
    let source_files = sources(c, root)?;
    if lock.source != source_digest(c, &source_files)
        && let Some(name) = lock.source_files.iter().find_map(|(name, expected)| {
            (source_files
                .get(name)
                .map(|bytes| hex_digest(bytes))
                .as_ref()
                != Some(expected))
            .then_some(name)
        })
    {
        return Err(format!(
            "Rust source `{}` differs from its import lock; run `click import lock`",
            root.join(name).display()
        ));
    }
    if !lock.frontend_matches(semantic_profile)
        || lock.config != config_digest
        || lock.source != source_digest(c, &source_files)
        || lock.artifact != hex_digest(&artifact)
    {
        return Err("Rust import lock differs from its inputs; refresh it".into());
    }
    let export = decode(&artifact, c, &source_files)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            function_index: index_functions(&export),
            export,
            identity: String::new(),
            execution: Default::default(),
        }),
    })
}

/// A Rust crate unit of a Click project, as `click.project.json` describes
/// it.
#[derive(Clone, Debug)]
pub(crate) struct UnitConfig {
    pub unit_name: String,
    /// The project file, re-read to detect a change during extraction.
    pub project_file: PathBuf,
    /// The digest of the unit's description, which its lock records.
    pub unit_digest: String,
    /// The unit's source root, absolute.
    pub root: PathBuf,
    /// The crate root, relative to the unit root.
    pub source: String,
    /// The crate description; without one, `source` is a single-file
    /// program.
    pub crate_config: Option<super::crate_inputs::CrateConfig>,
    /// The artifact's absolute path.
    pub artifact: PathBuf,
    pub lock_path: PathBuf,
}

impl UnitConfig {
    /// The import configuration, the directory its files are relative to,
    /// and the crate root's path.
    fn config(&self) -> Result<(Config, PathBuf, PathBuf), String> {
        if !self.source.ends_with(".rs") {
            return Err("a Rust unit source must be a `.rs` crate root".into());
        }
        let unit_root = fs::canonicalize(&self.root)
            .map_err(|error| format!("resolve the root of unit `{}`: {error}", self.unit_name))?;
        let Some(crate_config) = &self.crate_config else {
            // A single-file program is read from its own directory.
            let relative = Path::new(&self.source);
            let root = unit_root.join(relative.parent().unwrap_or(Path::new("")));
            let name = relative
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("a Rust unit source must name a file")?
                .to_string();
            let source = local_file(&root, &name)?;
            let config = Config {
                source: name,
                crate_config: None,
            };
            return Ok((config, root, source));
        };
        crate_config.validate(&self.source)?;
        for name in &crate_config.files {
            super::crate_inputs::file(&unit_root, name)?;
        }
        let source = super::crate_inputs::file(&unit_root, &self.source)?;
        let config = Config {
            source: self.source.clone(),
            crate_config: Some(crate_config.clone()),
        };
        Ok((config, unit_root, source))
    }
}

/// Extracts a project unit with the selected pinned Rust frontend: its lock entry and
/// the artifact to write.
pub(crate) fn prepare_unit(
    unit: &UnitConfig,
) -> Result<(serde_json::Value, Vec<(PathBuf, Vec<u8>)>), String> {
    let (config, root, source) = unit.config()?;
    let runtime = super::runtime::resolve(None)?;
    let inputs = Inputs {
        config: &config,
        config_digest: unit.unit_digest.clone(),
        root: &root,
        source: &source,
        outputs: [unit.artifact.clone(), unit.lock_path.clone()],
    };
    let project_file = unit.project_file.clone();
    let name = unit.unit_name.clone();
    let (mut lock, artifact) = extract(&inputs, &runtime, &move || {
        crate::project::Project::load(&project_file)?.unit_digest(&name)
    })?;
    lock.source_files = sources(&config, &root)?
        .iter()
        .map(|(name, bytes)| (name.clone(), hex_digest(bytes)))
        .collect();
    let entry = lock_entry(unit, &lock, artifact.len(), None)?;
    let value = serde_json::to_value(entry).map_err(|e| e.to_string())?;
    Ok((value, vec![(unit.artifact.clone(), artifact)]))
}

/// Loads a project unit from its lock entry.
pub(crate) fn load_unit(
    unit: &UnitConfig,
    lock: &serde_json::Value,
) -> Result<PreparedRustImport, String> {
    let (config, root, _) = unit.config()?;
    let entry = Entry::parse(LANGUAGE, &unit.unit_name, lock)?;
    let (lock, semantic_profile) = entry_lock(unit, &entry)?;
    if lock.config != unit.unit_digest {
        return Err(format!(
            "the project lock for unit `{}` does not match its description in `click.project.json`; run `click import lock` to prepare it again",
            unit.unit_name
        ));
    }
    let mut import = load_locked(
        &config,
        &unit.unit_digest,
        &root,
        &unit.artifact,
        lock,
        semantic_profile.as_deref(),
    )?;
    // The identity is checked after the inputs and artifact, so a changed
    // input is named before a mismatched identity.
    Arc::get_mut(&mut import.inner)
        .expect("a freshly loaded import is not shared")
        .identity = entry.checked_identity(LANGUAGE, &unit.source)?;
    Ok(import)
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn rust_entries_load_only_under_their_own_front_end() {
        assert_eq!(super::super::profile::get().identity, "click-rust-v1");
        let root = tempfile::tempdir().unwrap();
        let example =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/gate-fixtures/basic");
        for name in ["borrow.rs", "click.project.json"] {
            fs::copy(example.join(name), root.path().join(name)).unwrap();
        }
        let artifact = ".click/borrow/borrow.rs.ullbc";
        fs::create_dir_all(root.path().join(".click/borrow")).unwrap();
        fs::copy(example.join(artifact), root.path().join(artifact)).unwrap();
        let bytes = fs::metadata(root.path().join(artifact)).unwrap().len() as usize;
        let project =
            crate::project::Project::load(&root.path().join("click.project.json")).unwrap();
        let unit = project.rust_unit("borrow").unwrap();
        let saved: serde_json::Value =
            serde_json::from_slice(&fs::read(example.join("click.project.lock.json")).unwrap())
                .unwrap();
        let saved = saved["units"]["borrow"]["lock"].clone();
        // The committed entry is in the earlier schema and records the
        // semantic profile it was extracted under.
        let entry = Entry::parse(LANGUAGE, "borrow", &saved).unwrap();
        let (mut lock, semantic_profile) = entry_lock(&unit, &entry).unwrap();
        assert_eq!(lock.schema, LEGACY_LOCK_SCHEMA);
        assert_eq!(
            load_unit(&unit, &saved).unwrap().identity(),
            entry.sources["borrow.rs"].identity
        );
        let reload = |lock: &Lock, semantic_profile: Option<String>| {
            let entry = lock_entry(&unit, lock, bytes, semantic_profile).unwrap();
            load_unit(&unit, &serde_json::to_value(entry).unwrap())
        };
        reload(&lock, semantic_profile.clone()).unwrap();
        // Another semantic profile, or none, is refused, even in a
        // self-consistent entry.
        for other in [Some("other".to_string()), None] {
            assert!(reload(&lock, other).unwrap_err().contains("lock differs"));
        }
        // A release entry loads only with the current release pins.
        lock.exporter.clear();
        lock.charon_driver = None;
        lock.schema = RELEASE_LOCK_SCHEMA;
        let frontend = super::super::profile::FrontendIdentity::current();
        lock.frontend = Some(frontend.clone());
        reload(&lock, None).unwrap();
        assert!(reload(&lock, semantic_profile).is_err());
        for field in [
            "click_version",
            "extractor_revision",
            "extractor_version",
            "compiler_commit",
            "profile",
        ] {
            let mut changed = serde_json::to_value(&frontend).unwrap();
            changed[field] = "different".into();
            lock.frontend = Some(serde_json::from_value(changed).unwrap());
            assert!(reload(&lock, None).is_err(), "{field}");
        }
        lock.frontend = Some(frontend);
        let release = serde_json::to_value(lock_entry(&unit, &lock, bytes, None).unwrap()).unwrap();
        for (field, value) in [
            ("frontend", serde_json::Value::Null),
            ("exporter", "binary hash".into()),
            ("charon_driver", "binary hash".into()),
            ("schema", 8.into()),
        ] {
            let mut mixed = release.clone();
            mixed["rust"][field] = value;
            assert!(load_unit(&unit, &mixed).is_err(), "{field}");
        }
    }

    /// A project unit for an external crate, locked by hand from the
    /// committed adler2 artifact: the sidecar names the crate root by its own
    /// relative path, verifies, and a changed crate file is refused by name.
    #[test]
    fn project_unit_loads_an_external_crate_offline() {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
                "click-rust-unit-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
        let trial = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/adler2");
        let crate_root = root.join("vendor/adler2-2.0.1");
        let proofs = root.join("proofs");
        fs::create_dir_all(crate_root.join("src")).unwrap();
        fs::create_dir_all(proofs.join(".click/adler2/src")).unwrap();
        for file in ["src/lib.rs", "src/algo.rs"] {
            fs::copy(trial.join(file), crate_root.join(file)).unwrap();
        }
        let artifact = fs::read(trial.join(".click/adler2/src/lib.rs.ullbc")).unwrap();
        fs::write(proofs.join(".click/adler2/src/lib.rs.ullbc"), &artifact).unwrap();
        let proof = fs::read_to_string(trial.join("restoration.click"))
            .unwrap()
            .replace(
                "verifying \"src/lib.rs\";",
                "verifying \"../vendor/adler2-2.0.1/src/lib.rs\";",
            );
        let sidecar = proofs.join("restoration.click");
        fs::write(&sidecar, &proof).unwrap();
        let project_file = proofs.join(crate::project::FILE_NAME);
        fs::write(
            &project_file,
            serde_json::json!({"units": {"adler2": {
                "language": "rust",
                "root": "../vendor/adler2-2.0.1",
                "crate": {"name": "adler2", "edition": "2021", "features": ["std"],
                    "roots": ["adler2::adler32_slice", "adler2::Adler32::from_checksum"],
                    "files": ["src/lib.rs", "src/algo.rs"]},
                "sources": {"src/lib.rs": {}}
            }}})
            .to_string(),
        )
        .unwrap();
        let project = crate::project::Project::load(&project_file).unwrap();
        let unit = project.rust_unit("adler2").unwrap();
        let (config, unit_root, _) = unit.config().unwrap();
        let files = sources(&config, &unit_root).unwrap();
        let source = source_digest(&config, &files);
        let (exporter, driver, artifact_hash) = (
            hex_digest(b"charon"),
            hex_digest(b"driver"),
            hex_digest(&artifact),
        );
        let lock = Lock {
            schema: LEGACY_LOCK_SCHEMA,
            frontend: None,
            config: unit.unit_digest.clone(),
            source,
            exporter,
            artifact: artifact_hash,
            charon_driver: Some(driver),
            source_files: files
                .iter()
                .map(|(name, bytes)| (name.clone(), hex_digest(bytes)))
                .collect(),
        };
        fs::write(
            proofs.join(crate::project::LOCK_NAME),
            serde_json::json!({"schema": 1, "units": {"adler2": {
                "language": "rust",
                "lock": lock_entry(
                    &unit,
                    &lock,
                    artifact.len(),
                    Some(super::super::profile::get().semantic_identity()),
                )
                .unwrap()
            }}})
            .to_string(),
        )
        .unwrap();

        let load = || match crate::cli::read_c_inputs(&sidecar, &proof)? {
            crate::cli::CInput::PreparedProgram(program) => Ok(program),
            _ => Err("expected the unit's prepared crate".to_string()),
        };
        let program = load().unwrap();
        assert_eq!(
            program.logical_source(),
            "../vendor/adler2-2.0.1/src/lib.rs"
        );
        let click_project = crate::cli::read_lone_sidecar_project(&sidecar, &proof).unwrap();
        let verified =
            crate::surface::verify_program_prepared_project(&click_project, &program).unwrap();
        assert!(!verified.is_empty());

        fs::write(crate_root.join("src/algo.rs"), "// edited\n").unwrap();
        let error = load().unwrap_err();
        assert!(
            error.contains("algo.rs") && error.contains("differs from its import lock"),
            "{error}"
        );
        let _ = fs::remove_dir_all(&root);
    }
}
