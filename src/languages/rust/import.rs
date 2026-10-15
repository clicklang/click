//! Refresh runs the pinned exporter; ordinary loading only checks locked inputs.
use super::schema::{RustExport, SCHEMA, TARGET};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::Read;
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
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    language: String,
    target: String,
    source: String,
    #[serde(default)]
    exporter: String,
    artifact: String,
    #[serde(default)]
    backend: Option<String>,
    #[serde(default, rename = "crate")]
    crate_config: Option<super::crate_inputs::CrateConfig>,
}
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config: String,
    source: String,
    exporter: String,
    artifact: String,
    identity: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    charon_driver: Option<String>,
    /// A project unit's crate files with their digests, so a changed file
    /// can be named; `source` remains the authoritative digest.
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    source_files: std::collections::BTreeMap<String, String>,
}
fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn import_identity(
    config: &str,
    source: &str,
    exporter: &str,
    artifact: &str,
    driver: &str,
) -> String {
    let profile = super::profile::get();
    digest(
        format!(
            "{}\n{config}\n{source}\n{exporter}\n{artifact}\n{driver}\n{}",
            profile.identity,
            profile.semantic_identity()
        )
        .as_bytes(),
    )
}

fn read(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    if !fs::symlink_metadata(path)
        .map_err(|e| format!("read `{}`: {e}", path.display()))?
        .file_type()
        .is_file()
    {
        return Err(format!("`{}` must be a regular file", path.display()));
    }
    let f = fs::File::open(path).map_err(|e| e.to_string())?;
    if !f.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err("Rust input changed file type".into());
    }
    let mut bytes = Vec::new();
    f.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err(format!(
            "`{}` exceeds its {limit}-byte limit",
            path.display()
        ));
    }
    Ok(bytes)
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
fn config(path: &Path) -> Result<(Config, Vec<u8>, PathBuf), String> {
    let bytes = read(path, 1 << 20)?;
    let c: Config =
        serde_json::from_slice(&bytes).map_err(|e| format!("Rust import config: {e}"))?;
    // Configuration version is independent of the typed artifact schema.
    if !matches!(
        (c.schema, c.backend.as_deref()),
        (3 | 4, None | Some("charon") | Some("charon-trial"))
    ) || c.language != "rust"
        || c.target != TARGET
    {
        return Err("unsupported Rust import schema/language/target; use schema 3 and native Charon .ullbc artifacts (legacy extraction is retired)".into());
    }
    let absolute = fs::canonicalize(path).map_err(|e| e.to_string())?;
    let root = absolute
        .parent()
        .ok_or("Rust config needs a directory")?
        .to_path_buf();
    match (c.schema, &c.crate_config) {
        (3, None) => {
            local_file(&root, &c.source)?;
        }
        (4, Some(config)) => {
            config.validate(&c.source)?;
            for name in &config.files {
                super::crate_inputs::file(&root, name)?;
                if name == &c.artifact
                    || name == absolute.file_name().unwrap().to_string_lossy().as_ref()
                    || name == &format!("{}.lock", absolute.file_name().unwrap().to_string_lossy())
                {
                    return Err(
                        "Rust crate inputs must differ from config/artifact/lock outputs".into(),
                    );
                }
            }
        }
        _ => {
            return Err(
                "Rust schema 4 requires a crate configuration; schema 3 is single-file".into(),
            );
        }
    }
    local_file(&root, &c.artifact)?;
    if !c.source.ends_with(".rs")
        || c.source == c.artifact
        || c.artifact == absolute.file_name().unwrap().to_string_lossy()
        || c.artifact == format!("{}.lock", absolute.file_name().unwrap().to_string_lossy())
    {
        return Err("Rust artifact output must differ from source/config/lock".into());
    }
    Ok((c, bytes, root))
}
fn lock_path(path: &Path) -> Result<PathBuf, String> {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or("invalid Rust config name")?;
    Ok(path.with_file_name(format!("{name}.lock")))
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
        return digest(&files[&c.source]);
    }
    let hashes: Vec<_> = files
        .iter()
        .map(|(name, bytes)| (name, digest(bytes)))
        .collect();
    digest(
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
fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(m) if !m.file_type().is_file() => {
            return Err("Rust output must be a regular file".into());
        }
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => return Err(e.to_string()),
        _ => {}
    }
    crate::cli::write_file_atomically(path, bytes)
}
pub fn refresh_import(path: &Path) -> Result<(), String> {
    let (c, bytes, root) = config(path)?;
    let source = if c.crate_config.is_some() {
        super::crate_inputs::file(&root, &c.source)?
    } else {
        local_file(&root, &c.source)?
    };
    let legacy = (!c.exporter.is_empty()).then(|| root.join(&c.exporter));
    let runtime = super::runtime::resolve(legacy.as_deref())?;
    let exporter = &runtime.executable;
    let artifact_path = local_file(&root, &c.artifact)?;
    let lock_name = lock_path(path)?;
    let lock_output = root.join(lock_name.file_name().ok_or("invalid Rust lock filename")?);
    if exporter == &artifact_path
        || exporter == &lock_output
        || exporter == &source
        || exporter == &fs::canonicalize(path).map_err(|e| e.to_string())?
    {
        return Err("Rust exporter must differ from source/config/artifact/lock".into());
    }
    let inputs = Inputs {
        config: &c,
        config_digest: digest(&bytes),
        root: &root,
        source: &source,
        outputs: [artifact_path.clone(), lock_output],
    };
    let (lock, output_bytes) = extract(&inputs, &runtime, &|| Ok(digest(&read(path, 1 << 20)?)))?;
    write_atomic(&artifact_path, &output_bytes)?;
    write_atomic(
        &lock_path(path)?,
        &serde_json::to_vec_pretty(&lock).map_err(|e| e.to_string())?,
    )
}

/// A Rust import's inputs, from a per-sidecar config or a project unit.
struct Inputs<'a> {
    config: &'a Config,
    /// The digest of the configuration the lock records.
    config_digest: String,
    /// The directory crate files are relative to.
    root: &'a Path,
    source: &'a Path,
    /// The artifact and lock outputs, which the exporter must not be.
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
    let exporter_bytes = read(exporter, 128 << 20)?;
    let driver = &runtime.driver;
    if inputs.outputs.contains(driver) {
        return Err("Charon driver must differ from artifact/lock outputs".into());
    }
    let driver_bytes = read(driver, 128 << 20)?;
    let driver_hash = digest(&driver_bytes);
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
    let exporter_hash = digest(&exporter_bytes);
    let artifact_hash = digest(&output_bytes);
    let lock = Lock {
        schema: SCHEMA,
        identity: import_identity(
            &config_hash,
            &source_hash,
            &exporter_hash,
            &artifact_hash,
            &driver_hash,
        ),
        charon_driver: Some(driver_hash),
        config: config_hash,
        source: source_hash,
        exporter: exporter_hash,
        artifact: artifact_hash,
        source_files: Default::default(),
    };
    Ok((lock, output_bytes))
}

pub fn load_import(path: &Path) -> Result<PreparedRustImport, String> {
    let (c, bytes, root) = config(path)?;
    let lock: Lock =
        serde_json::from_slice(&read(&lock_path(path)?, 1 << 20)?).map_err(|e| e.to_string())?;
    load_locked(
        &c,
        &digest(&bytes),
        &root,
        &local_file(&root, &c.artifact)?,
        lock,
    )
}

fn load_locked(
    c: &Config,
    config_digest: &str,
    root: &Path,
    artifact_path: &Path,
    lock: Lock,
) -> Result<PreparedRustImport, String> {
    let artifact = read(artifact_path, 4 << 20)?;
    let source_files = sources(c, root)?;
    if lock.source != source_digest(c, &source_files)
        && let Some(name) = lock.source_files.iter().find_map(|(name, expected)| {
            (source_files.get(name).map(|bytes| digest(bytes)).as_ref() != Some(expected))
                .then_some(name)
        })
    {
        return Err(format!(
            "Rust crate file `{}` differs from its import lock; run `click import lock`",
            root.join(name).display()
        ));
    }
    if lock.schema != SCHEMA
        || lock.config != config_digest
        || lock.source != source_digest(c, &source_files)
        || lock.artifact != digest(&artifact)
        || lock.charon_driver.is_none()
        || lock.identity
            != import_identity(
                &lock.config,
                &lock.source,
                &lock.exporter,
                &lock.artifact,
                lock.charon_driver.as_deref().unwrap_or_default(),
            )
    {
        return Err("Rust import lock differs from its inputs; refresh it".into());
    }
    let export = decode(&artifact, c, &source_files)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            function_index: index_functions(&export),
            export,
            identity: lock.identity,
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
    pub crate_config: super::crate_inputs::CrateConfig,
    /// The artifact's absolute path.
    pub artifact: PathBuf,
    pub lock_path: PathBuf,
}

impl UnitConfig {
    fn config(&self) -> Result<(Config, PathBuf), String> {
        if !self.source.ends_with(".rs") {
            return Err("a Rust unit source must be a `.rs` crate root".into());
        }
        self.crate_config.validate(&self.source)?;
        let root = fs::canonicalize(&self.root)
            .map_err(|error| format!("resolve the root of unit `{}`: {error}", self.unit_name))?;
        for name in &self.crate_config.files {
            super::crate_inputs::file(&root, name)?;
        }
        let config = Config {
            schema: 4,
            language: "rust".into(),
            target: TARGET.into(),
            source: self.source.clone(),
            exporter: String::new(),
            artifact: String::new(),
            backend: None,
            crate_config: Some(self.crate_config.clone()),
        };
        Ok((config, root))
    }
}

/// Extracts a project unit with the selected pinned Rust frontend: its lock entry and
/// the artifact to write.
pub(crate) fn prepare_unit(
    unit: &UnitConfig,
) -> Result<(serde_json::Value, Vec<(PathBuf, Vec<u8>)>), String> {
    let (config, root) = unit.config()?;
    let source = super::crate_inputs::file(&root, &unit.source)?;
    let runtime = super::runtime::resolve(None)?;
    let exporter = &runtime.executable;
    if exporter == &source || exporter == &unit.artifact || exporter == &unit.lock_path {
        return Err("Rust exporter must differ from source/artifact/lock".into());
    }
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
        .map(|(name, bytes)| (name.clone(), digest(bytes)))
        .collect();
    let value = serde_json::to_value(&lock).map_err(|e| e.to_string())?;
    Ok((value, vec![(unit.artifact.clone(), artifact)]))
}

/// Loads a project unit from its lock entry.
pub(crate) fn load_unit(
    unit: &UnitConfig,
    lock: &serde_json::Value,
) -> Result<PreparedRustImport, String> {
    let (config, root) = unit.config()?;
    let lock = Lock::deserialize(lock).map_err(|e| format!("parse Rust import lock: {e}"))?;
    if lock.config != unit.unit_digest {
        return Err(format!(
            "the project lock for unit `{}` does not match its description in `click.project.json`; run `click import lock` to prepare it again",
            unit.unit_name
        ));
    }
    load_locked(&config, &unit.unit_digest, &root, &unit.artifact, lock)
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

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
        let artifact = fs::read(trial.join("restoration.ullbc")).unwrap();
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
                    "roots": ["adler2::Adler32::from_checksum"],
                    "files": ["src/lib.rs", "src/algo.rs"]},
                "sources": {"src/lib.rs": {}}
            }}})
            .to_string(),
        )
        .unwrap();
        let project = crate::project::Project::load(&project_file).unwrap();
        let unit = project.rust_unit("adler2").unwrap();
        let (config, unit_root) = unit.config().unwrap();
        let files = sources(&config, &unit_root).unwrap();
        let source = source_digest(&config, &files);
        let (exporter, driver, artifact_hash) =
            (digest(b"charon"), digest(b"driver"), digest(&artifact));
        let lock = Lock {
            schema: SCHEMA,
            identity: import_identity(
                &unit.unit_digest,
                &source,
                &exporter,
                &artifact_hash,
                &driver,
            ),
            config: unit.unit_digest.clone(),
            source,
            exporter,
            artifact: artifact_hash,
            charon_driver: Some(driver),
            source_files: files
                .iter()
                .map(|(name, bytes)| (name.clone(), digest(bytes)))
                .collect(),
        };
        fs::write(
            proofs.join(crate::project::LOCK_NAME),
            serde_json::json!({"schema": 1, "units": {"adler2": {"language": "rust", "lock": lock}}})
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
