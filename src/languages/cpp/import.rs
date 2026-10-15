//! Locked semantic imports produced by the pinned C++ frontend.
//!
//! `refresh_import` is the only operation in this module that executes the
//! Clang-based exporter. `load_import` validates the source, lock, and stored
//! semantic artifact without consulting or executing the exporter.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::schema::{
    CppExceptionBehavior, CppExport, CppLibraryAssertion, CppPreprocessorFile, CppProfile,
    CppStatement, EXPORT_SCHEMA, LANGUAGE, MAX_PREPROCESSOR_FILES, STANDARD, TARGET,
};
use crate::cli::write_file_atomically;
use crate::languages::compiler_process::{CompilerLimits, run_compiler};

const CONFIG_SCHEMA: u32 = 6;
const MAX_CONFIG_BYTES: usize = 1 << 20;
const MAX_COMPILATION_DATABASE_BYTES: usize = 16 << 20;
const MAX_SOURCE_BYTES: usize = 1 << 20;
const MAX_DEPENDENCIES: usize = 64;
const MAX_PREPROCESSOR_FILE_BYTES: usize = 4 << 20;
const MAX_PREPROCESSOR_TOTAL_BYTES: usize = 128 << 20;
const MAX_EXPORTER_BYTES: usize = 64 << 20;
const MAX_ARTIFACT_BYTES: usize = 8 << 20;
const MAX_DIAGNOSTIC_BYTES: usize = 64 << 10;

#[derive(Clone, Debug)]
pub struct PreparedCppImport {
    inner: Arc<PreparedInner>,
}

#[derive(Debug)]
struct PreparedInner {
    logical_source: String,
    identity: String,
    export: CppExport,
    execution: crate::languages::ExecutionCache,
}

impl PreparedCppImport {
    pub fn logical_source(&self) -> &str {
        &self.inner.logical_source
    }

    pub fn identity(&self) -> &str {
        &self.inner.identity
    }

    /// This import under the name a sidecar's `verifying` declaration gives
    /// its logical source; a project unit names it by its path in the unit.
    pub(crate) fn named(&self, logical_source: &str) -> Self {
        if self.logical_source() == logical_source {
            return self.clone();
        }
        Self {
            inner: Arc::new(PreparedInner {
                logical_source: logical_source.to_string(),
                identity: self.inner.identity.clone(),
                export: self.inner.export.clone(),
                execution: Default::default(),
            }),
        }
    }

    pub fn export(&self) -> &CppExport {
        &self.inner.export
    }

    pub(crate) fn prepared_execution(
        &self,
    ) -> Result<Arc<crate::languages::PreparedExecution>, String> {
        self.inner
            .execution
            .get_or_lower(|| Ok(super::lower_import(self)?.prepared_execution()))
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    language: String,
    standard: String,
    target: String,
    exceptions: bool,
    #[serde(default)]
    exception_behavior: CppExceptionBehavior,
    rtti: bool,
    exporter: String,
    compilation_database: String,
    working_directory: String,
    source: String,
    logical_source: String,
    dependencies: Vec<String>,
    function: String,
    #[serde(default)]
    library_assertions: Vec<CppLibraryAssertion>,
    artifact: String,
    #[serde(skip)]
    directory: PathBuf,
    /// Every selected function: `function` for a per-sidecar config, or a
    /// project unit source's `functions`.
    #[serde(skip)]
    functions: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config_sha256: String,
    exporter_sha256: String,
    compilation_database_sha256: String,
    source_sha256: String,
    logical_source_sha256: String,
    dependencies: BTreeMap<String, String>,
    preprocessor_files: BTreeMap<String, LockedPreprocessorFile>,
    artifact_sha256: String,
    artifact_bytes: usize,
    profile: CppProfile,
    identity: String,
    /// A project unit's roots at preparation, absolute: the unit root, then
    /// the project root. Preprocessor inputs under them are rechecked
    /// relative to the roots' current locations; inputs outside them are
    /// pinned by their recorded digest.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    prepared_roots: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct LockedPreprocessorFile {
    canonical_path: String,
    sha256: String,
}

pub fn refresh_import(config_path: &Path) -> Result<(), String> {
    refresh_import_inner(config_path).map_err(bounded_error)
}

fn refresh_import_inner(config_path: &Path) -> Result<(), String> {
    let (config, config_bytes) = read_config(config_path)?;
    let exporter = resolve_input(&config.directory, &config.exporter, "C++ exporter")?;
    let compilation_database = resolve_input(
        &config.directory,
        &config.compilation_database,
        "C++ compilation database",
    )?;
    let working_directory = resolve_input(
        &config.directory,
        &config.working_directory,
        "C++ working directory",
    )?;
    let outputs = [artifact_path(&config)?, lock_path(config_path)?];
    let (lock, artifact) = export(
        &config,
        hex_digest(&config_bytes),
        &ExportInputs {
            config_path: Some(&absolute_path(config_path)?),
            exporter: &exporter,
            compilation_database: &compilation_database,
            working_directory: &working_directory,
            outputs: &outputs,
        },
    )?;
    let mut lock_bytes =
        serde_json::to_vec_pretty(&lock).map_err(|error| format!("encode C++ lock: {error}"))?;
    lock_bytes.push(b'\n');
    if lock_bytes.len() > MAX_CONFIG_BYTES {
        return Err("C++ import lock exceeds its size limit".into());
    }
    write_file_atomically(&outputs[0], &artifact)?;
    write_file_atomically(&outputs[1], &lock_bytes)
}

/// The resolved inputs and outputs of one export.
struct ExportInputs<'a> {
    config_path: Option<&'a Path>,
    exporter: &'a Path,
    compilation_database: &'a Path,
    working_directory: &'a Path,
    /// The artifact and lock outputs, which no input may be.
    outputs: &'a [PathBuf; 2],
}

/// Runs the exporter twice on `config` and returns the lock and the
/// artifact, without writing either.
fn export(
    config: &Config,
    config_sha256: String,
    inputs: &ExportInputs<'_>,
) -> Result<(Lock, Vec<u8>), String> {
    let ExportInputs {
        exporter,
        compilation_database,
        working_directory,
        ..
    } = *inputs;
    if !working_directory.is_dir() {
        return Err(format!(
            "C++ working directory `{}` is not a directory",
            working_directory.display()
        ));
    }
    let source = resolve_source(config, working_directory)?;
    let logical_source = resolve_logical_source(config, working_directory)?;
    let dependencies = resolve_dependencies(config, working_directory)?;
    reject_output_collisions(inputs, &source, &logical_source, &dependencies)?;

    let exporter_bytes = read_stable(exporter, MAX_EXPORTER_BYTES, "C++ exporter")?;
    let compilation_database_before = read_stable(
        compilation_database,
        MAX_COMPILATION_DATABASE_BYTES,
        "C++ compilation database",
    )?;
    let source_before = read_stable(&source, MAX_SOURCE_BYTES, "C++ source")?;
    let logical_source_before =
        read_stable(&logical_source, MAX_SOURCE_BYTES, "C++ logical source")?;
    let dependency_bytes_before = read_dependencies(&dependencies)?;
    validate_library_pins(config, &dependency_bytes_before)?;
    let mut arguments = vec![
        "--logical-source".into(),
        config.logical_source.clone(),
        "--logical-source-path".into(),
        logical_source.to_string_lossy().into_owned(),
    ];
    for function in &config.functions {
        arguments.extend(["--function".into(), function.clone()]);
    }
    arguments.extend([
        "--source".into(),
        source.to_string_lossy().into_owned(),
        "--dependency-root".into(),
        working_directory.to_string_lossy().into_owned(),
        "--compilation-database".into(),
        compilation_database.to_string_lossy().into_owned(),
        "--exception-behavior".into(),
        config.exception_behavior.as_str().into(),
        "--library-assertions".into(),
        serde_json::to_string(&config.library_assertions)
            .map_err(|error| format!("encode C++ library contracts: {error}"))?,
    ]);
    let check_inputs = || -> Result<(), String> {
        if read_stable(&source, MAX_SOURCE_BYTES, "C++ source")? != source_before {
            return Err("C++ source changed during semantic export".into());
        }
        if read_stable(&logical_source, MAX_SOURCE_BYTES, "C++ logical source")?
            != logical_source_before
        {
            return Err("C++ logical source changed during semantic export".into());
        }
        if read_dependencies(&dependencies)? != dependency_bytes_before {
            return Err("C++ dependency changed during semantic export".into());
        }
        if read_stable(exporter, MAX_EXPORTER_BYTES, "C++ exporter")? != exporter_bytes {
            return Err("C++ exporter changed during semantic export".into());
        }
        if read_stable(
            compilation_database,
            MAX_COMPILATION_DATABASE_BYTES,
            "C++ compilation database",
        )? != compilation_database_before
        {
            return Err("C++ compilation database changed during semantic export".into());
        }
        Ok(())
    };
    let artifact = run_cpp_exporter(
        exporter,
        &arguments,
        working_directory,
        &config.logical_source,
    )?;
    check_inputs()?;
    let export = decode_artifact(&artifact, config, &dependencies)?;
    let preprocessor_files_before = read_preprocessor_files(&export.preprocessor_files)?;
    validate_library_headers(config, &dependencies, &preprocessor_files_before)?;
    let repeated = run_cpp_exporter(
        exporter,
        &arguments,
        working_directory,
        &config.logical_source,
    )?;
    check_inputs()?;
    if repeated != artifact {
        return Err("C++ semantic export changed while locking preprocessor inputs".into());
    }
    let preprocessor_files_after = read_preprocessor_files(&export.preprocessor_files)?;
    if preprocessor_files_before != preprocessor_files_after {
        return Err("C++ preprocessor input changed during semantic export".into());
    }
    let exporter_sha256 = hex_digest(&exporter_bytes);
    let compilation_database_sha256 = hex_digest(&compilation_database_before);
    let source_sha256 = hex_digest(&source_before);
    let logical_source_sha256 = hex_digest(&logical_source_before);
    let dependency_digests = dependency_bytes_before
        .iter()
        .map(|(path, bytes)| (path.clone(), hex_digest(bytes)))
        .collect::<BTreeMap<_, _>>();
    let artifact_sha256 = hex_digest(&artifact);
    let identity = semantic_identity(
        &config_sha256,
        &compilation_database_sha256,
        &source_sha256,
        &logical_source_sha256,
        &dependency_digests,
        &preprocessor_files_after,
        &exporter_sha256,
        &artifact_sha256,
        &export.profile,
    );
    let lock = Lock {
        schema: CONFIG_SCHEMA,
        config_sha256,
        exporter_sha256,
        compilation_database_sha256,
        source_sha256,
        logical_source_sha256,
        dependencies: dependency_digests,
        preprocessor_files: preprocessor_files_after,
        artifact_sha256,
        artifact_bytes: artifact.len(),
        profile: export.profile,
        identity,
        prepared_roots: Vec::new(),
    };
    Ok((lock, artifact))
}

fn run_cpp_exporter(
    exporter: &Path,
    arguments: &[String],
    working_directory: &Path,
    logical_source: &str,
) -> Result<Vec<u8>, String> {
    let output = run_compiler(
        exporter,
        arguments,
        working_directory,
        &BTreeMap::new(),
        CompilerLimits {
            timeout: Duration::from_secs(10),
            max_stdout_bytes: MAX_ARTIFACT_BYTES,
            max_stderr_bytes: MAX_DIAGNOSTIC_BYTES,
        },
    )
    .map_err(|error| format!("export C++ source `{logical_source}`: {error}"))?;
    if !output.stderr.is_empty() {
        return Err(format!(
            "C++ exporter emitted diagnostics: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output.stdout)
}

pub fn load_import(config_path: &Path) -> Result<PreparedCppImport, String> {
    load_import_inner(config_path).map_err(bounded_error)
}

fn load_import_inner(config_path: &Path) -> Result<PreparedCppImport, String> {
    let (config, config_bytes) = read_config(config_path)?;
    let lock_bytes = read_stable(
        &lock_path(config_path)?,
        MAX_CONFIG_BYTES,
        "C++ import lock",
    )?;
    let lock: Lock = serde_json::from_slice(&lock_bytes)
        .map_err(|error| format!("parse C++ import lock: {error}"))?;
    if lock.config_sha256 != hex_digest(&config_bytes) {
        return Err("C++ import lock does not match the import config; refresh it".into());
    }
    let compilation_database = resolve_input(
        &config.directory,
        &config.compilation_database,
        "C++ compilation database",
    )?;
    let compilation_database_bytes = read_stable(
        &compilation_database,
        MAX_COMPILATION_DATABASE_BYTES,
        "C++ compilation database",
    )?;
    if lock.compilation_database_sha256 != hex_digest(&compilation_database_bytes) {
        return Err("C++ compilation database differs from the import lock; refresh it".into());
    }
    let working_directory = resolve_input(
        &config.directory,
        &config.working_directory,
        "C++ working directory",
    )?;
    load_locked(
        &config,
        lock,
        &working_directory,
        &artifact_path(&config)?,
        &[],
    )
}

/// Checks a lock against `config`'s current inputs and loads its artifact.
/// `current_roots` are the current locations of a project unit's
/// `prepared_roots`; without them, every preprocessor input is re-read at its
/// recorded path.
fn load_locked(
    config: &Config,
    lock: Lock,
    working_directory: &Path,
    artifact_path: &Path,
    current_roots: &[PathBuf],
) -> Result<PreparedCppImport, String> {
    if lock.schema != CONFIG_SCHEMA {
        return Err(format!(
            "unsupported C++ import lock schema {}; expected {CONFIG_SCHEMA}",
            lock.schema
        ));
    }
    if lock.prepared_roots.len() != current_roots.len() {
        return Err("C++ import lock roots do not match its configuration".into());
    }
    let source = resolve_source(config, working_directory)?;
    let source_bytes = read_stable(&source, MAX_SOURCE_BYTES, "C++ source")?;
    if lock.source_sha256 != hex_digest(&source_bytes) {
        return Err(format!(
            "C++ source differs from the import lock: `{}`; refresh it",
            source.display()
        ));
    }
    let logical_source = resolve_logical_source(config, working_directory)?;
    let logical_source_bytes =
        read_stable(&logical_source, MAX_SOURCE_BYTES, "C++ logical source")?;
    if lock.logical_source_sha256 != hex_digest(&logical_source_bytes) {
        return Err(format!(
            "C++ logical source differs from the import lock: `{}`; refresh it",
            logical_source.display()
        ));
    }
    let dependencies = resolve_dependencies(config, working_directory)?;
    let dependency_bytes = read_dependencies(&dependencies)?;
    validate_library_pins(config, &dependency_bytes)?;
    let dependency_digests = dependency_bytes
        .into_iter()
        .map(|(path, bytes)| (path, hex_digest(&bytes)))
        .collect::<BTreeMap<_, _>>();
    if lock.dependencies != dependency_digests {
        return Err("C++ dependency inventory differs from the import lock; refresh it".into());
    }
    let artifact = read_stable(artifact_path, MAX_ARTIFACT_BYTES, "C++ semantic artifact")?;
    if lock.artifact_bytes != artifact.len() || lock.artifact_sha256 != hex_digest(&artifact) {
        return Err("C++ semantic artifact differs from the import lock; refresh it".into());
    }
    let export = decode_artifact(&artifact, config, &dependencies)?;
    if lock.profile != export.profile {
        return Err("C++ semantic artifact profile differs from the import lock".into());
    }
    let preprocessor_files = if current_roots.is_empty() {
        let files = read_preprocessor_files(&export.preprocessor_files)?;
        if lock.preprocessor_files != files {
            return Err(
                "C++ preprocessor input inventory differs from the import lock; refresh it".into(),
            );
        }
        files
    } else {
        let roots = lock
            .prepared_roots
            .iter()
            .map(PathBuf::from)
            .zip(current_roots.iter().cloned())
            .collect::<Vec<_>>();
        check_rooted_preprocessor_files(
            &export.preprocessor_files,
            &lock.preprocessor_files,
            &roots,
        )?
    };
    validate_library_headers(config, &dependencies, &preprocessor_files)?;
    let identity = semantic_identity(
        &lock.config_sha256,
        &lock.compilation_database_sha256,
        &lock.source_sha256,
        &lock.logical_source_sha256,
        &lock.dependencies,
        &lock.preprocessor_files,
        &lock.exporter_sha256,
        &lock.artifact_sha256,
        &lock.profile,
    );
    if lock.identity != identity {
        return Err("C++ import identity does not match its locked inputs".into());
    }

    Ok(PreparedCppImport {
        inner: Arc::new(PreparedInner {
            logical_source: config.logical_source.clone(),
            identity,
            export,
            execution: Default::default(),
        }),
    })
}

/// Checks a project unit's preprocessor inputs: each one under a prepared
/// root is re-read at the root's current location and must match the lock;
/// each one outside every root is pinned by its recorded digest. Returns the
/// inventory with rooted paths at their current locations.
fn check_rooted_preprocessor_files(
    files: &[CppPreprocessorFile],
    locked: &BTreeMap<String, LockedPreprocessorFile>,
    roots: &[(PathBuf, PathBuf)],
) -> Result<BTreeMap<String, LockedPreprocessorFile>, String> {
    super::budget::limit("preprocessor files", files.len(), MAX_PREPROCESSOR_FILES)?;
    if files.len() != locked.len() {
        return Err(
            "C++ preprocessor input inventory differs from the import lock; refresh it".into(),
        );
    }
    let mut total_bytes = 0usize;
    let mut current = BTreeMap::new();
    for file in files {
        let entry = locked
            .get(&file.accessed_path)
            .filter(|entry| entry.canonical_path == file.canonical_path)
            .ok_or("C++ preprocessor input inventory differs from the import lock; refresh it")?;
        let canonical = Path::new(&file.canonical_path);
        let Some(path) = roots.iter().find_map(|(prepared, now)| {
            canonical
                .strip_prefix(prepared)
                .ok()
                .map(|relative| now.join(relative))
        }) else {
            current.insert(file.accessed_path.clone(), entry.clone());
            continue;
        };
        let bytes = read_stable(&path, MAX_PREPROCESSOR_FILE_BYTES, "C++ preprocessor input")?;
        total_bytes = total_bytes
            .checked_add(bytes.len())
            .ok_or("C++ artifact budget exhausted: preprocessor bytes (counter overflow)")?;
        super::budget::limit(
            "preprocessor bytes",
            total_bytes,
            MAX_PREPROCESSOR_TOTAL_BYTES,
        )?;
        if hex_digest(&bytes) != entry.sha256 {
            return Err(format!(
                "C++ input `{}` differs from its import lock; run `click import lock`",
                path.display()
            ));
        }
        current.insert(
            file.accessed_path.clone(),
            LockedPreprocessorFile {
                canonical_path: path.to_string_lossy().into_owned(),
                sha256: entry.sha256.clone(),
            },
        );
    }
    Ok(current)
}

fn decode_artifact(
    bytes: &[u8],
    config: &Config,
    dependencies: &[(String, PathBuf)],
) -> Result<CppExport, String> {
    super::budget::check_serialized(bytes)?;
    let export: CppExport = serde_json::from_slice(bytes)
        .map_err(|error| format!("parse C++ semantic artifact: {error}"))?;
    export.validate(
        &config.logical_source,
        &config.functions,
        config.exceptions,
        config.exception_behavior,
        config.rtti,
        &config.dependencies,
    )?;
    validate_standard_byte_declarations(&export, config, dependencies)?;
    // One explicit statement walk; contract lookup never scans the inventory per site.
    let contracts: BTreeMap<_, _> = config
        .library_assertions
        .iter()
        .map(|contract| (contract.function.as_str(), contract))
        .collect();
    let metadata_files: std::collections::BTreeSet<_> = export
        .preprocessor_files
        .iter()
        .map(|file| file.canonical_path.as_str())
        .collect();
    let dependency_files: BTreeMap<_, _> = dependencies
        .iter()
        .map(|(header, path)| (header.as_str(), path.to_string_lossy()))
        .collect();
    let mut pending = export
        .functions
        .iter()
        .map(|function| function.body.as_slice())
        .collect::<Vec<_>>();
    pending.extend(
        export
            .reachable_functions
            .iter()
            .map(|function| function.body.as_slice()),
    );
    while let Some(statements) = pending.pop() {
        for statement in statements {
            crate::instrumentation::record_deterministic_work(1);
            match statement {
                CppStatement::LibraryAssert {
                    contract, metadata, ..
                } => {
                    if contracts.get(contract.function.as_str()).copied() != Some(contract) {
                        return Err("C++ artifact library assertion differs from its configured assumed contract".into());
                    }
                    for argument in metadata {
                        if let super::schema::CppLibraryMetadata::Literal(literal) = argument
                            && dependency_files
                                .get(literal.constructor.header.as_str())
                                .map(|path| path.as_ref())
                                != Some(literal.declaration_file.as_str())
                        {
                            return Err("C++ literal metadata declaration differs from its pinned constructor header".into());
                        }
                        if !metadata_files.contains(argument.declaration_file()) {
                            return Err("C++ library metadata declaration must belong to the locked preprocessor closure".into());
                        }
                    }
                }
                CppStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                CppStatement::Scope { body, .. } => pending.push(body),
                CppStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    pending.push(try_body);
                    pending.push(handler);
                }
                _ => {}
            }
        }
    }
    Ok(export)
}

/// Byte access is a language privilege of the actual pinned declaration, not
/// of an arbitrary enum with the same integer representation. This borrowed
/// metadata walk covers types in nested calls, conversions and expressions.
fn validate_standard_byte_declarations(
    export: &CppExport,
    config: &Config,
    dependencies: &[(String, PathBuf)],
) -> Result<(), String> {
    use super::schema::CppType;
    use std::cell::RefCell;
    let paths: BTreeMap<_, _> = dependencies
        .iter()
        .map(|(name, path)| (name.as_str(), path))
        .collect();
    let preprocessor_paths: std::collections::BTreeSet<_> = export
        .preprocessor_files
        .iter()
        .map(|file| file.canonical_path.as_str())
        .collect();
    let checked = RefCell::new(std::collections::BTreeSet::new());
    let check_type = |ty: &CppType| -> Result<(), String> {
        fn check(
            ty: &CppType,
            paths: &BTreeMap<&str, &PathBuf>,
            checked: &RefCell<std::collections::BTreeSet<String>>,
            preprocessor_paths: &std::collections::BTreeSet<&str>,
        ) -> Result<(), String> {
            crate::instrumentation::record_deterministic_work(1);
            match ty {
                CppType::Pointer { pointee } | CppType::LvalueReference { pointee } => {
                    check(pointee, paths, checked, preprocessor_paths)
                }
                CppType::Enumeration { span, .. } if super::scalar::is_standard_byte(ty) => {
                    if (
                        span.start_line,
                        span.start_column,
                        span.end_line,
                        span.end_column,
                    ) != (69, 3, 69, 37)
                    {
                        return Err(
                            "std::byte requires the pinned standard declaration span".into()
                        );
                    }
                    if checked.borrow().contains(&span.file) {
                        return Ok(());
                    }
                    let path = paths
                        .get(span.file.as_str())
                        .ok_or("std::byte requires a locked standard header dependency")?;
                    if !path
                        .to_str()
                        .is_some_and(|path| preprocessor_paths.contains(path))
                    {
                        return Err("std::byte declaration header must belong to the locked preprocessor closure".into());
                    }
                    let bytes = read_stable(path, MAX_SOURCE_BYTES, "std::byte header")?;
                    if hex_digest(&bytes)
                        != "51409c852efecb6e4de3ef7c31e51e63ddd4ec376ee00e3c68e85e6579fa8648"
                    {
                        return Err(
                            "std::byte declaration header differs from the supported libstdc++ pin"
                                .into(),
                        );
                    }
                    checked.borrow_mut().insert(span.file.clone());
                    Ok(())
                }
                _ => Ok(()),
            }
        }
        check(ty, &paths, &checked, &preprocessor_paths)
    };
    let sources = std::collections::BTreeSet::from_iter(
        std::iter::once(config.logical_source.clone()).chain(config.dependencies.iter().cloned()),
    );
    for function in export.functions.iter().chain(&export.reachable_functions) {
        // An axiom has an interface and no source of its own: its types are
        // checked, and its synthetic spans name no file to check.
        if function.axiom.is_some() {
            for parameter in &function.parameters {
                check_type(&parameter.value_type)?;
            }
            check_type(&function.return_type)?;
            continue;
        }
        super::validity::check_function_with_types(
            function,
            &function.span.file,
            &sources,
            &check_type,
        )?;
    }
    for record in &export.records {
        for argument in &record.byte_template_arguments {
            check_type(&argument.value_type)?;
        }
        for field in &record.fields {
            check_type(&field.value_type)?;
        }
    }
    for constant in &export.constants {
        check_type(&constant.value_type)?;
    }
    Ok(())
}

fn validate_library_pins(
    config: &Config,
    dependencies: &BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    let mut digests = BTreeMap::new();
    for (function, header, sha256) in config
        .library_assertions
        .iter()
        .flat_map(CppLibraryAssertion::pins)
    {
        let bytes = dependencies
            .get(header)
            .ok_or("C++ assumed library assertion header is missing from dependencies")?;
        let digest = digests.entry(header).or_insert_with(|| hex_digest(bytes));
        if digest.as_str() != sha256 {
            return Err(format!(
                "C++ assumed library contract `{}` header hash differs from its explicit pin",
                function
            ));
        }
    }
    Ok(())
}

fn validate_library_headers(
    config: &Config,
    dependencies: &[(String, PathBuf)],
    files: &BTreeMap<String, LockedPreprocessorFile>,
) -> Result<(), String> {
    if config.library_assertions.is_empty() {
        return Ok(());
    }
    let dependencies: BTreeMap<_, _> = dependencies
        .iter()
        .map(|(name, path)| (name.as_str(), path))
        .collect();
    let observed: BTreeMap<_, _> = files
        .values()
        .map(|file| (file.canonical_path.as_str(), file.sha256.as_str()))
        .collect();
    for (_, header, sha256) in config
        .library_assertions
        .iter()
        .flat_map(CppLibraryAssertion::pins)
    {
        let path = dependencies[header].to_string_lossy();
        if observed.get(path.as_ref()).copied() != Some(sha256) {
            return Err(
                "C++ assumed library contract header must be in the locked preprocessor closure"
                    .into(),
            );
        }
    }
    Ok(())
}

fn semantic_identity(
    config_sha256: &str,
    compilation_database_sha256: &str,
    source_sha256: &str,
    logical_source_sha256: &str,
    dependencies: &BTreeMap<String, String>,
    preprocessor_files: &BTreeMap<String, LockedPreprocessorFile>,
    exporter_sha256: &str,
    artifact_sha256: &str,
    profile: &CppProfile,
) -> String {
    let encoded = serde_json::to_vec(&(
        CONFIG_SCHEMA,
        EXPORT_SCHEMA,
        "click-cpp-semantic-import-v6",
        config_sha256,
        compilation_database_sha256,
        source_sha256,
        logical_source_sha256,
        dependencies,
        preprocessor_files,
        exporter_sha256,
        artifact_sha256,
        profile,
    ))
    .expect("C++ semantic identity serializes");
    hex_digest(&encoded)
}

fn read_config(path: &Path) -> Result<(Config, Vec<u8>), String> {
    let absolute = absolute_path(path)?;
    let bytes = read_stable(&absolute, MAX_CONFIG_BYTES, "C++ import config")?;
    let mut config: Config = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse C++ import config: {error}"))?;
    config.directory = absolute
        .parent()
        .ok_or("C++ import config has no parent directory")?
        .to_path_buf();
    config.functions = vec![config.function.clone()];
    validate_config(&config)?;
    Ok((config, bytes))
}

fn validate_config(config: &Config) -> Result<(), String> {
    if config.schema != CONFIG_SCHEMA
        || config.language != LANGUAGE
        || config.standard != STANDARD
        || config.target != TARGET
    {
        return Err(format!(
            "C++ import config must use schema {CONFIG_SCHEMA}, Clang {STANDARD} for {TARGET}"
        ));
    }
    if matches!(config.exception_behavior, CppExceptionBehavior::ScalarInt32) && !config.exceptions
    {
        return Err("scalar int32 exception import requires C++ exceptions enabled".into());
    }
    for (label, value) in [
        ("exporter", config.exporter.as_str()),
        ("compilation database", config.compilation_database.as_str()),
        ("working directory", config.working_directory.as_str()),
        ("source", config.source.as_str()),
        ("logical source", config.logical_source.as_str()),
        ("function", config.function.as_str()),
        ("artifact", config.artifact.as_str()),
    ] {
        if value.is_empty() || value.as_bytes().contains(&0) {
            return Err(format!("C++ import config has invalid {label}"));
        }
    }
    validate_relative_path(&config.source, "source")?;
    validate_relative_path(&config.compilation_database, "compilation database")?;
    validate_relative_path(&config.logical_source, "logical source")?;
    validate_relative_path(&config.artifact, "artifact")?;
    let mut previous_dependency: Option<&str> = None;
    for dependency in &config.dependencies {
        validate_relative_path(dependency, "dependency")?;
        if dependency.is_empty()
            || dependency.as_bytes().contains(&0)
            || previous_dependency.is_some_and(|previous| previous >= dependency.as_str())
        {
            return Err("C++ dependencies must be unique sorted relative paths".into());
        }
        previous_dependency = Some(dependency);
    }
    if config.library_assertions.len() > 64 {
        return Err("C++ assumed library assertion inventory exceeds its size limit".into());
    }
    let mut previous_contract: Option<&str> = None;
    for contract in &config.library_assertions {
        contract.validate()?;
        if previous_contract.is_some_and(|previous| previous >= contract.function.as_str()) {
            return Err(
                "C++ assumed library assertions must have unique sorted function names".into(),
            );
        }
        if contract.pins().any(|(_, header, _)| {
            config
                .dependencies
                .binary_search_by(|name| name.as_str().cmp(header))
                .is_err()
        }) {
            return Err(
                "C++ assumed library assertion header must be an explicit dependency".into(),
            );
        }
        previous_contract = Some(&contract.function);
    }
    if Path::new(&config.source)
        .extension()
        .and_then(|value| value.to_str())
        != Some("cpp")
    {
        return Err("the first C++ import slice requires a `.cpp` translation unit".into());
    }
    if !matches!(
        Path::new(&config.logical_source)
            .extension()
            .and_then(|value| value.to_str()),
        Some("cpp" | "h")
    ) {
        return Err("the first C++ import slice requires a `.cpp` or `.h` logical source".into());
    }
    if config.functions.is_empty() || config.functions.len() > 64 {
        return Err("a C++ import selects 1 to 64 functions".into());
    }
    for (index, function) in config.functions.iter().enumerate() {
        let mut components = function.rsplit("::");
        let member = components.next().unwrap_or_default();
        let valid_selector = (is_identifier(member)
            || matches!(member, "operator+=" | "operator-=" | "operator[]"))
            && components.all(is_identifier);
        if !valid_selector {
            return Err("C++ function selector requires a function name or Class::method (including operator+=, operator-= and operator[])".into());
        }
        if config.functions[..index].contains(function) {
            return Err(format!("C++ function `{function}` is selected twice"));
        }
    }
    if config.source == config.artifact || config.logical_source == config.artifact {
        return Err("C++ source and semantic artifact paths must differ".into());
    }
    Ok(())
}

pub(super) fn is_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
}

fn validate_relative_path(path: &str, label: &str) -> Result<(), String> {
    let path = Path::new(path);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        return Err(format!(
            "C++ {label} path must stay inside its configured root"
        ));
    }
    Ok(())
}

fn absolute_path(path: &Path) -> Result<PathBuf, String> {
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|error| format!("read current directory: {error}"))?
            .join(path)
    };
    joined
        .canonicalize()
        .map_err(|error| format!("resolve `{}`: {error}", joined.display()))
}

fn resolve_input(base: &Path, path: &str, label: &str) -> Result<PathBuf, String> {
    let path = Path::new(path);
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    };
    joined
        .canonicalize()
        .map_err(|error| format!("resolve {label} `{}`: {error}", joined.display()))
}

fn resolve_source(config: &Config, working_directory: &Path) -> Result<PathBuf, String> {
    resolve_input(working_directory, &config.source, "C++ source")
}

fn resolve_logical_source(config: &Config, working_directory: &Path) -> Result<PathBuf, String> {
    resolve_input(
        working_directory,
        &config.logical_source,
        "C++ logical source",
    )
}

fn resolve_dependencies(
    config: &Config,
    working_directory: &Path,
) -> Result<Vec<(String, PathBuf)>, String> {
    if config.dependencies.len() > MAX_DEPENDENCIES {
        return Err("C++ dependency inventory exceeds its bound".into());
    }
    config
        .dependencies
        .iter()
        .map(|dependency| {
            let path = resolve_input(working_directory, dependency, "C++ dependency")?;
            if !path.starts_with(working_directory) {
                return Err(format!(
                    "C++ dependency `{dependency}` escapes the configured working directory"
                ));
            }
            Ok((dependency.clone(), path))
        })
        .collect()
}

fn read_dependencies(
    dependencies: &[(String, PathBuf)],
) -> Result<BTreeMap<String, Vec<u8>>, String> {
    dependencies
        .iter()
        .map(|(name, path)| {
            read_stable(path, MAX_SOURCE_BYTES, "C++ dependency").map(|bytes| (name.clone(), bytes))
        })
        .collect()
}

fn read_preprocessor_files(
    files: &[CppPreprocessorFile],
) -> Result<BTreeMap<String, LockedPreprocessorFile>, String> {
    super::budget::limit("preprocessor files", files.len(), MAX_PREPROCESSOR_FILES)?;
    if files.is_empty() {
        return Err("C++ preprocessor file inventory must not be empty".into());
    }
    let mut total_bytes = 0usize;
    let mut result = BTreeMap::new();
    for file in files {
        let accessed = Path::new(&file.accessed_path);
        let canonical = accessed.canonicalize().map_err(|error| {
            format!(
                "resolve C++ preprocessor input `{}`: {error}",
                accessed.display()
            )
        })?;
        if canonical != Path::new(&file.canonical_path) {
            return Err(format!(
                "C++ preprocessor input `{}` changed its resolved target; refresh it",
                file.accessed_path
            ));
        }
        let bytes = read_stable(
            &canonical,
            MAX_PREPROCESSOR_FILE_BYTES,
            "C++ preprocessor input",
        )?;
        total_bytes = total_bytes
            .checked_add(bytes.len())
            .ok_or("C++ artifact budget exhausted: preprocessor bytes (counter overflow)")?;
        super::budget::limit(
            "preprocessor bytes",
            total_bytes,
            MAX_PREPROCESSOR_TOTAL_BYTES,
        )?;
        if accessed.canonicalize().ok().as_deref() != Some(canonical.as_path()) {
            return Err(format!(
                "C++ preprocessor input `{}` changed its resolved target while being read",
                file.accessed_path
            ));
        }
        result.insert(
            file.accessed_path.clone(),
            LockedPreprocessorFile {
                canonical_path: file.canonical_path.clone(),
                sha256: hex_digest(&bytes),
            },
        );
    }
    Ok(result)
}

fn artifact_path(config: &Config) -> Result<PathBuf, String> {
    validate_relative_path(&config.artifact, "artifact")?;
    Ok(config.directory.join(&config.artifact))
}

fn lock_path(config_path: &Path) -> Result<PathBuf, String> {
    let absolute = if config_path.is_absolute() {
        config_path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|error| format!("read current directory: {error}"))?
            .join(config_path)
    };
    let name = absolute
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("C++ import config path has no UTF-8 filename")?;
    Ok(absolute.with_file_name(format!("{name}.lock")))
}

fn reject_output_collisions(
    inputs: &ExportInputs<'_>,
    source: &Path,
    logical_source: &Path,
    dependencies: &[(String, PathBuf)],
) -> Result<(), String> {
    let [artifact, lock] = inputs.outputs;
    for (output_label, output) in [("artifact", artifact), ("lock", lock)] {
        for (input_label, input) in [
            ("config", inputs.config_path),
            ("source", Some(source)),
            ("logical source", Some(logical_source)),
            ("exporter", Some(inputs.exporter)),
            ("compilation database", Some(inputs.compilation_database)),
        ] {
            if input == Some(output.as_path()) {
                return Err(format!(
                    "C++ {output_label} output collides with the {input_label} input"
                ));
            }
        }
        for (_, dependency) in dependencies {
            if output == dependency {
                return Err(format!(
                    "C++ {output_label} output collides with a dependency input"
                ));
            }
        }
    }
    if artifact == lock {
        return Err("C++ artifact and lock outputs collide".into());
    }
    Ok(())
}

fn read_stable(path: &Path, max: usize, label: &str) -> Result<Vec<u8>, String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if !before.file_type().is_file() {
        return Err(format!(
            "{label} `{}` is not a regular file",
            path.display()
        ));
    }
    if before.len() > max as u64 {
        return Err(format!("{label} exceeds its {max}-byte limit"));
    }
    let bytes =
        fs::read(path).map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if bytes.len() > max {
        return Err(format!("{label} exceeds its {max}-byte limit"));
    }
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("re-read {label} `{}`: {error}", path.display()))?;
    if before.len() != after.len() || before.modified().ok() != after.modified().ok() {
        return Err(format!(
            "{label} `{}` changed while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn hex_digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn bounded_error(error: String) -> String {
    const MAX_CHARS: usize = 8_000;
    if error.chars().count() <= MAX_CHARS {
        error
    } else {
        format!(
            "{}... [diagnostic truncated]",
            error.chars().take(MAX_CHARS).collect::<String>()
        )
    }
}

/// A C++ unit of a Click project, as `click.project.json` describes it.
#[derive(Clone, Debug)]
pub(crate) struct UnitConfig {
    pub unit_name: String,
    /// The project root, absolute and canonical; artifact paths are
    /// relative to it.
    pub project_root: PathBuf,
    /// The digest of the unit's description, which each source's lock
    /// records.
    pub unit_digest: String,
    /// The unit's source root, absolute; the exporter's working directory.
    pub root: PathBuf,
    pub exceptions: bool,
    pub rtti: bool,
    /// Click's own description of the build: arguments every source is
    /// compiled with, before its own.
    pub args: Vec<String>,
    pub lock_path: PathBuf,
}

/// One logical source of a C++ unit and the functions selected from it.
#[derive(Clone, Debug)]
pub(crate) struct UnitSource {
    pub logical_source: String,
    pub translation_unit: String,
    pub functions: Vec<String>,
    pub dependencies: Vec<String>,
    pub library_assertions: Vec<CppLibraryAssertion>,
    pub exception_behavior: CppExceptionBehavior,
    pub args: Vec<String>,
    /// The artifact's path relative to the project root.
    pub artifact: String,
}

impl UnitConfig {
    fn config(&self, source: &UnitSource) -> Result<Config, String> {
        let config = Config {
            schema: CONFIG_SCHEMA,
            language: LANGUAGE.into(),
            standard: STANDARD.into(),
            target: TARGET.into(),
            exceptions: self.exceptions,
            exception_behavior: source.exception_behavior,
            rtti: self.rtti,
            // A unit names no exporter, database or working directory of its
            // own: the export receives them directly.
            exporter: "unit".into(),
            compilation_database: "unit".into(),
            working_directory: ".".into(),
            source: source.translation_unit.clone(),
            logical_source: source.logical_source.clone(),
            dependencies: source.dependencies.clone(),
            function: source.functions.first().cloned().unwrap_or_default(),
            library_assertions: source.library_assertions.clone(),
            artifact: source.artifact.clone(),
            directory: self.project_root.clone(),
            functions: source.functions.clone(),
        };
        validate_config(&config)?;
        Ok(config)
    }

    fn working_directory(&self) -> Result<PathBuf, String> {
        fs::canonicalize(&self.root).map_err(|error| {
            format!(
                "resolve the root `{}` of unit `{}`: {error}",
                self.root.display(),
                self.unit_name
            )
        })
    }

    /// The roots whose files are rechecked when loading: the unit root, then
    /// the project root.
    fn roots(&self) -> Result<Vec<PathBuf>, String> {
        Ok(vec![self.working_directory()?, self.project_root.clone()])
    }

    /// The compilation database Click synthesizes for one source from the
    /// unit's build description.
    fn compilation_database(
        &self,
        source: &UnitSource,
        working_directory: &Path,
    ) -> Result<Vec<u8>, String> {
        let mut arguments = vec![
            "clang++".to_string(),
            "-x".into(),
            "c++".into(),
            format!("-std={STANDARD}"),
            format!("--target={TARGET}"),
            if self.exceptions {
                "-fexceptions"
            } else {
                "-fno-exceptions"
            }
            .into(),
            if self.rtti { "-frtti" } else { "-fno-rtti" }.into(),
        ];
        arguments.extend(self.args.iter().chain(&source.args).cloned());
        arguments.extend([
            "-c".into(),
            source.translation_unit.clone(),
            "-o".into(),
            format!("{}.o", source.translation_unit),
        ]);
        serde_json::to_vec_pretty(&serde_json::json!([{
            "directory": working_directory,
            "file": source.translation_unit,
            "arguments": arguments,
        }]))
        .map_err(|error| format!("encode C++ compilation database: {error}"))
    }
}

/// Exports every source of a project unit with the exporter at `exporter`:
/// the unit's lock entry, keyed by logical source, and the artifacts to write.
pub(crate) fn prepare_unit(
    unit: &UnitConfig,
    sources: &[UnitSource],
    exporter: &Path,
) -> Result<(serde_json::Value, Vec<(PathBuf, Vec<u8>)>), String> {
    let exporter = fs::canonicalize(exporter)
        .map_err(|error| format!("C++ exporter `{}`: {error}", exporter.display()))?;
    let working_directory = unit.working_directory()?;
    let roots = unit.roots()?;
    let scratch = std::env::temp_dir().join(format!(
        "click-cpp-unit-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
    ));
    fs::create_dir_all(&scratch)
        .map_err(|error| format!("create `{}`: {error}", scratch.display()))?;
    let result = (|| {
        let mut entries = serde_json::Map::new();
        let mut artifacts = Vec::new();
        for (index, source) in sources.iter().enumerate() {
            let config = unit.config(source)?;
            let database = scratch.join(format!("{index}/compile_commands.json"));
            write_file_atomically(
                &database,
                &unit.compilation_database(source, &working_directory)?,
            )?;
            let outputs = [artifact_path(&config)?, unit.lock_path.clone()];
            let (mut lock, artifact) = export(
                &config,
                unit.unit_digest.clone(),
                &ExportInputs {
                    config_path: None,
                    exporter: &exporter,
                    compilation_database: &database,
                    working_directory: &working_directory,
                    outputs: &outputs,
                },
            )
            .map_err(bounded_error)?;
            lock.prepared_roots = roots
                .iter()
                .map(|root| root.to_string_lossy().into_owned())
                .collect();
            entries.insert(
                source.logical_source.clone(),
                serde_json::to_value(&lock).map_err(|error| error.to_string())?,
            );
            artifacts.push((outputs[0].clone(), artifact));
        }
        Ok((serde_json::Value::Object(entries), artifacts))
    })();
    let _ = fs::remove_dir_all(&scratch);
    result
}

/// Loads one logical source of a project unit from the unit's lock entry.
pub(crate) fn load_unit(
    unit: &UnitConfig,
    source: &UnitSource,
    lock: &serde_json::Value,
) -> Result<PreparedCppImport, String> {
    let config = unit.config(source)?;
    let lock = lock
        .get(&source.logical_source)
        .ok_or_else(|| {
            format!(
                "the project lock for unit `{}` has no source `{}`; run `click import lock`",
                unit.unit_name, source.logical_source
            )
        })
        .and_then(|value| {
            Lock::deserialize(value).map_err(|error| format!("parse C++ import lock: {error}"))
        })?;
    if lock.config_sha256 != unit.unit_digest {
        return Err(format!(
            "the project lock for unit `{}` does not match its description in `click.project.json`; run `click import lock` to prepare it again",
            unit.unit_name
        ));
    }
    load_locked(
        &config,
        lock,
        &unit.working_directory()?,
        &artifact_path(&config)?,
        &unit.roots()?,
    )
    .map_err(bounded_error)
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    /// A unit's preprocessor inputs under a prepared root are rechecked at
    /// the root's current location; inputs outside every root are pinned by
    /// their recorded digest and never read.
    #[test]
    fn rooted_preprocessor_inputs_follow_their_root_and_outside_inputs_stay_pinned() {
        let base = std::env::temp_dir().join(format!("click-cpp-rooted-{}", std::process::id()));
        let now = base.join("now");
        fs::create_dir_all(now.join("include")).unwrap();
        fs::write(now.join("include/local.h"), "int local;\n").unwrap();
        let prepared = PathBuf::from("/prepared/unit");
        let file = |path: &str| CppPreprocessorFile {
            accessed_path: path.into(),
            canonical_path: path.into(),
        };
        let files = vec![
            file("/prepared/unit/include/local.h"),
            file("/usr/include/stdint.h"),
        ];
        let locked = BTreeMap::from([
            (
                "/prepared/unit/include/local.h".to_string(),
                LockedPreprocessorFile {
                    canonical_path: "/prepared/unit/include/local.h".into(),
                    sha256: hex_digest(b"int local;\n"),
                },
            ),
            (
                "/usr/include/stdint.h".to_string(),
                LockedPreprocessorFile {
                    canonical_path: "/usr/include/stdint.h".into(),
                    sha256: hex_digest(b"not read"),
                },
            ),
        ]);
        let roots = [(prepared, now.clone())];
        let current = check_rooted_preprocessor_files(&files, &locked, &roots).unwrap();
        assert_eq!(
            current["/prepared/unit/include/local.h"].canonical_path,
            now.join("include/local.h").to_string_lossy()
        );
        assert_eq!(
            current["/usr/include/stdint.h"].canonical_path,
            "/usr/include/stdint.h"
        );

        fs::write(now.join("include/local.h"), "int changed;\n").unwrap();
        let error = check_rooted_preprocessor_files(&files, &locked, &roots).unwrap_err();
        assert!(
            error.contains("local.h") && error.contains("differs"),
            "{error}"
        );
        let error = check_rooted_preprocessor_files(&files[..1], &locked, &roots).unwrap_err();
        assert!(error.contains("inventory differs"), "{error}");
        let _ = fs::remove_dir_all(&base);
    }
}
