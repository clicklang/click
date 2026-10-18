//! Locked semantic imports produced by the pinned C++ frontend.
//!
//! `prepare_unit` is the only operation in this module that executes the
//! Clang-based exporter. `load_unit` validates a project unit's sources, lock,
//! and stored semantic artifacts without consulting or executing the exporter.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::schema::{
    CppExceptionBehavior, CppExport, CppLibraryAssertion, CppPreprocessorFile, CppProfile,
    CppStatement, LANGUAGE, MAX_PREPROCESSOR_FILES, STANDARD, TARGET,
};
use crate::cli::write_file_atomically;
use crate::languages::c::target::COptimization;
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use crate::languages::envelope::{self, Entry, SourceParts};
use crate::languages::inputs::{Leaf, hex_digest};
use crate::languages::portable_paths::PathLabels;

const CONFIG_SCHEMA: u32 = 6;
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

/// A C++ unit's section of its project lock entry: for each logical source,
/// what the envelope's common fields do not record
/// (`crate::languages::envelope`).
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Section {
    sources: BTreeMap<String, SectionSource>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SectionSource {
    schema: u32,
    source_sha256: String,
    logical_source_sha256: String,
    compilation_database_sha256: String,
    dependencies: BTreeMap<String, String>,
    /// The canonical path of each preprocessor input whose accessed path
    /// differs from it.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    canonical_paths: BTreeMap<String, String>,
    profile: CppProfile,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    prepared_roots: Vec<String>,
}

const LANGUAGE_NAME: &str = "c++";

/// The envelope entry recording `locks`, keyed by logical source, whose
/// artifacts are at `artifacts`, relative to the project. A source's inputs
/// are the preprocessor inputs the exporter read.
fn lock_entry(
    locks: &BTreeMap<String, Lock>,
    artifacts: &BTreeMap<String, String>,
) -> Result<Entry, String> {
    let first = locks.values().next().ok_or("a C++ unit lists a source")?;
    if locks.values().any(|lock| {
        lock.config_sha256 != first.config_sha256 || lock.exporter_sha256 != first.exporter_sha256
    }) {
        return Err(
            "the sources of a C++ unit were prepared from different descriptions or exporters"
                .into(),
        );
    }
    let mut sources = BTreeMap::new();
    let mut section = Section {
        sources: BTreeMap::new(),
    };
    for (logical, lock) in locks {
        let inputs = lock
            .preprocessor_files
            .iter()
            .map(|(accessed, file)| (accessed.clone(), file.sha256.clone()))
            .collect();
        let artifact = artifacts
            .get(logical)
            .ok_or_else(|| format!("C++ source `{logical}` has no artifact"))?;
        sources.insert(
            logical.clone(),
            SourceParts {
                inputs,
                artifact: envelope::Artifact {
                    path: artifact.clone(),
                    sha256: lock.artifact_sha256.clone(),
                    bytes: lock.artifact_bytes,
                },
            },
        );
        section.sources.insert(
            logical.clone(),
            SectionSource {
                schema: lock.schema,
                source_sha256: lock.source_sha256.clone(),
                logical_source_sha256: lock.logical_source_sha256.clone(),
                compilation_database_sha256: lock.compilation_database_sha256.clone(),
                dependencies: lock.dependencies.clone(),
                canonical_paths: lock
                    .preprocessor_files
                    .iter()
                    .filter(|(accessed, file)| **accessed != file.canonical_path)
                    .map(|(accessed, file)| (accessed.clone(), file.canonical_path.clone()))
                    .collect(),
                profile: lock.profile.clone(),
                prepared_roots: lock.prepared_roots.clone(),
            },
        );
    }
    Ok(Entry::new(
        LANGUAGE_NAME,
        first.config_sha256.clone(),
        envelope::Frontend {
            name: "clang".into(),
            identity: first.exporter_sha256.clone(),
        },
        sources,
        serde_json::to_value(section).expect("a C++ lock section serializes"),
    ))
}

/// The lock of `logical` that `entry` records.
fn entry_lock(entry: &Entry, logical: &str) -> Result<Lock, String> {
    let mut section = Section::deserialize(entry.section(LANGUAGE_NAME).expect("parsed for C++"))
        .map_err(|error| format!("parse the C++ lock section: {error}"))?;
    let part = section.sources.remove(logical).ok_or_else(|| {
        format!("the project lock has no source `{logical}`; run `click import lock`")
    })?;
    let recorded = entry.sources.get(logical).ok_or_else(|| {
        format!("the project lock has no source `{logical}`; run `click import lock`")
    })?;
    Ok(Lock {
        schema: part.schema,
        config_sha256: entry.unit.clone(),
        exporter_sha256: entry.frontend.identity.clone(),
        compilation_database_sha256: part.compilation_database_sha256,
        source_sha256: part.source_sha256,
        logical_source_sha256: part.logical_source_sha256,
        dependencies: part.dependencies,
        preprocessor_files: recorded
            .inputs
            .iter()
            .map(|(accessed, sha256)| {
                (
                    accessed.clone(),
                    LockedPreprocessorFile {
                        canonical_path: part
                            .canonical_paths
                            .get(accessed)
                            .unwrap_or(accessed)
                            .clone(),
                        sha256: sha256.clone(),
                    },
                )
            })
            .collect(),
        artifact_sha256: recorded.artifact.sha256.clone(),
        artifact_bytes: recorded.artifact.bytes,
        profile: part.profile,
        prepared_roots: part.prepared_roots,
    })
}

/// The resolved inputs and outputs of one export.
struct ExportInputs<'a> {
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
    // The compiler may open a file no configured input names, such as a
    // header the source includes; none may be an output.
    crate::languages::inputs::reject_output_collisions(
        &[
            ("C++ artifact", &inputs.outputs[0]),
            ("C++ lock", &inputs.outputs[1]),
        ],
        preprocessor_files_after
            .values()
            .map(|file| ("preprocessor", Path::new(&file.canonical_path))),
    )?;
    let exporter_sha256 = hex_digest(&exporter_bytes);
    let compilation_database_sha256 = hex_digest(&compilation_database_before);
    let source_sha256 = hex_digest(&source_before);
    let logical_source_sha256 = hex_digest(&logical_source_before);
    let dependency_digests = dependency_bytes_before
        .iter()
        .map(|(path, bytes)| (path.clone(), hex_digest(bytes)))
        .collect::<BTreeMap<_, _>>();
    let artifact_sha256 = hex_digest(&artifact);
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

/// Checks a lock against `config`'s current inputs and loads `artifact`.
/// `current_roots` are the current locations of a project unit's
/// `prepared_roots`; without them, every preprocessor input is re-read at its
/// recorded path. The import's identity is the lock entry's, which the
/// caller sets.
fn load_locked(
    config: &Config,
    lock: Lock,
    working_directory: &Path,
    artifact: Vec<u8>,
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

    Ok(PreparedCppImport {
        inner: Arc::new(PreparedInner {
            logical_source: config.logical_source.clone(),
            identity: String::new(),
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
        let relocate = |recorded: &str| {
            roots.iter().find_map(|(prepared, now)| {
                Path::new(recorded)
                    .strip_prefix(prepared)
                    .ok()
                    .map(|relative| now.join(relative))
            })
        };
        let Some(path) = relocate(&file.canonical_path) else {
            current.insert(file.accessed_path.clone(), entry.clone());
            continue;
        };
        // The compiler opens the accessed path, so a retargeted symlink must
        // still resolve to the locked file.
        if let Some(accessed) = relocate(&file.accessed_path) {
            let resolved = fs::canonicalize(&accessed)
                .map_err(|error| format!("resolve C++ input `{}`: {error}", accessed.display()))?;
            if resolved != fs::canonicalize(&path).unwrap_or_else(|_| path.clone()) {
                return Err(format!(
                    "C++ input `{}` changed its resolved target since the import lock; run `click import lock`",
                    accessed.display()
                ));
            }
        }
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

/// Replaces each label in `lock` and `artifact`, which `labels` names, by
/// its root, or each root by its label when `portable`. The artifact's
/// preprocessor inventory is sorted again under the new spelling, so a
/// portable artifact is the same from every checkout. The artifact digest
/// follows the replaced text.
fn relabel(
    labels: &PathLabels,
    lock: &Lock,
    artifact: &[u8],
    portable: bool,
) -> Result<(Lock, Vec<u8>), String> {
    let replace = |text: &str| {
        if portable {
            labels.to_portable(text)
        } else {
            labels.to_absolute(text)
        }
    };
    let artifact = std::str::from_utf8(artifact)
        .map_err(|_| "C++ semantic artifact is not UTF-8".to_string())?;
    let mut value: serde_json::Value = serde_json::from_str(&replace(artifact))
        .map_err(|error| format!("parse C++ semantic artifact: {error}"))?;
    if let Some(files) = value
        .get_mut("preprocessor_files")
        .and_then(serde_json::Value::as_array_mut)
    {
        files.sort_by(|left, right| {
            left["accessed_path"]
                .as_str()
                .cmp(&right["accessed_path"].as_str())
        });
    }
    let mut artifact = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    artifact.push(b'\n');
    let text = serde_json::to_string(lock).map_err(|error| error.to_string())?;
    let mut lock: Lock = serde_json::from_str(&replace(&text))
        .map_err(|error| format!("parse C++ import lock: {error}"))?;
    lock.artifact_sha256 = hex_digest(&artifact);
    lock.artifact_bytes = artifact.len();
    Ok((lock, artifact))
}

/// Where a loaded lock places the pinned Clang's resource directory, whose
/// builtin headers lie outside every project root: they are pinned by their
/// recorded digest and never read, so the directory need not exist.
const PINNED_RESOURCE_ROOT: &str = "/click-pinned-clang-resource";

/// The pinned Clang resource directory the exporter at `exporter` supplies
/// to a command that names none.
fn exporter_resource_directory(
    exporter: &Path,
    working_directory: &Path,
) -> Result<PathBuf, String> {
    let output = run_compiler(
        exporter,
        &["--print-resource-dir".to_string()],
        working_directory,
        &BTreeMap::new(),
        CompilerLimits {
            timeout: Duration::from_secs(10),
            max_stdout_bytes: 4096,
            max_stderr_bytes: MAX_DIAGNOSTIC_BYTES,
        },
    )
    .map_err(|error| format!("ask the C++ exporter for its resource directory: {error}"))?;
    let text = String::from_utf8(output.stdout)
        .map_err(|_| "the C++ exporter's resource directory is not UTF-8".to_string())?;
    Ok(PathBuf::from(text.trim()))
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

fn reject_output_collisions(
    inputs: &ExportInputs<'_>,
    source: &Path,
    logical_source: &Path,
    dependencies: &[(String, PathBuf)],
) -> Result<(), String> {
    let [artifact, lock] = inputs.outputs;
    crate::languages::inputs::reject_output_collisions(
        &[("C++ artifact", artifact), ("C++ lock", lock)],
        [
            ("source", source),
            ("logical source", logical_source),
            ("exporter", inputs.exporter),
            ("compilation database", inputs.compilation_database),
        ]
        .into_iter()
        .chain(
            dependencies
                .iter()
                .map(|(_, path)| ("dependency", path.as_path())),
        ),
    )
}

/// Reads a C++ input or artifact, which must itself be a regular file.
fn read_stable(path: &Path, max: usize, label: &str) -> Result<Vec<u8>, String> {
    crate::languages::inputs::read_stable(path, max, label, Leaf::Refuse)
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
    /// The project's optimization level, which every source is exported at.
    pub optimization: COptimization,
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
        validate_unit_args(&self.args, self.optimization)
            .map_err(|error| format!("unit `{}`: {error}", self.unit_name))?;
        validate_unit_args(&source.args, self.optimization).map_err(|error| {
            format!(
                "unit `{}` source `{}`: {error}",
                self.unit_name, source.logical_source
            )
        })?;
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
            self.optimization.flag().into(),
        ];
        if self.optimization.optimizes() {
            arguments.push("-fno-strict-aliasing".into());
        }
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

/// The arguments Click sets itself for every C++ source; a unit may not name
/// them.
const FIXED_ARGUMENT_PREFIXES: &[&str] = &[
    "-std=",
    "--target=",
    "-target",
    "-x",
    "-fexceptions",
    "-fno-exceptions",
    "-frtti",
    "-fno-rtti",
    "-fstrict-aliasing",
    "-fno-strict-aliasing",
];

/// Spellings that are a preprocessor input, a semantic setting the exporter
/// observes from Clang, or affect only code generation and diagnostics
/// (`docs/reference/cli/import.md#c-unit-arguments`).
const ACCEPTED_ARGUMENTS: &[&str] = &[
    "-nostdinc",
    "-nostdinc++",
    "-funsigned-char",
    "-fsigned-char",
    "-ffreestanding",
    "-g",
    "-fstack-protector",
    "-fstack-protector-strong",
    "-fstack-protector-all",
    "-fstack-clash-protection",
    "-fcf-protection",
    "-fcf-protection=full",
    "-w",
];

/// Preprocessor options that take a value, either joined or as the next
/// argument.
const VALUE_ARGUMENTS: &[&str] = &["-D", "-U", "-I", "-iquote", "-isystem", "-include"];

/// Checks a C++ unit's or source's arguments against the flag policy: each
/// is a preprocessor input, a semantic setting the exporter observes, or an
/// option affecting only code generation and diagnostics; Click itself sets
/// the language, target, optimization level and aliasing rules. As for C, an
/// argument may repeat the project's level but not name another.
fn validate_unit_args(args: &[String], optimization: COptimization) -> Result<(), String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let position = index + 1;
        index += 1;
        if argument.is_empty() || argument.contains('\0') {
            return Err(format!("argument {position} is empty or contains NUL"));
        }
        if argument == optimization.flag() {
            continue;
        }
        if argument.starts_with("-O") {
            return Err(format!(
                "argument {position} `{argument}` names an optimization level; the project \
                 verifies its units at `{}`, set by `optimization` in `click.project.json`",
                optimization.flag()
            ));
        }
        if FIXED_ARGUMENT_PREFIXES
            .iter()
            .any(|fixed| argument == fixed || (fixed.ends_with('=') && argument.starts_with(fixed)))
        {
            return Err(format!(
                "argument {position} `{argument}` is set by Click for every C++ unit"
            ));
        }
        if ACCEPTED_ARGUMENTS.contains(&argument.as_str())
            || argument.starts_with("--sysroot=")
            || argument.starts_with("-fmacro-prefix-map=")
            || (argument.starts_with("-W")
                && !["-Wa,", "-Wl,", "-Wp,"]
                    .iter()
                    .any(|pass| argument.starts_with(pass)))
        {
            continue;
        }
        if argument == "--sysroot" {
            if index == args.len() {
                return Err(format!(
                    "missing value after argument {position} `{argument}`"
                ));
            }
            index += 1;
            continue;
        }
        let Some(option) = VALUE_ARGUMENTS
            .iter()
            .find(|option| argument.starts_with(**option))
        else {
            return Err(format!(
                "unsupported C++ argument {position} `{argument}`; a unit accepts preprocessor \
                 inputs, `-funsigned-char`, `-fsigned-char`, `-ffreestanding`, and options \
                 affecting only code generation or diagnostics \
                 (`docs/reference/cli/import.md#c-unit-arguments`)"
            ));
        };
        let value = if argument.len() == option.len() {
            if index == args.len() || args[index].is_empty() {
                return Err(format!(
                    "missing value after argument {position} `{argument}`"
                ));
            }
            index += 1;
            &args[index - 1]
        } else {
            &argument[option.len()..]
        };
        if matches!(*option, "-D" | "-U")
            && value.split(['=', '(']).next().unwrap_or(value).trim() == "__OPTIMIZE__"
        {
            return Err(format!(
                "argument {position} defines `__OPTIMIZE__`, which the optimization level sets"
            ));
        }
    }
    Ok(())
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
    let resources = exporter_resource_directory(&exporter, &working_directory)?;
    let labels = PathLabels::new(&[
        ("$unit", roots[0].as_path()),
        ("$project", roots[1].as_path()),
        ("$clang-resource", resources.as_path()),
    ])?;
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
        let mut locks = BTreeMap::new();
        let mut artifact_paths = BTreeMap::new();
        let mut artifacts = Vec::new();
        for (index, source) in sources.iter().enumerate() {
            let config = unit.config(source)?;
            let database = scratch.join(format!("{index}/compile_commands.json"));
            let database_bytes = unit.compilation_database(source, &working_directory)?;
            write_file_atomically(&database, &database_bytes)?;
            let outputs = [artifact_path(&config)?, unit.lock_path.clone()];
            let (lock, artifact) = export(
                &config,
                unit.unit_digest.clone(),
                &ExportInputs {
                    exporter: &exporter,
                    compilation_database: &database,
                    working_directory: &working_directory,
                    outputs: &outputs,
                },
            )
            .map_err(bounded_error)?;
            // The lock and artifact name the unit's own files by their root's
            // label, so they read the same from any checkout.
            let (mut lock, artifact) = relabel(&labels, &lock, &artifact, true)?;
            lock.prepared_roots = vec!["$unit".into(), "$project".into()];
            lock.compilation_database_sha256 = hex_digest(
                labels
                    .to_portable(&String::from_utf8_lossy(&database_bytes))
                    .as_bytes(),
            );
            locks.insert(source.logical_source.clone(), lock);
            artifact_paths.insert(source.logical_source.clone(), source.artifact.clone());
            artifacts.push((outputs[0].clone(), artifact));
        }
        let entry = lock_entry(&locks, &artifact_paths)?;
        Ok((
            serde_json::to_value(entry).map_err(|error| error.to_string())?,
            artifacts,
        ))
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
    let entry = Entry::parse(LANGUAGE_NAME, &unit.unit_name, lock)?;
    let lock = entry_lock(&entry, &source.logical_source)?;
    if lock.config_sha256 != unit.unit_digest {
        return Err(format!(
            "the project lock for unit `{}` does not match its description in `click.project.json`; run `click import lock` to prepare it again",
            unit.unit_name
        ));
    }
    let artifact = read_stable(
        &artifact_path(&config)?,
        MAX_ARTIFACT_BYTES,
        "C++ semantic artifact",
    )?;
    if lock.artifact_bytes != artifact.len() || lock.artifact_sha256 != hex_digest(&artifact) {
        return Err("C++ semantic artifact differs from the import lock; refresh it".into());
    }
    // Checked as recorded, the lock and artifact are then read with each
    // root's label replaced by the root's current location.
    let roots = unit.roots()?;
    let labels = PathLabels::new(&[
        ("$unit", roots[0].as_path()),
        ("$project", roots[1].as_path()),
        ("$clang-resource", Path::new(PINNED_RESOURCE_ROOT)),
    ])?;
    let (current, artifact) = relabel(&labels, &lock, &artifact, false)?;
    // The identity is checked after the inputs and artifact, so a changed
    // input is named before a mismatched identity.
    let mut import = load_locked(
        &config,
        current,
        &unit.working_directory()?,
        artifact,
        &roots,
    )
    .map_err(bounded_error)?;
    Arc::get_mut(&mut import.inner)
        .expect("a freshly loaded import is not shared")
        .identity = entry.checked_identity(LANGUAGE_NAME, &source.logical_source)?;
    Ok(import)
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
