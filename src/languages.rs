//! Program languages supported by Surface Click.

use std::fs;
use std::path::Path;

pub mod c;
pub(crate) mod compiler_process;
pub mod cpp;
pub mod rust;

#[derive(Clone, Debug)]
pub enum PreparedCompilerImport {
    C(Vec<c::compiler_import::PreparedCImport>),
    Cpp(cpp::PreparedCppImport),
    Rust(rust::PreparedRustImport),
}

fn import_language(config_path: &Path) -> Result<Option<String>, String> {
    const MAX_CONFIG_BYTES: u64 = 1 << 20;
    let metadata = fs::symlink_metadata(config_path)
        .map_err(|error| format!("read import config `{}`: {error}", config_path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_CONFIG_BYTES {
        return Err("compiler import config must be a regular file of at most 1 MiB".into());
    }
    let bytes = fs::read(config_path)
        .map_err(|error| format!("read import config `{}`: {error}", config_path.display()))?;
    if bytes.len() > MAX_CONFIG_BYTES as usize {
        return Err("compiler import config exceeds its 1 MiB limit".into());
    }
    let value: serde_json::Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("parse import config: {error}"))?;
    match value.get("language") {
        Some(serde_json::Value::String(language)) => Ok(Some(language.clone())),
        Some(_) => Err("compiler import language must be a string".into()),
        None => Ok(None),
    }
}

pub fn load_compiler_import(config_path: &Path) -> Result<PreparedCompilerImport, String> {
    match import_language(config_path)?.as_deref() {
        Some("c++") => cpp::load_import(config_path).map(PreparedCompilerImport::Cpp),
        Some("rust") => rust::load_import(config_path).map(PreparedCompilerImport::Rust),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::load_imports(config_path).map(PreparedCompilerImport::C),
    }
}

/// Explicitly refresh the compiler-owned artifact selected by an import file.
///
/// Existing C configurations have no language field. Typed C++ and Rust
/// boundaries identify themselves explicitly and never fall back to C handling.
pub fn refresh_compiler_import(config_path: &Path) -> Result<(), String> {
    match import_language(config_path)?.as_deref() {
        Some("c++") => cpp::refresh_import(config_path),
        Some("rust") => rust::refresh_import(config_path),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::create_lock(config_path),
    }
}

/// Immutable compiler-owned inputs shared by the verification tools.
#[derive(Clone, Debug)]
pub enum PreparedProgram {
    Cpp(cpp::PreparedCppImport),
    Rust(rust::PreparedRustImport),
}
impl PreparedProgram {
    pub(crate) fn prepare_execution(&self) -> Result<std::sync::Arc<PreparedExecution>, String> {
        match self {
            Self::Cpp(import) => Ok(cpp::lower_import(import)?.prepared_execution()),
            Self::Rust(import) => rust::prepare_execution(import),
        }
    }

    pub fn logical_source(&self) -> &str {
        match self {
            Self::Cpp(p) => p.logical_source(),
            Self::Rust(p) => p.logical_source(),
        }
    }
    pub fn identity(&self) -> &str {
        match self {
            Self::Cpp(p) => p.identity(),
            Self::Rust(p) => p.identity(),
        }
    }
    pub fn language(&self) -> &'static str {
        match self {
            Self::Cpp(_) => "C++",
            Self::Rust(_) => "Rust",
        }
    }
}
pub trait PreparedProgramSource {
    fn prepared_program(&self) -> PreparedProgram;
}
impl PreparedProgramSource for PreparedProgram {
    fn prepared_program(&self) -> PreparedProgram {
        self.clone()
    }
}
impl PreparedProgramSource for cpp::PreparedCppImport {
    fn prepared_program(&self) -> PreparedProgram {
        PreparedProgram::Cpp(self.clone())
    }
}
impl PreparedProgramSource for rust::PreparedRustImport {
    fn prepared_program(&self) -> PreparedProgram {
        PreparedProgram::Rust(self.clone())
    }
}

/// A frontend's checked execution and contract-facing metadata. Language-specific
/// interpretation is complete before the shared verifier consumes this package.
#[derive(Clone, Debug)]
pub(crate) struct PreparedExecution {
    pub functions: Vec<c::syntax::C0Function>,
    pub layouts: std::collections::BTreeMap<String, c::syntax::C0StructLayout>,
    /// Click `extern` contracts the frontend supplies for library functions
    /// the program calls but does not define, parsed with the sidecar.
    pub library_contracts: String,
}
