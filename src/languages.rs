//! Target languages supported by Surface Click.

pub mod c;
pub(crate) mod compiler_process;
pub mod cpp;
pub(crate) mod envelope;
pub(crate) mod inputs;
pub(crate) mod portable_paths;
pub mod rust;

/// The language a program's sources are written in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceLanguage {
    C,
    Cpp,
    Rust,
}

impl SourceLanguage {
    /// The language of the source a `verifying` clause names, by its
    /// extension.
    pub fn of_source_path(path: &str) -> Self {
        if path.ends_with(".rs") {
            Self::Rust
        } else if path.ends_with(".cpp") {
            Self::Cpp
        } else {
            Self::C
        }
    }

    /// The language of a file's `verifying` sources: Rust when any is a Rust
    /// source, since that decides which signature syntax the sidecar admits.
    pub fn of_sources<'p>(paths: impl IntoIterator<Item = &'p str>) -> Self {
        paths
            .into_iter()
            .map(Self::of_source_path)
            .max_by_key(|language| *language == Self::Rust)
            .unwrap_or(Self::C)
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::C => "C",
            Self::Cpp => "C++",
            Self::Rust => "Rust",
        }
    }
}

impl std::fmt::Display for SourceLanguage {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.name())
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
            Self::Cpp(import) => import.prepared_execution(),
            Self::Rust(import) => import.prepared_execution(),
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
    pub fn language(&self) -> SourceLanguage {
        match self {
            Self::Cpp(_) => SourceLanguage::Cpp,
            Self::Rust(_) => SourceLanguage::Rust,
        }
    }
}
impl From<&PreparedProgram> for PreparedProgram {
    fn from(program: &PreparedProgram) -> Self {
        program.clone()
    }
}
impl From<cpp::PreparedCppImport> for PreparedProgram {
    fn from(import: cpp::PreparedCppImport) -> Self {
        Self::Cpp(import)
    }
}
impl From<&cpp::PreparedCppImport> for PreparedProgram {
    fn from(import: &cpp::PreparedCppImport) -> Self {
        Self::Cpp(import.clone())
    }
}
impl From<rust::PreparedRustImport> for PreparedProgram {
    fn from(import: rust::PreparedRustImport) -> Self {
        Self::Rust(import)
    }
}
impl From<&rust::PreparedRustImport> for PreparedProgram {
    fn from(import: &rust::PreparedRustImport) -> Self {
        Self::Rust(import.clone())
    }
}

/// An import's lowered execution, computed on first use. Lowering depends
/// only on the import, so every session over the same import shares it.
#[derive(Debug, Default)]
pub(crate) struct ExecutionCache(std::sync::OnceLock<std::sync::Arc<PreparedExecution>>);

impl ExecutionCache {
    pub(crate) fn get_or_lower(
        &self,
        lower: impl FnOnce() -> Result<std::sync::Arc<PreparedExecution>, String>,
    ) -> Result<std::sync::Arc<PreparedExecution>, String> {
        if let Some(execution) = self.0.get() {
            return Ok(execution.clone());
        }
        let execution = lower()?;
        Ok(self.0.get_or_init(|| execution).clone())
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
    /// The layout name of each record whose source spelling differs from
    /// it, by that spelling: a C++ class template instance,
    /// `Stored<long long>`, is laid out as `Stored__long_long`.
    pub record_spellings: std::collections::BTreeMap<String, String>,
}

/// `text` with every whole importer name it contains spelled as its source
/// language spells it: a Rust item by its path, `quad::walk`, and a C++
/// declaration as C++ names it, `Square::area`.
pub fn display_source_names(text: &str) -> std::borrow::Cow<'_, str> {
    match rust::names::display_rust_names(text) {
        std::borrow::Cow::Borrowed(text) => cpp::names::display_cpp_names(text),
        std::borrow::Cow::Owned(text) => {
            std::borrow::Cow::Owned(cpp::names::display_cpp_names(&text).into_owned())
        }
    }
}

/// The source spelling `name` stands for when it is a whole importer name.
pub fn source_display_name(name: &str) -> Option<String> {
    rust::names::rust_display_name(name).or_else(|| cpp::names::cpp_display_name(name))
}

/// Whether the claim label `label` is the one `requested` names, as the
/// importer spells it or as its source language does.
pub fn claim_label_matches(label: &str, requested: &str) -> bool {
    label == requested || (requested.contains("::") && display_source_names(label) == requested)
}
