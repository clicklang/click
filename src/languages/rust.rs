//! Experimental safe Rust imports, compiler-owned extraction and direct kernel lowering.
pub mod borrow_frontiers;
mod charon;
mod crate_inputs;
mod import;
pub(crate) mod lowering;
pub mod names;
mod profile;
mod runtime;
pub mod schema;
pub(crate) use crate_inputs::CrateConfig;
pub use import::{PreparedRustImport, load_import, refresh_import};
pub(crate) use import::{UnitConfig, load_unit, prepare_unit};

/// Prepare the same contract-facing execution package as the other typed frontend.
pub(crate) fn prepare_execution(
    import: &PreparedRustImport,
) -> Result<std::sync::Arc<crate::languages::PreparedExecution>, String> {
    let (functions, layouts) =
        lowering::lower_with_identity(import.export(), Some(import.identity()))?;
    Ok(std::sync::Arc::new(crate::languages::PreparedExecution {
        functions,
        layouts,
        library_contracts: String::new(),
    }))
}
