//! Experimental safe Rust imports, compiler-owned typed HIR and direct kernel lowering.
mod charon;
mod import;
pub(crate) mod lowering;
pub mod schema;
pub use import::{PreparedRustImport, load_import, refresh_import};
pub(crate) use lowering::lower;
