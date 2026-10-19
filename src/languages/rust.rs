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
pub use import::PreparedRustImport;
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
        library_contracts: enum_declarations(import.export()),
        record_spellings: Default::default(),
    }))
}

/// The `spec enum` each crate enum is to its sidecar: the same name, its
/// variants in declaration order, and each field by its Rust type, so a
/// contract constructs and matches the values the program does. A struct
/// variant's fields are positional, `Shape::Rect(width, height)`.
fn enum_declarations(export: &schema::RustExport) -> String {
    let mut declarations = String::new();
    for declared in &export.enums {
        declarations.push_str(&format!("\nspec enum {} {{\n", declared.name));
        for variant in &declared.variants {
            declarations.push_str("    ");
            declarations.push_str(&variant.name);
            if !variant.fields.is_empty() {
                let fields = variant
                    .fields
                    .iter()
                    .map(|field| match field {
                        schema::Type::I32 => "i32",
                        schema::Type::U8 => "u8",
                        schema::Type::U16 => "u16",
                        schema::Type::U32 => "u32",
                        schema::Type::Usize => "usize",
                        schema::Type::Bool => "bool",
                        _ => unreachable!("the importer admits only scalar enum fields"),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                declarations.push_str(&format!("({fields})"));
            }
            declarations.push_str(",\n");
        }
        declarations.push_str("}\n");
    }
    declarations
}
