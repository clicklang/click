//! The pinned semantic C++ frontend boundary.
//!
//! C++ source is interpreted by the repository-owned LibTooling exporter.
//! This module validates and locks that typed output; it deliberately does not
//! feed C++ text or generated C through the C parser.

mod budget;
mod import;
mod interface;
mod lifetime;
mod lowering;
mod names;
mod scalar;
mod schema;
mod validity;

pub use import::{PreparedCppImport, load_import, refresh_import};
pub use lowering::{LoweredCppFunction, lower_import};
pub use schema::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppConstant, CppConstantReference,
    CppConstevalMetadata, CppExceptionBehavior, CppExport, CppExpression, CppField,
    CppFieldInitializer, CppFieldReference, CppFunction, CppFunctionKind, CppFunctionReference,
    CppInitializer, CppLibraryAssertion, CppLibraryAssertionKind, CppLibraryMetadata,
    CppLiteralConstructor, CppLiteralMetadata, CppLiteralMetadataBinding, CppPlace,
    CppPlaceReference, CppProfile, CppRecord, CppSpan, CppStatement, CppType, CppTypeAlias,
};
