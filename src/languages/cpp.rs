//! The pinned semantic C++ frontend boundary.
//!
//! C++ source is interpreted by the repository-owned LibTooling exporter.
//! This module validates and locks that typed output; it deliberately does not
//! feed C++ text or generated C through the C parser.

mod budget;
mod construction;
mod import;
mod interface;
mod lifetime;
mod lowering;
pub(crate) mod names;
mod scalar;
mod schema;
pub(crate) mod standard_library;
mod validity;

pub use import::{PreparedCppImport, load_import, refresh_import};
pub(crate) use import::{UnitConfig, UnitSource, load_unit, prepare_unit};
pub use lowering::{LoweredCppFunction, lower_import};
pub use schema::{
    CppBase, CppBaseReference, CppBinaryOperator, CppByteTemplateArgument, CppCallArgument,
    CppCleanup, CppCondition, CppConditionCall, CppConstant, CppConstantReference,
    CppConstevalMetadata, CppExceptionBehavior, CppExport, CppExpression, CppField,
    CppFieldInitializer, CppFieldReference, CppFunction, CppFunctionKind, CppFunctionReference,
    CppInitializer, CppLibraryAssertion, CppLibraryAssertionKind, CppLibraryMetadata,
    CppLiteralConstructor, CppLiteralMetadata, CppLiteralMetadataBinding, CppPlace,
    CppPlaceReference, CppProfile, CppProjection, CppRecord, CppScalarCastKind,
    CppScalarConversion, CppSpan, CppStatement, CppType, CppTypeAlias,
};
