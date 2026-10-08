use super::scalar::{Scalar, ScalarKind, same_scalar_type, same_unqualified_integer_type};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::{Deserialize, Serialize};

// Validation follows lexical scopes. A child owns only its declarations and
// borrows its parent; entering a scope never copies or scans outer places.
#[derive(Default)]
struct ValidationPlaces<'a> {
    parent: Option<&'a ValidationPlaces<'a>>,
    declarations: BTreeMap<String, (String, CppType)>,
    names: BTreeSet<String>,
}

impl<'a> ValidationPlaces<'a> {
    fn new() -> Self {
        Self::default()
    }

    fn child(&self) -> ValidationPlaces<'_> {
        ValidationPlaces {
            parent: Some(self),
            ..ValidationPlaces::default()
        }
    }

    fn get(&self, id: &str) -> Option<&(String, CppType)> {
        self.declarations
            .get(id)
            .or_else(|| self.parent.and_then(|parent| parent.get(id)))
    }

    fn contains_key(&self, id: &str) -> bool {
        self.get(id).is_some()
    }

    fn contains_name(&self, name: &str) -> bool {
        self.names.contains(name) || self.parent.is_some_and(|parent| parent.contains_name(name))
    }

    fn insert_name(&mut self, name: String) -> bool {
        if self.contains_name(&name) {
            return false;
        }
        self.names.insert(name)
    }

    fn insert(&mut self, id: String, place: (String, CppType)) -> Result<(), ()> {
        // Duplicate identities are errors; do not hide an outer declaration.
        if self.contains_key(&id) {
            return Err(());
        }
        self.declarations.insert(id, place);
        Ok(())
    }
}

pub(crate) const EXPORT_SCHEMA: u32 = 43;
pub(crate) const MAX_PREPROCESSOR_FILES: usize = 4096;
pub(crate) const LANGUAGE: &str = "c++";
pub(crate) const STANDARD: &str = "c++20";
pub(crate) const TARGET: &str = "x86_64-unknown-linux-gnu";
pub(crate) const CLANG_VERSION: &str = "19.1.7";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppExport {
    pub schema: u32,
    pub language: String,
    pub profile: CppProfile,
    pub exception_behavior: CppExceptionBehavior,
    pub logical_source: String,
    pub dependencies: Vec<String>,
    pub preprocessor_files: Vec<CppPreprocessorFile>,
    pub constants: Vec<CppConstant>,
    pub records: Vec<CppRecord>,
    pub function: CppFunction,
    pub reachable_functions: Vec<CppFunction>,
}

/// An explicitly assumed external contract, not a verified implementation.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppLibraryAssertion {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub literal_constructor: Option<CppLiteralConstructor>,
    pub kind: CppLibraryAssertionKind,
    pub function: String,
    pub header: String,
    pub sha256: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CppLibraryAssertionKind {
    CheckedBooleanStatement,
    CheckedBooleanStatementWithConstevalMetadata,
    CheckedBooleanStatementWithLiteralMetadata,
}

/// Assumes defined, normally returning construction from a narrow string literal,
/// with no caller-visible memory effects. Does not verify the implementation.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppLiteralConstructor {
    pub function: String,
    pub header: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppLiteralMetadata {
    pub constructor: CppLiteralConstructor,
    pub declaration_file: String,
    pub record: String,
    pub record_type: String,
    pub literal: String,
    pub binding: CppLiteralMetadataBinding,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CppLiteralMetadataBinding {
    Value,
    ConstReference,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppLibraryMetadata {
    Consteval(CppConstevalMetadata),
    Literal(CppLiteralMetadata),
}

impl CppLibraryMetadata {
    pub(crate) fn declaration_file(&self) -> &str {
        match self {
            Self::Consteval(metadata) => &metadata.declaration_file,
            Self::Literal(metadata) => &metadata.declaration_file,
        }
    }

    fn validate(&self, contract: &CppLibraryAssertion) -> Result<(), String> {
        match self {
            Self::Consteval(metadata) => metadata.validate(),
            Self::Literal(metadata) => {
                if contract.kind
                    != CppLibraryAssertionKind::CheckedBooleanStatementWithLiteralMetadata
                    || contract.literal_constructor.as_ref() != Some(&metadata.constructor)
                    || !metadata
                        .record
                        .split("::")
                        .all(super::import::is_identifier)
                    || metadata.record.len() > 256
                    || metadata.constructor.function
                        != format!(
                            "{}::{}",
                            metadata.record,
                            metadata.record.rsplit("::").next().unwrap_or_default()
                        )
                    || !valid_metadata_file(&metadata.declaration_file)
                    || metadata.record_type.is_empty()
                    || metadata.record_type.len() > 1024
                    || !metadata.record_type.is_ascii()
                    || metadata.record_type.as_bytes().contains(&0)
                    || metadata.literal.len() > 4096
                    || !metadata.literal.is_ascii()
                    || metadata.literal.as_bytes().contains(&0)
                {
                    return Err("invalid C++ literal metadata contract or provenance".into());
                }
                Ok(())
            }
        }
    }
}

fn valid_metadata_file(file: &str) -> bool {
    Path::new(file).is_absolute() && file.len() <= 4096 && !file.as_bytes().contains(&0)
}

/// Forced compile-time metadata; no runtime call or nontrivial cleanup is erased.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppConstevalMetadata {
    pub function: String,
    pub declaration_file: String,
}

impl CppConstevalMetadata {
    pub(crate) fn validate(&self) -> Result<(), String> {
        if !self.function.split("::").all(super::import::is_identifier)
            || self.function.len() > 256
            || !valid_metadata_file(&self.declaration_file)
        {
            return Err("invalid C++ consteval metadata provenance".into());
        }
        Ok(())
    }
}

pub(super) fn validate_library_assertion_metadata(
    contract: &CppLibraryAssertion,
    metadata: &[CppLibraryMetadata],
    specialization: &Option<String>,
) -> Result<(), String> {
    contract.validate()?;
    if metadata.len() > 8
        || specialization
            .as_ref()
            .is_some_and(|name| name.len() > 512 || !super::import::is_identifier(name))
        || (contract.kind == CppLibraryAssertionKind::CheckedBooleanStatement
            && (!metadata.is_empty() || specialization.is_some()))
    {
        return Err(
            "C++ library assertion metadata does not match its declared contract kind".into(),
        );
    }
    for argument in metadata {
        argument.validate(contract)?;
    }
    Ok(())
}

impl CppLibraryAssertion {
    pub(crate) fn pins(&self) -> impl Iterator<Item = (&str, &str, &str)> {
        std::iter::once((
            self.function.as_str(),
            self.header.as_str(),
            self.sha256.as_str(),
        ))
        .chain(self.literal_constructor.iter().map(|pin| {
            (
                pin.function.as_str(),
                pin.header.as_str(),
                pin.sha256.as_str(),
            )
        }))
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        if (self.kind == CppLibraryAssertionKind::CheckedBooleanStatementWithLiteralMetadata)
            != self.literal_constructor.is_some()
        {
            return Err(
                "C++ literal metadata requires its own constructor contract and kind".into(),
            );
        }
        for (function, header, sha256) in self.pins() {
            if !function.split("::").all(super::import::is_identifier)
                || function.len() > 256
                || !valid_relative_source_path(header)
                || header.len() > 1024
                || header
                    .split('/')
                    .any(|part| part.is_empty() || part == "." || part == "..")
                || sha256.len() != 64
                || !sha256
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return Err("invalid C++ assumed library assertion or constructor contract".into());
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppPreprocessorFile {
    pub accessed_path: String,
    pub canonical_path: String,
}

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CppExceptionBehavior {
    #[default]
    NormalOnly,
    ScalarInt32,
}

impl CppExceptionBehavior {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::NormalOnly => "normal_only",
            Self::ScalarInt32 => "scalar_int32",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppRecord {
    pub declaration_id: String,
    pub name: String,
    pub size_bytes: u32,
    pub alignment_bytes: u32,
    pub fields: Vec<CppField>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<CppBase>,
    pub destructor: Option<CppFunctionReference>,
    pub span: CppSpan,
}

/// A distinct public, non-virtual base subobject, never a copied field list.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppBase {
    pub value_type: CppType,
    pub offset_bytes: u32,
    pub size_bytes: u32,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppField {
    pub declaration_id: String,
    pub name: String,
    pub value_type: CppType,
    pub offset_bytes: u32,
    pub size_bytes: u32,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppProfile {
    pub frontend: String,
    pub frontend_version: String,
    pub standard: String,
    pub target: String,
    pub exceptions: bool,
    pub rtti: bool,
    pub compilation_directory: String,
    pub compilation_file: String,
    pub compilation_command: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFunction {
    pub declaration_id: String,
    pub name: String,
    pub function_kind: CppFunctionKind,
    pub return_type: CppType,
    pub parameters: Vec<CppPlace>,
    pub declared_noexcept: bool,
    pub span: CppSpan,
    pub body: Vec<CppStatement>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppFunctionKind {
    Free,
    StaticMethod {
        record_declaration_id: String,
        record_name: String,
    },
    Constructor {
        record_declaration_id: String,
        record_name: String,
    },
    Destructor {
        record_declaration_id: String,
        record_name: String,
    },
    Method {
        record_declaration_id: String,
        record_name: String,
        is_const: bool,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppType {
    Void,
    Boolean {
        bits: u32,
        is_const: bool,
    },
    Integer {
        bits: u32,
        signed: bool,
        is_const: bool,
        source_aliases: Vec<CppTypeAlias>,
    },
    LvalueReference {
        pointee: Box<CppType>,
    },
    Pointer {
        pointee: Box<CppType>,
    },
    Record {
        declaration_id: String,
        name: String,
        is_const: bool,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppTypeAlias {
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppConstant {
    pub declaration_id: String,
    pub name: String,
    pub value_type: CppType,
    pub initializer: CppExpression,
    pub evaluated_value: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppConstantReference {
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppPlace {
    pub declaration_id: String,
    pub name: String,
    pub value_type: CppType,
    pub span: CppSpan,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CppBinaryOperator {
    Add,
    Subtract,
    Divide,
    Remainder,
    LessThan,
    GreaterThan,
    Equal,
    NotEqual,
    Multiply,
    LessEqual,
    GreaterEqual,
    LogicalAnd,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppExpression {
    IntegerLiteral {
        value: String,
        value_type: CppType,
        span: CppSpan,
    },
    CompilerConstant {
        value: String,
        value_type: CppType,
        span: CppSpan,
    },
    ConstantReference {
        constant: CppConstantReference,
        value_type: CppType,
        span: CppSpan,
    },
    Load {
        place: CppPlaceReference,
        value_type: CppType,
        span: CppSpan,
    },
    AddressOf {
        place: CppPlaceReference,
        value_type: CppType,
        span: CppSpan,
    },
    Dereference {
        pointer: Box<CppExpression>,
        value_type: CppType,
        span: CppSpan,
    },
    MemberLoad {
        object: CppPlaceReference,
        field: CppFieldReference,
        value_type: CppType,
        span: CppSpan,
    },
    IntegralCast {
        value: Box<CppExpression>,
        value_type: CppType,
        span: CppSpan,
    },
    Binary {
        operator: CppBinaryOperator,
        left: Box<CppExpression>,
        right: Box<CppExpression>,
        value_type: CppType,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppPlaceReference {
    /// Ordered field and nominal base edges from the complete root object.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub projections: Vec<CppProjection>,
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFunctionReference {
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFieldReference {
    pub record_declaration_id: String,
    pub declaration_id: String,
    pub name: String,
    pub span: CppSpan,
}

/// Preserve the original field-reference encoding; a base edge has a distinct
/// wrapper and identifies both the derived owner and the nominal base target.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum CppProjection {
    Field(CppFieldReference),
    Base { base: CppBaseReference },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppBaseReference {
    pub record_declaration_id: String,
    pub base_declaration_id: String,
    pub base_name: String,
    pub span: CppSpan,
}

impl CppProjection {
    fn span(&self) -> &CppSpan {
        match self {
            Self::Field(field) => &field.span,
            Self::Base { base } => &base.span,
        }
    }
    pub(super) fn as_ref(&self) -> ProjectionRef<'_> {
        self.into()
    }
}

#[derive(Clone, Copy)]
pub(super) enum ProjectionRef<'a> {
    Field(&'a CppFieldReference),
    Base(&'a CppBaseReference),
}
impl<'a> From<&'a CppProjection> for ProjectionRef<'a> {
    fn from(value: &'a CppProjection) -> Self {
        match value {
            CppProjection::Field(field) => Self::Field(field),
            CppProjection::Base { base } => Self::Base(base),
        }
    }
}
impl<'a> From<&'a CppFieldReference> for ProjectionRef<'a> {
    fn from(value: &'a CppFieldReference) -> Self {
        Self::Field(value)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppFieldInitializer {
    pub field: CppFieldReference,
    pub value: CppExpression,
    pub span: CppSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppCleanup {
    Destructor {
        object: CppPlaceReference,
        callee: CppFunctionReference,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppCallArgument {
    Value {
        value: CppExpression,
    },
    Reference {
        place: CppPlaceReference,
    },
    Call {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        value_type: CppType,
        span: CppSpan,
    },
}

/// A pure condition retains its existing expression encoding. A call is a
/// separate effectful operation, evaluated exactly once before either arm.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum CppCondition {
    Expression(CppExpression),
    Call { call: CppConditionCall },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppConditionCall {
    pub callee: CppFunctionReference,
    pub arguments: Vec<CppCallArgument>,
    pub value_type: CppType,
    pub span: CppSpan,
}

impl From<CppExpression> for CppCondition {
    fn from(value: CppExpression) -> Self {
        Self::Expression(value)
    }
}

impl CppCondition {
    pub(crate) fn value_type(&self) -> &CppType {
        match self {
            Self::Expression(value) => value.value_type(),
            Self::Call { call } => &call.value_type,
        }
    }

    fn constant_boolean(&self) -> Option<bool> {
        match self {
            Self::Expression(value) => value.constant_boolean(),
            Self::Call { .. } => None,
        }
    }

    fn validate(
        &self,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Expression(value) => value.validate(places, records, logical_source),
            Self::Call { call } => {
                require_bool(&call.value_type, false, "if condition call")?;
                validate_call(
                    &call.callee,
                    &call.arguments,
                    &call.span,
                    places,
                    records,
                    logical_source,
                )
            }
        }
    }

    fn validate_constant_references(
        &self,
        logical_source: &str,
        constants: &BTreeMap<String, &CppConstant>,
        referenced_constants: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        match self {
            Self::Expression(value) => {
                value.validate_constant_references(logical_source, constants, referenced_constants)
            }
            Self::Call { call } => {
                for argument in &call.arguments {
                    argument.validate_constant_references(
                        logical_source,
                        constants,
                        referenced_constants,
                    )?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppInitializer {
    Value {
        value: CppExpression,
    },
    Call {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        span: CppSpan,
    },
    Aggregate {
        fields: Vec<CppFieldInitializer>,
        span: CppSpan,
    },
    Constructor {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum CppStatement {
    Declare {
        local: CppPlace,
        initializer: CppInitializer,
        span: CppSpan,
    },
    Assign {
        target: CppPlaceReference,
        value: CppExpression,
        span: CppSpan,
    },
    Store {
        pointer: CppExpression,
        value: CppExpression,
        span: CppSpan,
    },
    MemberStore {
        object: CppPlaceReference,
        field: CppFieldReference,
        value: CppExpression,
        span: CppSpan,
    },
    Return {
        value: CppExpression,
        cleanups: Vec<CppCleanup>,
        span: CppSpan,
    },
    ReturnCall {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        value_type: CppType,
        cleanups: Vec<CppCleanup>,
        span: CppSpan,
    },
    Throw {
        value: CppExpression,
        span: CppSpan,
    },
    Assume {
        condition: CppExpression,
        span: CppSpan,
    },
    LibraryAssert {
        condition: CppExpression,
        contract: CppLibraryAssertion,
        #[serde(default)]
        metadata: Vec<CppLibraryMetadata>,
        specialization: Option<String>,
        span: CppSpan,
    },
    TryCatchInt32 {
        try_body: Vec<CppStatement>,
        binding: CppPlace,
        handler: Vec<CppStatement>,
        span: CppSpan,
    },
    Scope {
        body: Vec<CppStatement>,
        cleanups: Vec<CppCleanup>,
        span: CppSpan,
    },
    If {
        condition: CppCondition,
        then_branch: Vec<CppStatement>,
        else_branch: Vec<CppStatement>,
        span: CppSpan,
    },
    Call {
        callee: CppFunctionReference,
        arguments: Vec<CppCallArgument>,
        span: CppSpan,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CppSpan {
    pub file: String,
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

impl CppExport {
    pub(crate) fn validate(
        &self,
        logical_source: &str,
        function: &str,
        expected_exceptions: bool,
        expected_exception_behavior: CppExceptionBehavior,
        expected_rtti: bool,
        expected_dependencies: &[String],
    ) -> Result<(), String> {
        super::budget::check_inventories(self)?;
        if self.schema != EXPORT_SCHEMA {
            return Err(format!(
                "unsupported C++ exporter schema {}; expected {EXPORT_SCHEMA}",
                self.schema
            ));
        }
        if self.language != LANGUAGE
            || self.profile.frontend != "clang"
            || self.profile.standard != STANDARD
            || self.profile.target != TARGET
            || self.profile.exceptions != expected_exceptions
            || self.profile.rtti != expected_rtti
        {
            return Err(format!(
                "C++ export profile must match the configured Clang {STANDARD} profile for {TARGET}"
            ));
        }
        if self.exception_behavior != expected_exception_behavior
            || (matches!(self.exception_behavior, CppExceptionBehavior::ScalarInt32)
                && !self.profile.exceptions)
        {
            return Err(
                "C++ exception behavior differs from the configured compiler profile".into(),
            );
        }
        if !self.profile.frontend_version.contains(CLANG_VERSION) {
            return Err(format!(
                "C++ export used `{}`; expected Clang {CLANG_VERSION}",
                self.profile.frontend_version
            ));
        }
        if self.profile.compilation_directory.is_empty()
            || self.profile.compilation_directory.as_bytes().contains(&0)
            || self.profile.compilation_file.is_empty()
            || self.profile.compilation_file.as_bytes().contains(&0)
            || self.profile.compilation_command.is_empty()
            || self
                .profile
                .compilation_command
                .iter()
                .any(|argument| argument.is_empty() || argument.as_bytes().contains(&0))
        {
            return Err("C++ export is missing its selected compilation command identity".into());
        }
        let driver = Path::new(&self.profile.compilation_command[0])
            .file_name()
            .and_then(|name| name.to_str());
        if !matches!(driver, Some("clang++" | "clang++-19")) {
            return Err("C++ export compilation command does not use pinned Clang".into());
        }
        if self.logical_source != logical_source {
            return Err(format!(
                "C++ export names logical source `{}` instead of `{logical_source}`",
                self.logical_source
            ));
        }
        if self.dependencies != expected_dependencies {
            return Err(format!(
                "C++ export dependencies {:?} differ from configured dependencies {:?}",
                self.dependencies, expected_dependencies
            ));
        }
        super::budget::limit(
            "preprocessor files",
            self.preprocessor_files.len(),
            MAX_PREPROCESSOR_FILES,
        )?;
        if self.preprocessor_files.is_empty() {
            return Err("C++ export has an invalid preprocessor file inventory size".into());
        }
        let mut previous_file: Option<&str> = None;
        for file in &self.preprocessor_files {
            if !Path::new(&file.accessed_path).is_absolute()
                || !Path::new(&file.canonical_path).is_absolute()
                || file.accessed_path.as_bytes().contains(&0)
                || file.canonical_path.as_bytes().contains(&0)
                || previous_file.is_some_and(|previous| previous >= file.accessed_path.as_str())
            {
                return Err(
                    "C++ export preprocessor files must be sorted unique absolute paths".into(),
                );
            }
            previous_file = Some(&file.accessed_path);
        }
        let mut declaration_sources = BTreeSet::from([logical_source.to_string()]);
        let mut previous_dependency: Option<&str> = None;
        for dependency in &self.dependencies {
            if !valid_relative_source_path(dependency)
                || previous_dependency.is_some_and(|previous| previous >= dependency.as_str())
            {
                return Err("C++ export dependencies must be unique sorted relative paths".into());
            }
            previous_dependency = Some(dependency);
            declaration_sources.insert(dependency.clone());
        }
        let expected_name = match &self.function.function_kind {
            CppFunctionKind::Method { record_name, .. }
            | CppFunctionKind::StaticMethod { record_name, .. } => {
                let prefix = format!("{record_name}::");
                let member = function.strip_prefix(&prefix).ok_or_else(|| {
                    "selected C++ method requires a qualified Class::method selector".to_string()
                })?;
                format!(
                    "{record_name}_{}",
                    if member == "operator+=" {
                        "operator_add_assign"
                    } else if member == "operator-=" {
                        "operator_subtract_assign"
                    } else {
                        member
                    }
                )
            }
            _ => function.replace("::", "_"),
        };
        if self.function.name != expected_name {
            return Err(format!(
                "C++ export resolved `{}` instead of selected function `{function}`",
                self.function.name
            ));
        }
        if !matches!(
            self.function.function_kind,
            CppFunctionKind::Free
                | CppFunctionKind::StaticMethod { .. }
                | CppFunctionKind::Method { .. }
        ) {
            return Err("the selected C++ declaration must be a free function".into());
        }

        if (self.profile.rtti
            || (self.profile.exceptions
                && matches!(self.exception_behavior, CppExceptionBehavior::NormalOnly)))
            && self
                .records
                .iter()
                .any(|record| record.destructor.is_some())
        {
            return Err(
                "exception- or RTTI-enabled normal-only C++ records require trivial destruction"
                    .into(),
            );
        }
        let records =
            validate_record_inventory(&self.records, logical_source, &declaration_sources)?;

        let CheckedConstants {
            declarations: constants,
            dependencies: constant_dependencies,
        } = validate_constant_inventory(&self.constants, logical_source, &declaration_sources)?;

        self.function.span.validate(logical_source)?;
        let mut functions = BTreeMap::new();
        let mut referenced_constants = BTreeSet::new();
        for source in std::iter::once(&self.function).chain(&self.reachable_functions) {
            source.span.validate_in(&declaration_sources)?;
            if source.span.file != logical_source
                && matches!(
                    source.function_kind,
                    CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. }
                )
            {
                return Err("C++ header constructors and destructors remain outside the executable graph profile".into());
            }
            source.validate(
                &source.span.file,
                &declaration_sources,
                &records,
                self.profile.exceptions,
                self.exception_behavior,
            )?;
            source.validate_constant_references(
                &source.span.file,
                &constants,
                &mut referenced_constants,
            )?;
            if functions
                .insert(source.declaration_id.clone(), source)
                .is_some()
            {
                return Err(format!(
                    "duplicate C++ function declaration identity `{}`",
                    source.declaration_id
                ));
            }
        }
        let mut reachable_constants = referenced_constants.clone();
        let mut pending = referenced_constants.into_iter().collect::<Vec<_>>();
        while let Some(declaration_id) = pending.pop() {
            if let Some(Some(dependency)) = constant_dependencies.get(&declaration_id)
                && reachable_constants.insert(dependency.clone())
            {
                pending.push(dependency.clone());
            }
        }
        if reachable_constants != constants.keys().cloned().collect() {
            return Err(
                "C++ export contains a constant outside the selected function graph".into(),
            );
        }

        for record in &self.records {
            let Some(destructor) = &record.destructor else {
                continue;
            };
            let target = functions.get(&destructor.declaration_id).ok_or_else(|| {
                format!(
                    "C++ record `{}` refers to missing destructor definition `{}`",
                    record.name, destructor.declaration_id
                )
            })?;
            if target.name != destructor.name {
                return Err(format!(
                    "C++ destructor declaration `{}` is named `{}`, not `{}`",
                    destructor.declaration_id, target.name, destructor.name
                ));
            }
            if !matches!(
                &target.function_kind,
                CppFunctionKind::Destructor {
                    record_declaration_id,
                    record_name,
                } if record_declaration_id == &record.declaration_id
                    && record_name == &record.name
            ) {
                return Err(format!(
                    "C++ record `{}` has a mismatched destructor declaration",
                    record.name
                ));
            }
        }

        let mut visiting = Vec::new();
        let mut visited = BTreeMap::new();
        validate_reachable_calls(
            &self.function.declaration_id,
            &functions,
            &records,
            &mut visiting,
            &mut visited,
        )?;
        validate_reachable_records(&functions, &records)?;
        if visited.len() != functions.len() {
            return Err(
                "C++ export contains a function outside the selected function's reachable graph"
                    .into(),
            );
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub(super) struct RecordIndex<'a> {
    declarations: BTreeMap<String, &'a CppRecord>,
    fields: BTreeMap<(&'a str, &'a str), &'a CppField>,
}

impl<'a> RecordIndex<'a> {
    pub(super) fn new(declarations: BTreeMap<String, &'a CppRecord>) -> Self {
        let mut fields = BTreeMap::new();
        for record in declarations.values() {
            for field in &record.fields {
                crate::instrumentation::record_deterministic_work(1);
                fields.insert(
                    (
                        record.declaration_id.as_str(),
                        field.declaration_id.as_str(),
                    ),
                    field,
                );
            }
        }
        Self {
            declarations,
            fields,
        }
    }

    pub(super) fn resolve_path<'b, 's, P: Into<ProjectionRef<'b>>>(
        &'s self,
        root_type: &'s CppType,
        path: impl IntoIterator<Item = P>,
    ) -> Result<(&'s CppType, u32), String> {
        let mut value_type = match root_type {
            CppType::LvalueReference { pointee } => pointee.as_ref(),
            value => value,
        };
        let mut offset = 0u32;
        for reference in path {
            crate::instrumentation::record_deterministic_work(1);
            let CppType::Record {
                declaration_id,
                name,
                ..
            } = value_type
            else {
                return Err("C++ field projection requires a record object".into());
            };
            validate_record_reference(self, declaration_id, name)?;
            let reference = match reference.into() {
                ProjectionRef::Field(field) => field,
                ProjectionRef::Base(base) => {
                    if base.record_declaration_id != *declaration_id {
                        return Err(
                            "C++ base projection belongs to the wrong derived record".into()
                        );
                    }
                    let owner = self[declaration_id]
                        .base
                        .as_ref()
                        .ok_or("C++ base projection requires a declared base subobject")?;
                    let CppType::Record {
                        declaration_id: target_id,
                        name: target_name,
                        ..
                    } = &owner.value_type
                    else {
                        return Err("C++ base projection requires a nominal record base".into());
                    };
                    if &base.base_declaration_id != target_id || &base.base_name != target_name {
                        return Err("C++ base projection has the wrong nominal base target".into());
                    }
                    offset = offset
                        .checked_add(owner.offset_bytes)
                        .ok_or("C++ base projection offset overflows")?;
                    value_type = &owner.value_type;
                    continue;
                }
            };
            if reference.record_declaration_id != *declaration_id {
                return Err(format!(
                    "C++ field `{}` belongs to the wrong record declaration",
                    reference.name
                ));
            }
            let field = self
                .fields
                .get(&(declaration_id.as_str(), reference.declaration_id.as_str()))
                .ok_or_else(|| {
                    format!(
                        "C++ member access refers to unknown field declaration `{}`",
                        reference.declaration_id
                    )
                })?;
            if field.name != reference.name {
                return Err(format!(
                    "C++ field declaration `{}` is named `{}`, not `{}`",
                    reference.declaration_id, field.name, reference.name
                ));
            }
            offset = offset
                .checked_add(field.offset_bytes)
                .ok_or("C++ field projection offset overflows")?;
            value_type = &field.value_type;
        }
        Ok((value_type, offset))
    }
}

impl<'a> std::ops::Deref for RecordIndex<'a> {
    type Target = BTreeMap<String, &'a CppRecord>;
    fn deref(&self) -> &Self::Target {
        &self.declarations
    }
}

fn validate_record_inventory<'a>(
    inventory: &'a [CppRecord],
    logical_source: &str,
    declaration_sources: &BTreeSet<String>,
) -> Result<RecordIndex<'a>, String> {
    let mut records = BTreeMap::new();
    let mut record_names = BTreeSet::new();
    let mut field_identities = BTreeSet::new();
    for record in inventory {
        crate::instrumentation::record_deterministic_work(1);
        if !record_names.insert(record.name.as_str()) {
            return Err("C++ record profile does not support same-named record layouts".into());
        }
        for field in &record.fields {
            crate::instrumentation::record_deterministic_work(1);
            if !field_identities.insert(field.declaration_id.as_str()) {
                return Err(format!(
                    "duplicate C++ field declaration identity `{}`",
                    field.declaration_id
                ));
            }
            field.value_type.validate_aliases_in(declaration_sources)?;
        }
        if records
            .insert(record.declaration_id.clone(), record)
            .is_some()
        {
            return Err(format!(
                "duplicate C++ record declaration identity `{}`",
                record.declaration_id
            ));
        }
    }
    let records = RecordIndex::new(records);
    for record in inventory {
        record.validate(logical_source, declaration_sources, &records)?;
    }
    record_layout_order(&records)?;
    Ok(records)
}

// Resolve embedded declarations once, without recursively expanding shared layouts.
// The returned order places every child before its owners.
pub(super) fn record_layout_order<'a>(
    records: &BTreeMap<String, &'a CppRecord>,
) -> Result<Vec<&'a CppRecord>, String> {
    let mut remaining = BTreeMap::new();
    let mut owners: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut ready = Vec::new();
    for (id, record) in records {
        crate::instrumentation::record_deterministic_work(1);
        let mut count = 0;
        for value_type in record
            .fields
            .iter()
            .map(|field| &field.value_type)
            .chain(record.base.iter().map(|base| &base.value_type))
        {
            crate::instrumentation::record_deterministic_work(1);
            if let CppType::Record {
                declaration_id,
                name,
                is_const,
            } = value_type
            {
                let child = validate_record_reference(records, declaration_id, name)?;
                if *is_const || child.destructor.is_some() {
                    return Err("embedded C++ record fields require mutable, trivially destructible records".into());
                }
                count += 1;
                owners.entry(declaration_id).or_default().push(id);
            }
        }
        remaining.insert(id.as_str(), count);
        if count == 0 {
            ready.push(id.as_str());
        }
    }
    let mut ordered = Vec::with_capacity(records.len());
    while let Some(id) = ready.pop() {
        ordered.push(records[id]);
        if let Some(parents) = owners.get(id) {
            for parent in parents {
                crate::instrumentation::record_deterministic_work(1);
                let count = remaining.get_mut(parent).expect("indexed record owner");
                *count -= 1;
                if *count == 0 {
                    ready.push(parent);
                }
            }
        }
    }
    if ordered.len() != records.len() {
        return Err("C++ embedded record declarations contain a by-value cycle".into());
    }
    Ok(ordered)
}

// Every layout must belong to a typed declaration in the selected graph.
// This structural check is separate from the supported field-type policy.
fn validate_reachable_records(
    functions: &BTreeMap<String, &CppFunction>,
    records: &RecordIndex<'_>,
) -> Result<(), String> {
    let mut referenced = BTreeSet::new();
    fn reference<'a>(value_type: &'a CppType, referenced: &mut BTreeSet<&'a str>) {
        match value_type {
            CppType::Record { declaration_id, .. } => {
                referenced.insert(declaration_id);
            }
            CppType::LvalueReference { pointee } | CppType::Pointer { pointee } => {
                reference(pointee, referenced)
            }
            _ => {}
        }
    }
    for function in functions.values() {
        for parameter in &function.parameters {
            crate::instrumentation::record_deterministic_work(1);
            reference(&parameter.value_type, &mut referenced);
        }
        match &function.function_kind {
            CppFunctionKind::Method {
                record_declaration_id,
                ..
            }
            | CppFunctionKind::Constructor {
                record_declaration_id,
                ..
            }
            | CppFunctionKind::Destructor {
                record_declaration_id,
                ..
            } => {
                referenced.insert(record_declaration_id.as_str());
            }
            _ => {}
        }
        let mut pending = vec![function.body.as_slice()];
        while let Some(body) = pending.pop() {
            for statement in body {
                crate::instrumentation::record_deterministic_work(1);
                match statement {
                    CppStatement::Declare { local, .. } => {
                        reference(&local.value_type, &mut referenced)
                    }
                    CppStatement::Scope { body, .. } => pending.push(body),
                    CppStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        pending.push(then_branch);
                        pending.push(else_branch);
                    }
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
    }
    let mut pending: Vec<_> = referenced.iter().copied().collect();
    while let Some(id) = pending.pop() {
        let record = records
            .get(id)
            .ok_or_else(|| format!("unknown C++ record declaration `{id}`"))?;
        for value_type in record
            .fields
            .iter()
            .map(|field| &field.value_type)
            .chain(record.base.iter().map(|base| &base.value_type))
        {
            crate::instrumentation::record_deterministic_work(1);
            if let CppType::Record { declaration_id, .. } = value_type
                && referenced.insert(declaration_id.as_str())
            {
                pending.push(declaration_id.as_str());
            }
        }
    }
    if referenced != records.keys().map(String::as_str).collect() {
        return Err("C++ export contains a record outside the selected function graph".into());
    }
    Ok(())
}

impl CppRecord {
    fn require_flat_local_layout(&self) -> Result<(), String> {
        if self.base.is_some() {
            return Err("automatic C++ objects with base subobjects remain unsupported".into());
        }
        if self
            .fields
            .iter()
            .any(|field| matches!(field.value_type, CppType::Record { .. }))
        {
            return Err(
                "automatic C++ objects with embedded record fields remain unsupported".into(),
            );
        }
        Ok(())
    }

    fn validate(
        &self,
        logical_source: &str,
        sources: &BTreeSet<String>,
        records: &RecordIndex<'_>,
    ) -> Result<(), String> {
        if self.declaration_id.is_empty() || self.name.is_empty() {
            return Err("C++ record is missing declaration identity".into());
        }
        self.span.validate_in(sources)?;
        if let Some(destructor) = &self.destructor {
            if destructor.declaration_id.is_empty() || destructor.name.is_empty() {
                return Err(format!(
                    "C++ record `{}` has an unidentified destructor",
                    self.name
                ));
            }
            destructor.span.validate(logical_source)?;
        }
        if (self.fields.is_empty() && self.base.is_none())
            || self.alignment_bytes == 0
            || !self.alignment_bytes.is_power_of_two()
            || self.size_bytes == 0
            || !self.size_bytes.is_multiple_of(self.alignment_bytes)
        {
            return Err(format!("C++ record `{}` has an invalid layout", self.name));
        }
        if let Some(base) = &self.base {
            base.span.validate_in(sources)?;
            let CppType::Record {
                declaration_id,
                name,
                is_const: false,
            } = &base.value_type
            else {
                return Err("C++ base subobject requires a mutable nominal record type".into());
            };
            let child = validate_record_reference(records, declaration_id, name)?;
            // This first profile models data-free tagged wrappers: one complete
            // base, no own fields, overlap, tail-padding reuse or base cleanup.
            if base.span.file != self.span.file
                || !self.fields.is_empty()
                || self.destructor.is_some()
                || child.destructor.is_some()
                || base.offset_bytes != 0
                || base.size_bytes != child.size_bytes
                || self.size_bytes != child.size_bytes
                || self.alignment_bytes != child.alignment_bytes
            {
                return Err(format!(
                    "C++ record `{}` has an invalid single-base layout",
                    self.name
                ));
            }
        }
        let mut identities = std::collections::BTreeSet::new();
        let mut names = std::collections::BTreeSet::new();
        let mut previous_end = 0u32;
        for field in &self.fields {
            field.span.validate_in(sources)?;
            if field.span.file != self.span.file {
                return Err(format!(
                    "C++ record `{}` field declaration has a different source",
                    self.name
                ));
            }
            if field.declaration_id.is_empty() || field.name.is_empty() {
                return Err(format!(
                    "C++ record `{}` has an unidentified field",
                    self.name
                ));
            }
            if !identities.insert(field.declaration_id.clone()) || !names.insert(field.name.clone())
            {
                return Err(format!("C++ record `{}` has a duplicate field", self.name));
            }
            let (size, alignment) = match &field.value_type {
                CppType::Integer { .. } => {
                    if require_int32(&field.value_type, false, "record field").is_ok() {
                        (4, 4)
                    } else {
                        require_signed_int64(&field.value_type, false, "record field")?;
                        (8, 8)
                    }
                }
                CppType::Pointer { pointee } => {
                    require_int32(pointee, false, "record pointer field")?;
                    (8, 8)
                }
                CppType::Record {
                    declaration_id,
                    name,
                    is_const: false,
                } => {
                    let child = validate_record_reference(records, declaration_id, name)?;
                    (child.size_bytes, child.alignment_bytes)
                }
                _ => {
                    return Err(format!(
                        "C++ record field `{}.{}` is outside the scalar/pointer/embedded-record slice",
                        self.name, field.name
                    ));
                }
            };
            let end = field
                .offset_bytes
                .checked_add(field.size_bytes)
                .ok_or_else(|| format!("C++ record `{}` field layout overflows", self.name))?;
            if field.size_bytes != size
                || alignment == 0
                || self.alignment_bytes < alignment
                || field.offset_bytes % alignment != 0
                || field.offset_bytes < previous_end
                || end > self.size_bytes
            {
                return Err(format!(
                    "C++ record field `{}.{}` has an invalid layout",
                    self.name, field.name
                ));
            }
            previous_end = end;
        }
        Ok(())
    }
}

impl CppFunction {
    // Executable spans are local to this body; alias origins are checked once
    // by metadata validity against the shared locked declaration inventory.
    fn validate(
        &self,
        logical_source: &str,
        alias_sources: &BTreeSet<String>,
        records: &RecordIndex<'_>,
        exceptions_enabled: bool,
        exception_behavior: CppExceptionBehavior,
    ) -> Result<(), String> {
        super::budget::check_function(self)?;
        super::validity::check_function(self, logical_source, alias_sources)?;
        match &self.function_kind {
            CppFunctionKind::Free
            | CppFunctionKind::StaticMethod { .. }
            | CppFunctionKind::Method { .. } => {
                if self.return_type != CppType::Void
                    && require_scalar_integer(&self.return_type, "function return type").is_err()
                {
                    require_bool(&self.return_type, false, "function return type")?;
                }
            }
            CppFunctionKind::Constructor {
                record_declaration_id,
                record_name,
            }
            | CppFunctionKind::Destructor {
                record_declaration_id,
                record_name,
            } => {
                if self.return_type != CppType::Void {
                    return Err(format!(
                        "C++ object operation `{}` must have void artifact return type",
                        self.name
                    ));
                }
                validate_record_reference(records, record_declaration_id, record_name)?;
            }
        }
        if let CppFunctionKind::Method {
            record_declaration_id,
            record_name,
            ..
        } = &self.function_kind
        {
            validate_record_reference(records, record_declaration_id, record_name)?;
        }
        if let CppFunctionKind::StaticMethod {
            record_declaration_id,
            record_name,
        } = &self.function_kind
        {
            // A static declaration has class identity, but no object layout or receiver.
            if record_declaration_id.is_empty()
                || record_name.is_empty()
                || !self.name.starts_with(&format!("{record_name}_"))
            {
                return Err("C++ static helper has a mismatched class identity".into());
            }
            if require_scalar_integer(&self.return_type, "static helper return type").is_err() {
                require_bool(&self.return_type, false, "static helper return type")?;
            }
            for parameter in &self.parameters {
                if require_scalar_integer(&parameter.value_type, "static helper parameter").is_err()
                {
                    require_bool(&parameter.value_type, false, "static helper parameter")?;
                }
            }
        }
        if !self.declared_noexcept
            && (!exceptions_enabled
                || matches!(
                    self.function_kind,
                    CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. }
                ))
        {
            return Err(format!(
                "C++ function `{}` must declare noexcept outside the exception-enabled object-free profile",
                self.name
            ));
        }
        if matches!(exception_behavior, CppExceptionBehavior::ScalarInt32)
            && self.declared_noexcept
            && matches!(
                self.function_kind,
                CppFunctionKind::Free
                    | CppFunctionKind::StaticMethod { .. }
                    | CppFunctionKind::Method { .. }
            )
        {
            return Err(format!(
                "C++ function `{}` declares noexcept, whose termination behavior is outside the scalar int32 exception profile",
                self.name
            ));
        }
        let mut places = ValidationPlaces::new();
        for parameter in &self.parameters {
            match &parameter.value_type {
                CppType::Boolean { .. } => {
                    require_bool(&parameter.value_type, false, "by-value parameter")?;
                }
                CppType::Integer { .. } => {
                    require_scalar_integer(&parameter.value_type, "by-value parameter")?;
                }
                CppType::LvalueReference { pointee } => {
                    if let CppType::Record {
                        declaration_id,
                        name,
                        ..
                    } = pointee.as_ref()
                    {
                        validate_record_reference(records, declaration_id, name)?;
                    } else {
                        if require_int32(pointee, true, "reference pointee").is_err() {
                            require_const_signed_int64(pointee, "reference pointee")?;
                        }
                    }
                }
                CppType::Pointer { pointee } => {
                    require_int32(pointee, false, "pointer pointee")?;
                }
                _ => {
                    return Err(
                        "the supported C++ parameters are by-value `bool`, `int&`, `const int&`, `int*`, and one simple record reference"
                            .into(),
                    );
                }
            }
            if places
                .insert(
                    parameter.declaration_id.clone(),
                    (parameter.name.clone(), parameter.value_type.clone()),
                )
                .is_err()
            {
                return Err(format!(
                    "duplicate C++ parameter declaration identity `{}`",
                    parameter.declaration_id
                ));
            }
            if !places.insert_name(parameter.name.clone()) {
                return Err(format!("duplicate C++ parameter name `{}`", parameter.name));
            }
        }
        if let CppFunctionKind::Method {
            record_declaration_id,
            record_name,
            is_const,
        } = &self.function_kind
        {
            let Some(receiver) = self.parameters.first() else {
                return Err("C++ method is missing its receiver".into());
            };
            if receiver.name != "self"
                || !matches!(&receiver.value_type,
                CppType::LvalueReference { pointee } if matches!(pointee.as_ref(),
                    CppType::Record { declaration_id, name, is_const: actual_const }
                    if declaration_id == record_declaration_id && name == record_name && actual_const == is_const))
            {
                return Err(
                    "C++ method has a mismatched receiver identity or const qualification".into(),
                );
            }
        }
        if let CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        }
        | CppFunctionKind::Destructor {
            record_declaration_id,
            record_name,
        } = &self.function_kind
        {
            let Some(self_parameter) = self.parameters.first() else {
                return Err(format!(
                    "C++ object operation `{}` is missing its explicit object parameter",
                    self.name
                ));
            };
            if self_parameter.name != "self"
                || !matches!(
                    &self_parameter.value_type,
                    CppType::LvalueReference { pointee }
                        if matches!(
                            pointee.as_ref(),
                            CppType::Record { declaration_id, name, is_const: false }
                                if declaration_id == record_declaration_id && name == record_name
                        )
                )
            {
                return Err(format!(
                    "C++ object operation `{}` has an invalid explicit object parameter",
                    self.name
                ));
            }
            if matches!(self.function_kind, CppFunctionKind::Destructor { .. })
                && self.parameters.len() != 1
            {
                return Err(format!(
                    "C++ destructor `{}` cannot have explicit parameters",
                    self.name
                ));
            }
        }
        if let CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        } = &self.function_kind
        {
            let self_parameter = &self.parameters[0];
            let record = validate_record_reference(records, record_declaration_id, record_name)?;
            if record.base.is_some() {
                return Err("C++ constructors with base subobjects remain unsupported".into());
            }
            if self.body.len() < record.fields.len() {
                return Err(format!(
                    "C++ constructor `{}` does not initialize every field",
                    self.name
                ));
            }
            for (statement, expected_field) in self.body.iter().zip(&record.fields) {
                let CppStatement::MemberStore {
                    object,
                    field,
                    value,
                    ..
                } = statement
                else {
                    return Err(format!(
                        "C++ constructor `{}` must begin with member initialization in declaration order",
                        self.name
                    ));
                };
                if object.declaration_id != self_parameter.declaration_id
                    || object.name != self_parameter.name
                    || field.record_declaration_id != *record_declaration_id
                    || field.declaration_id != expected_field.declaration_id
                    || field.name != expected_field.name
                    || value.references_place(&self_parameter.declaration_id)
                {
                    return Err(format!(
                        "C++ constructor `{}` has an invalid initializer for field `{}`",
                        self.name, expected_field.name
                    ));
                }
            }
        }
        if self.body.is_empty() {
            return Err("supported C++ function has no executable statements".into());
        }
        validate_return_types(&self.body, &self.return_type)?;
        if exceptions_enabled
            && matches!(exception_behavior, CppExceptionBehavior::NormalOnly)
            && sequence_constructs_record(&self.body)
        {
            return Err("exception-enabled normal-only C++ supports borrowed records only".into());
        }
        if matches!(exception_behavior, CppExceptionBehavior::NormalOnly)
            && sequence_contains_throw(&self.body)
        {
            return Err("throw expressions are outside the normal-only C++ profile".into());
        }
        if matches!(exception_behavior, CppExceptionBehavior::ScalarInt32)
            && !matches!(
                self.function_kind,
                CppFunctionKind::Free | CppFunctionKind::StaticMethod { .. }
            )
        {
            let mut calls = Vec::new();
            collect_calls(&self.body, &mut calls);
            if sequence_contains_throw(&self.body) || !calls.is_empty() {
                return Err(format!(
                    "noexcept C++ object operation `{}` may not throw or call another function in the scalar int32 exception profile",
                    self.name
                ));
            }
        }
        let mut aggregate_locals = 0;
        let mut destructible_locals = 0usize;
        let mut nested_scopes = 0;
        let mut nested_scope_outer_cleanup_counts = Vec::new();
        let mut has_conditional_cleanup_scope = false;
        let mut has_exception_cleanup_scope = false;
        for statement in &self.body {
            if let CppStatement::Declare {
                local,
                initializer,
                span,
            } = statement
            {
                span.validate(logical_source)?;
                local.span.validate(logical_source)?;
                if local.declaration_id.is_empty() || local.name.is_empty() {
                    return Err("C++ local is missing declaration identity".into());
                }
                match &local.value_type {
                    CppType::Integer { .. } => {
                        require_scalar_integer(&local.value_type, "automatic local")?;
                    }
                    CppType::Record {
                        declaration_id,
                        name,
                        is_const: false,
                    } => {
                        if has_conditional_cleanup_scope {
                            return Err(format!(
                                "C++ function `{}` cannot combine conditional construction with an outer aggregate object",
                                self.name
                            ));
                        }
                        let record = validate_record_reference(records, declaration_id, name)?;
                        record.require_flat_local_layout()?;
                        aggregate_locals += 1;
                        if record.destructor.is_some() {
                            if !matches!(initializer, CppInitializer::Constructor { .. }) {
                                return Err(format!(
                                    "C++ local `{}` with nontrivial destruction requires direct constructor initialization",
                                    local.name
                                ));
                            }
                            destructible_locals += 1;
                        }
                    }
                    _ => {
                        return Err(
                            "the supported automatic C++ local must be mutable `int` or one simple aggregate object"
                                .into(),
                        );
                    }
                }
                initializer.validate_for_local(
                    &local.value_type,
                    &places,
                    records,
                    logical_source,
                )?;
                if places
                    .insert(
                        local.declaration_id.clone(),
                        (local.name.clone(), local.value_type.clone()),
                    )
                    .is_err()
                {
                    return Err(format!(
                        "duplicate C++ local declaration identity `{}`",
                        local.declaration_id
                    ));
                }
                if !places.insert_name(local.name.clone()) {
                    return Err(format!(
                        "C++ local `{}` shadows another supported place",
                        local.name
                    ));
                }
            } else if let CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                span,
            } = statement
            {
                if !matches!(exception_behavior, CppExceptionBehavior::ScalarInt32)
                    || !matches!(
                        self.function_kind,
                        CppFunctionKind::Free | CppFunctionKind::StaticMethod { .. }
                    )
                    || destructible_locals != 0
                {
                    return Err(
                        "int32 try/catch requires the scalar exception profile without outer destructible locals".into(),
                    );
                }
                span.validate(logical_source)?;
                binding.span.validate(logical_source)?;
                if binding.declaration_id.is_empty() || binding.name.is_empty() {
                    return Err("C++ catch binding is missing declaration identity".into());
                }
                require_int32(&binding.value_type, false, "catch binding")?;
                binding.value_type.validate_aliases_in(alias_sources)?;
                if places.contains_key(&binding.declaration_id)
                    || places.contains_name(&binding.name)
                {
                    return Err(format!(
                        "C++ catch binding `{}` shadows another supported place",
                        binding.name
                    ));
                }
                if let [
                    CppStatement::Scope {
                        body,
                        cleanups,
                        span,
                    },
                ] = try_body.as_slice()
                {
                    if nested_scopes != 0 || has_exception_cleanup_scope {
                        return Err(format!(
                            "C++ function `{}` may unwind exactly one guard in a try region",
                            self.name
                        ));
                    }
                    if sequence_contains_return(body) {
                        return Err(
                            "the first C++ unwind slice does not support return from a guarded try region".into(),
                        );
                    }
                    if !matches!(body.first(), Some(CppStatement::Declare { .. })) {
                        return Err(
                            "the first C++ unwind slice requires guard construction first in the try region".into(),
                        );
                    }
                    validate_nested_scope(
                        body,
                        cleanups,
                        span,
                        &places,
                        records,
                        logical_source,
                        &self.name,
                    )?;
                    has_exception_cleanup_scope = true;
                } else {
                    for member in try_body {
                        member.validate(&places, records, logical_source)?;
                    }
                }
                let mut handler_places = places.child();
                debug_assert!(!handler_places.contains_name(&binding.name));
                handler_places.insert_name(binding.name.clone());
                let inserted = handler_places.insert(
                    binding.declaration_id.clone(),
                    (binding.name.clone(), binding.value_type.clone()),
                );
                debug_assert!(inserted.is_ok());
                for member in handler {
                    member.validate(&handler_places, records, logical_source)?;
                }
            } else if let CppStatement::Scope {
                body,
                cleanups,
                span,
            } = statement
            {
                if !matches!(self.function_kind, CppFunctionKind::Free) {
                    return Err(
                        "nested C++ scopes are supported only in a free-function body".into(),
                    );
                }
                if has_conditional_cleanup_scope {
                    return Err(format!(
                        "C++ function `{}` cannot combine conditional construction with another cleanup scope",
                        self.name
                    ));
                }
                nested_scopes += 1;
                nested_scope_outer_cleanup_counts.push(destructible_locals);
                validate_nested_scope(
                    body,
                    cleanups,
                    span,
                    &places,
                    records,
                    logical_source,
                    &self.name,
                )?;
            } else if let CppStatement::If {
                condition,
                then_branch,
                else_branch,
                span,
            } = statement
                && matches!(then_branch.as_slice(), [CppStatement::TryCatchInt32 { .. }])
            {
                let [
                    CppStatement::TryCatchInt32 {
                        try_body,
                        binding,
                        handler,
                        span: try_span,
                    },
                ] = then_branch.as_slice()
                else {
                    unreachable!("checked above")
                };
                let [
                    CppStatement::Scope {
                        body,
                        cleanups,
                        span: scope_span,
                    },
                ] = try_body.as_slice()
                else {
                    return Err("conditional guarded try requires one cleanup scope".into());
                };
                if !matches!(exception_behavior, CppExceptionBehavior::ScalarInt32)
                    || !matches!(
                        self.function_kind,
                        CppFunctionKind::Free | CppFunctionKind::StaticMethod { .. }
                    )
                    || !else_branch.is_empty()
                    || nested_scopes != 0
                    || has_conditional_cleanup_scope
                    || has_exception_cleanup_scope
                    || aggregate_locals != 0
                    || destructible_locals != 0
                    || !matches!(
                        handler.as_slice(),
                        [CppStatement::Return { .. } | CppStatement::ReturnCall { .. }]
                    )
                    || !matches!(body.first(), Some(CppStatement::Declare { .. }))
                    || sequence_contains_return(body)
                {
                    return Err(
                        "conditional guarded try requires one guard, a returning int32 handler, and no outer cleanup lifetime".into(),
                    );
                }
                if matches!(condition, CppCondition::Call { .. }) {
                    return Err(
                        "conditional guarded try requires a pure condition to preserve catch scope"
                            .into(),
                    );
                }
                span.validate(logical_source)?;
                try_span.validate(logical_source)?;
                condition.validate(&places, records, logical_source)?;
                require_bool(condition.value_type(), false, "if condition")?;
                binding.span.validate(logical_source)?;
                if binding.declaration_id.is_empty() || binding.name.is_empty() {
                    return Err("C++ catch binding is missing declaration identity".into());
                }
                require_int32(&binding.value_type, false, "catch binding")?;
                binding.value_type.validate_aliases_in(alias_sources)?;
                if places.contains_key(&binding.declaration_id)
                    || places.contains_name(&binding.name)
                {
                    return Err(format!(
                        "C++ catch binding `{}` shadows another supported place",
                        binding.name
                    ));
                }
                validate_nested_scope(
                    body,
                    cleanups,
                    scope_span,
                    &places,
                    records,
                    logical_source,
                    &self.name,
                )?;
                let mut handler_places = places.child();
                debug_assert!(!handler_places.contains_name(&binding.name));
                handler_places.insert_name(binding.name.clone());
                let inserted = handler_places.insert(
                    binding.declaration_id.clone(),
                    (binding.name.clone(), binding.value_type.clone()),
                );
                debug_assert!(inserted.is_ok());
                for member in handler {
                    member.validate(&handler_places, records, logical_source)?;
                }
                nested_scopes += 1;
                nested_scope_outer_cleanup_counts.push(0);
                has_conditional_cleanup_scope = true;
            } else if let CppStatement::If {
                condition,
                then_branch,
                else_branch,
                span,
            } = statement
                && then_branch
                    .iter()
                    .chain(else_branch)
                    .any(|statement| matches!(statement, CppStatement::Scope { .. }))
            {
                if !matches!(self.function_kind, CppFunctionKind::Free) {
                    return Err(
                        "conditional C++ construction is supported only in a free-function body"
                            .into(),
                    );
                }
                if nested_scopes != 0 || has_conditional_cleanup_scope {
                    return Err(format!(
                        "C++ function `{}` may contain exactly one cleanup scope in one if arm",
                        self.name
                    ));
                }
                if aggregate_locals != 0 || destructible_locals != 0 {
                    return Err(format!(
                        "C++ function `{}` cannot combine conditional construction with an outer aggregate object",
                        self.name
                    ));
                }
                let (scope_body, scope_cleanups, scope_span) = match (
                    then_branch.as_slice(),
                    else_branch.as_slice(),
                ) {
                    (
                        [
                            CppStatement::Scope {
                                body,
                                cleanups,
                                span,
                            },
                        ],
                        [],
                    )
                    | (
                        [],
                        [
                            CppStatement::Scope {
                                body,
                                cleanups,
                                span,
                            },
                        ],
                    ) => (body, cleanups, span),
                    _ => {
                        return Err(format!(
                            "C++ function `{}` may conditionally construct an object in exactly one otherwise-empty if arm",
                            self.name
                        ));
                    }
                };
                span.validate(logical_source)?;
                condition.validate(&places, records, logical_source)?;
                require_bool(condition.value_type(), false, "if condition")?;
                nested_scopes += 1;
                nested_scope_outer_cleanup_counts.push(0);
                has_conditional_cleanup_scope = true;
                validate_nested_scope(
                    scope_body,
                    scope_cleanups,
                    scope_span,
                    &places,
                    records,
                    logical_source,
                    &self.name,
                )?;
            } else {
                statement.validate(&places, records, logical_source)?;
            }
        }
        if nested_scopes != 0
            && aggregate_locals != 0
            && (aggregate_locals != 1
                || destructible_locals != 1
                || nested_scope_outer_cleanup_counts.as_slice() != [1])
        {
            return Err(format!(
                "C++ function `{}` may combine cleanup lifetimes only as one outer destructible object followed by one inner cleanup scope",
                self.name
            ));
        }
        if has_exception_cleanup_scope && nested_scopes != 0 {
            return Err(format!(
                "C++ function `{}` may unwind exactly one guard in a try region",
                self.name
            ));
        }
        if aggregate_locals > 1 && destructible_locals != aggregate_locals {
            return Err(format!(
                "C++ function `{}` may declare multiple aggregate locals only when all require destruction",
                self.name
            ));
        }
        if destructible_locals != 0 {
            let Some(CppStatement::Return { .. } | CppStatement::ReturnCall { .. }) =
                self.body.last()
            else {
                return Err(format!(
                    "C++ function `{}` with automatic destruction requires one final return",
                    self.name
                ));
            };
        }
        super::lifetime::LifetimePlan::new(&self.body, |id| records.get(id).copied())?
            .validate(&self.body, &self.name)?;
        match &self.function_kind {
            CppFunctionKind::Free
            | CppFunctionKind::StaticMethod { .. }
            | CppFunctionKind::Method { .. }
                if self.return_type != CppType::Void && !sequence_always_returns(&self.body) =>
            {
                return Err(
                    "supported non-void C++ function can reach the end without returning".into(),
                );
            }
            CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. }
                if sequence_contains_return(&self.body) =>
            {
                return Err(
                    "supported C++ constructor/destructor body cannot contain a return statement"
                        .into(),
                );
            }
            _ => {}
        }
        Ok(())
    }
}

impl CppStatement {
    fn validate(
        &self,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Declare { .. } => {
                Err("automatic C++ locals are currently supported only in the function body".into())
            }
            Self::Assign {
                target,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                let target_type = validate_place_reference(target, places, logical_source)?;
                match target_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, false, "assignment target")?;
                    }
                    CppType::Integer { .. } => {
                        require_scalar_integer(target_type, "assignment target")?;
                    }
                    _ => {
                        return Err(
                            "C++ assignment target is not a mutable reference or local".into()
                        );
                    }
                }
                value.validate(places, records, logical_source)?;
                let expected = match target_type {
                    CppType::LvalueReference { pointee } => pointee.as_ref(),
                    value => value,
                };
                if !same_scalar_type(expected, value.value_type()) {
                    return Err("C++ assignment requires matching widths and signedness".into());
                }
                require_scalar_integer(value.value_type(), "assignment value")
            }
            Self::Store {
                pointer,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                pointer.validate(places, records, logical_source)?;
                require_mutable_int32_pointer(pointer.value_type(), "store pointer")?;
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "stored value")
            }
            Self::MemberStore {
                object,
                field,
                value,
                span,
            } => {
                span.validate(logical_source)?;
                let object_type = validate_root_reference(object, places, logical_source)?;
                if matches!(object_type, CppType::Record { is_const: true, .. })
                    || matches!(object_type, CppType::LvalueReference { pointee } if matches!(pointee.as_ref(), CppType::Record { is_const: true, .. }))
                {
                    return Err(
                        "C++ member store cannot write through a const record reference".into(),
                    );
                }
                let field_type =
                    validate_member_reference(object, field, places, records, logical_source)?;
                value.validate(places, records, logical_source)?;
                if !same_scalar_type(value.value_type(), field_type) {
                    return Err(format!(
                        "C++ member store to `{}` has a mismatched value type",
                        field.name
                    ));
                }
                Ok(())
            }
            Self::Return {
                value,
                cleanups,
                span,
            } => {
                span.validate(logical_source)?;
                value.validate(places, records, logical_source)?;
                if require_scalar_integer(value.value_type(), "return value").is_err() {
                    require_bool(value.value_type(), false, "return value")?;
                }
                for cleanup in cleanups {
                    cleanup.validate(places, records, logical_source)?;
                }
                Ok(())
            }
            Self::ReturnCall {
                callee,
                arguments,
                value_type,
                cleanups,
                span,
            } => {
                validate_call(callee, arguments, span, places, records, logical_source)?;
                if require_scalar_integer(value_type, "return-call value").is_err() {
                    require_bool(value_type, false, "return-call value")?;
                }
                for cleanup in cleanups {
                    cleanup.validate(places, records, logical_source)?;
                }
                Ok(())
            }
            Self::Assume { condition, span } => {
                span.validate(logical_source)?;
                condition.validate(places, records, logical_source)?;
                require_bool(condition.value_type(), false, "assumption condition")?;
                if !checked_boolean_condition(condition, places, false) {
                    return Err("C++ __builtin_assume requires a total scalar condition without memory reads or side effects".into());
                }
                Ok(())
            }
            Self::LibraryAssert {
                condition,
                contract,
                metadata,
                specialization,
                span,
            } => {
                validate_library_assertion_metadata(contract, metadata, specialization)?;
                span.validate(logical_source)?;
                condition.validate(places, records, logical_source)?;
                require_bool(condition.value_type(), false, "library assertion condition")?;
                if !checked_boolean_condition(condition, places, true) {
                    return Err("C++ library assertion requires a supported scalar condition without side effects or partial arithmetic; field reads require normal memory authority".into());
                }
                Ok(())
            }
            Self::Throw { value, span } => {
                span.validate(logical_source)?;
                value.validate(places, records, logical_source)?;
                require_int32(value.value_type(), false, "exception payload")
            }
            Self::TryCatchInt32 { .. } => {
                Err("nested C++ try/catch is outside the scalar int32 profile".into())
            }
            Self::Scope { .. } => Err(
                "the supported C++ slice permits one nested scope directly in a free-function body"
                    .into(),
            ),
            Self::If {
                condition,
                then_branch,
                else_branch,
                span,
            } => {
                span.validate(logical_source)?;
                condition.validate(places, records, logical_source)?;
                require_bool(condition.value_type(), false, "if condition")?;
                for statement in then_branch.iter().chain(else_branch) {
                    statement.validate(places, records, logical_source)?;
                }
                Ok(())
            }
            Self::Call {
                callee,
                arguments,
                span,
            } => validate_call(callee, arguments, span, places, records, logical_source),
        }
    }
}

impl CppCleanup {
    fn validate(
        &self,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Destructor {
                object,
                callee,
                span,
            } => {
                span.validate(logical_source)?;
                callee.span.validate(logical_source)?;
                let CppType::Record {
                    declaration_id,
                    name,
                    ..
                } = validate_place_reference(object, places, logical_source)?
                else {
                    return Err("C++ destructor cleanup must name a record object".into());
                };
                let record = validate_record_reference(records, declaration_id, name)?;
                let Some(destructor) = &record.destructor else {
                    return Err(format!(
                        "C++ cleanup names trivially destructible record `{}`",
                        record.name
                    ));
                };
                if destructor.declaration_id != callee.declaration_id
                    || destructor.name != callee.name
                {
                    return Err(format!(
                        "C++ cleanup for `{}` names the wrong destructor",
                        object.name
                    ));
                }
                Ok(())
            }
        }
    }
}

impl CppInitializer {
    fn validate_for_local(
        &self,
        local_type: &CppType,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match (self, local_type) {
            (Self::Value { value }, CppType::Integer { .. }) => {
                value.validate(places, records, logical_source)?;
                if !same_scalar_type(local_type, value.value_type()) {
                    return Err(
                        "C++ local initializer requires matching widths and signedness".into(),
                    );
                }
                require_scalar_integer(value.value_type(), "local initializer")
            }
            (
                Self::Call {
                    callee,
                    arguments,
                    span,
                },
                CppType::Integer { .. },
            ) => validate_call(callee, arguments, span, places, records, logical_source),
            (
                Self::Aggregate { fields, span },
                CppType::Record {
                    declaration_id,
                    name,
                    ..
                },
            ) => {
                span.validate(logical_source)?;
                let record = validate_record_reference(records, declaration_id, name)?;
                if fields.len() != record.fields.len() {
                    return Err(format!(
                        "C++ aggregate initializer for `{name}` must initialize every field"
                    ));
                }
                for (initializer, expected) in fields.iter().zip(&record.fields) {
                    initializer.span.validate(logical_source)?;
                    initializer.field.span.validate(logical_source)?;
                    if initializer.field.record_declaration_id != *declaration_id
                        || initializer.field.declaration_id != expected.declaration_id
                        || initializer.field.name != expected.name
                    {
                        return Err(format!(
                            "C++ aggregate initializer for `{name}` does not follow declaration order"
                        ));
                    }
                    initializer
                        .value
                        .validate(places, records, logical_source)?;
                    if initializer.value.value_type() != &expected.value_type {
                        return Err(format!(
                            "C++ aggregate initializer for `{}.{}` has a mismatched value type",
                            name, expected.name
                        ));
                    }
                }
                Ok(())
            }
            (
                Self::Constructor {
                    callee,
                    arguments,
                    span,
                },
                CppType::Record { .. },
            ) => {
                if arguments
                    .iter()
                    .any(|argument| matches!(argument, CppCallArgument::Call { .. }))
                {
                    return Err(
                        "nested C++ calls in constructor arguments remain unsupported".into(),
                    );
                }
                validate_call(callee, arguments, span, places, records, logical_source)
            }
            (Self::Aggregate { .. }, _) => {
                Err("C++ aggregate initializer requires a supported record local".into())
            }
            (Self::Constructor { .. }, _) => {
                Err("C++ constructor initializer requires a supported record local".into())
            }
            (_, CppType::Record { .. }) => Err(
                "C++ record local requires direct aggregate or constructor initialization".into(),
            ),
            _ => Err("unsupported C++ local initializer".into()),
        }
    }
}

fn validate_call(
    callee: &CppFunctionReference,
    arguments: &[CppCallArgument],
    span: &CppSpan,
    places: &ValidationPlaces<'_>,
    records: &RecordIndex<'_>,
    logical_source: &str,
) -> Result<(), String> {
    let nested_calls = arguments
        .iter()
        .filter(|argument| matches!(argument, CppCallArgument::Call { .. }))
        .count();
    let isolated = arguments
        .iter()
        .find_map(|argument| match argument {
            CppCallArgument::Call { arguments, .. } => Some(scalar_only_arguments(arguments)),
            _ => None,
        })
        .unwrap_or(false);
    if nested_calls > 1
        || (nested_calls == 1
            && arguments.iter().any(|argument| match argument {
                CppCallArgument::Call { .. } => false,
                CppCallArgument::Value { value } => {
                    !stable_scalar_argument(value, places)
                        && !(isolated && field_scalar_argument(value))
                }
                CppCallArgument::Reference { .. } => true,
            }))
    {
        return Err("nested C++ call arguments require one call and order-independent scalar siblings to preserve evaluation order".into());
    }
    span.validate(logical_source)?;
    callee.span.validate(logical_source)?;
    if callee.declaration_id.is_empty() || callee.name.is_empty() {
        return Err("C++ call is missing resolved declaration identity".into());
    }
    for argument in arguments {
        argument.validate(places, records, logical_source)?;
    }
    Ok(())
}

// No pointer or reference crosses this call boundary, and no input is another
// call. Mutable globals and external calls are not admitted by
// this profile, so reachable code cannot acquire an alias to caller storage.
fn scalar_only_arguments(arguments: &[CppCallArgument]) -> bool {
    arguments.iter().all(|argument| {
        crate::instrumentation::record_deterministic_work(1);
        match argument {
            CppCallArgument::Value { value } => Scalar::of(value.value_type()).is_some(),
            CppCallArgument::Call { .. } | CppCallArgument::Reference { .. } => false,
        }
    })
}

pub(super) fn field_scalar_argument(expression: &CppExpression) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        CppExpression::MemberLoad { value_type, .. } => Scalar::of(value_type).is_some(),
        CppExpression::IntegralCast { value, .. } => field_scalar_argument(value),
        _ => false,
    }
}

// A sibling must be total and invariant across the nested call. Scalar
// locals and by-value parameters cannot have their address taken in this
// profile. References, pointers, field reads and checked arithmetic do not
// meet this condition, even when their expression syntax has no side effects.
fn stable_scalar_argument(expression: &CppExpression, places: &ValidationPlaces<'_>) -> bool {
    match expression {
        CppExpression::IntegerLiteral { .. }
        | CppExpression::CompilerConstant { .. }
        | CppExpression::ConstantReference { .. } => true,
        CppExpression::Load { place, .. } => matches!(
            places.get(&place.declaration_id),
            Some((_, CppType::Integer { .. } | CppType::Boolean { .. }))
        ),
        CppExpression::IntegralCast { value, .. } => stable_scalar_argument(value, places),
        _ => false,
    }
}

fn checked_boolean_condition(
    expression: &CppExpression,
    places: &ValidationPlaces<'_>,
    field_reads: bool,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        CppExpression::Binary {
            operator: CppBinaryOperator::LogicalAnd,
            left,
            right,
            ..
        } => {
            checked_boolean_condition(left, places, field_reads)
                && checked_boolean_condition(right, places, field_reads)
        }
        CppExpression::Binary {
            operator:
                CppBinaryOperator::Equal
                | CppBinaryOperator::NotEqual
                | CppBinaryOperator::LessThan
                | CppBinaryOperator::GreaterThan
                | CppBinaryOperator::LessEqual
                | CppBinaryOperator::GreaterEqual,
            left,
            right,
            ..
        } => {
            (stable_scalar_argument(left, places) || (field_reads && field_scalar_argument(left)))
                && (stable_scalar_argument(right, places)
                    || (field_reads && field_scalar_argument(right)))
        }
        CppExpression::IntegralCast {
            value,
            value_type: CppType::Boolean { .. },
            ..
        } => checked_boolean_condition(value, places, field_reads),
        _ => {
            stable_scalar_argument(expression, places)
                || (field_reads && field_scalar_argument(expression))
        }
    }
}

impl CppCallArgument {
    fn validate(
        &self,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::Call {
                callee,
                arguments,
                value_type,
                span,
            } => {
                if require_scalar_integer(value_type, "nested-call value").is_err() {
                    require_bool(value_type, false, "nested-call value")?;
                }
                validate_call(callee, arguments, span, places, records, logical_source)
            }
            Self::Value { value } => value.validate(places, records, logical_source),
            Self::Reference { place } => {
                let root = validate_root_reference(place, places, logical_source)?;
                for projection in &place.projections {
                    projection.span().validate(logical_source)?;
                }
                let (value_type, _) = resolve_reference_type(root, place, records)?;
                if let CppType::Record {
                    declaration_id,
                    name,
                    ..
                } = value_type
                {
                    validate_record_reference(records, declaration_id, name)?;
                    return Ok(());
                }
                if !place.projections.is_empty() || matches!(root, CppType::LvalueReference { .. })
                {
                    require_int32(value_type, true, "call reference argument")
                } else {
                    Err("C++ reference argument does not name a supported reference".into())
                }
            }
        }
    }
}

impl CppExpression {
    // Only a closed, typed Boolean conversion participates in return analysis.
    // The selected constexpr arm is retained as an ordinary constant if; an
    // unknown runtime condition must still return on both paths.
    fn constant_boolean(&self) -> Option<bool> {
        let Self::IntegralCast {
            value,
            value_type: CppType::Boolean { .. },
            ..
        } = self
        else {
            return None;
        };
        match value.as_ref() {
            Self::CompilerConstant { value, .. } | Self::IntegerLiteral { value, .. } => {
                match value.as_str() {
                    "0" => Some(false),
                    "1" => Some(true),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    pub(crate) fn value_type(&self) -> &CppType {
        match self {
            Self::IntegerLiteral { value_type, .. }
            | Self::CompilerConstant { value_type, .. }
            | Self::ConstantReference { value_type, .. }
            | Self::Load { value_type, .. }
            | Self::AddressOf { value_type, .. }
            | Self::Dereference { value_type, .. }
            | Self::MemberLoad { value_type, .. }
            | Self::IntegralCast { value_type, .. }
            | Self::Binary { value_type, .. } => value_type,
        }
    }

    fn references_place(&self, declaration_id: &str) -> bool {
        match self {
            Self::IntegerLiteral { .. }
            | Self::CompilerConstant { .. }
            | Self::ConstantReference { .. } => false,
            Self::Load { place, .. } | Self::AddressOf { place, .. } => {
                place.declaration_id == declaration_id
            }
            Self::Dereference { pointer, .. } | Self::IntegralCast { value: pointer, .. } => {
                pointer.references_place(declaration_id)
            }
            Self::MemberLoad { object, .. } => object.declaration_id == declaration_id,
            Self::Binary { left, right, .. } => {
                left.references_place(declaration_id) || right.references_place(declaration_id)
            }
        }
    }

    fn validate(
        &self,
        places: &ValidationPlaces<'_>,
        records: &RecordIndex<'_>,
        logical_source: &str,
    ) -> Result<(), String> {
        match self {
            Self::IntegerLiteral {
                value,
                value_type,
                span,
            }
            | Self::CompilerConstant {
                value,
                value_type,
                span,
            } => {
                require_scalar_integer(value_type, "integer constant type")?;
                let valid = Scalar::mutable_kind(value_type)
                    .and_then(|kind| kind.parse_literal(value))
                    .is_some();
                if !valid {
                    return Err(format!("unsupported C++ integer constant `{value}`"));
                }
                span.validate(logical_source)
            }
            Self::ConstantReference {
                constant,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                constant.span.validate(logical_source)?;
                if constant.declaration_id.is_empty() || constant.name.is_empty() {
                    return Err("C++ constant reference is missing declaration identity".into());
                }
                require_signed_int64(value_type, false, "constant reference type")
            }
            Self::Load {
                place,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let place_type = validate_place_reference(place, places, logical_source)?;
                match place_type {
                    CppType::LvalueReference { pointee } => {
                        if require_int32(pointee, true, "loaded reference pointee").is_ok() {
                            require_int32(value_type, false, "loaded value type")
                        } else {
                            require_signed_int64(pointee, true, "loaded reference pointee")?;
                            require_signed_int64(value_type, false, "loaded value type")
                        }
                    }
                    CppType::Boolean { .. } => {
                        require_bool(place_type, false, "loaded parameter")?;
                        require_bool(value_type, false, "loaded value type")
                    }
                    CppType::Integer { .. } => {
                        require_scalar_integer(place_type, "loaded scalar")?;
                        if !same_scalar_type(place_type, value_type) {
                            return Err(
                                "C++ scalar load requires matching widths and signedness".into()
                            );
                        }
                        require_scalar_integer(value_type, "loaded value type")
                    }
                    CppType::Pointer { .. } => {
                        require_mutable_int32_pointer(place_type, "loaded pointer parameter")?;
                        require_mutable_int32_pointer(value_type, "loaded pointer value type")
                    }
                    CppType::Record { .. } => {
                        Err("C++ record values cannot be loaded or copied".into())
                    }
                    CppType::Void => Err("C++ void values cannot be loaded".into()),
                }
            }
            Self::AddressOf {
                place,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let place_type = validate_place_reference(place, places, logical_source)?;
                match place_type {
                    CppType::LvalueReference { pointee } => {
                        require_int32(pointee, false, "addressed reference pointee")?;
                    }
                    _ => {
                        return Err(
                            "supported C++ address-of must name a mutable `int&` parameter".into(),
                        );
                    }
                }
                require_mutable_int32_pointer(value_type, "address-of result type")
            }
            Self::Dereference {
                pointer,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                pointer.validate(places, records, logical_source)?;
                require_mutable_int32_pointer(pointer.value_type(), "dereference operand")?;
                require_int32(value_type, false, "dereference result type")
            }
            Self::MemberLoad {
                object,
                field,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                let field_type =
                    validate_member_reference(object, field, places, records, logical_source)?;
                if !same_scalar_type(value_type, field_type) {
                    return Err(format!(
                        "C++ member load of `{}` has a mismatched value type",
                        field.name
                    ));
                }
                Ok(())
            }
            Self::IntegralCast {
                value,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                value.validate(places, records, logical_source)?;
                require_integral_scalar(value.value_type(), "integral cast operand")?;
                require_integral_scalar(value_type, "integral cast result")?;
                Ok(())
            }
            Self::Binary {
                operator:
                    operator @ (CppBinaryOperator::Add
                    | CppBinaryOperator::Subtract
                    | CppBinaryOperator::Multiply
                    | CppBinaryOperator::Divide
                    | CppBinaryOperator::Remainder),
                left,
                right,
                value_type,
                span,
                ..
            } => {
                require_scalar_integer(value_type, "binary result type")?;
                let kind = Scalar::mutable_kind(value_type).unwrap();
                if kind.is_wide()
                    && !(matches!(
                        operator,
                        CppBinaryOperator::Divide | CppBinaryOperator::Remainder
                    ) || (*operator == CppBinaryOperator::Multiply
                        && kind == ScalarKind::Int128))
                {
                    return Err(
                        "C++ wide arithmetic supports checked signed multiplication and signed/unsigned division/remainder only".into(),
                    );
                }
                span.validate(logical_source)?;
                left.validate(places, records, logical_source)?;
                right.validate(places, records, logical_source)?;
                if !same_scalar_type(left.value_type(), value_type)
                    || !same_scalar_type(right.value_type(), value_type)
                {
                    return Err("C++ arithmetic requires matching widths and signedness".into());
                }
                Ok(())
            }
            Self::Binary {
                operator:
                    CppBinaryOperator::Equal
                    | CppBinaryOperator::NotEqual
                    | CppBinaryOperator::LessThan
                    | CppBinaryOperator::GreaterThan
                    | CppBinaryOperator::LessEqual
                    | CppBinaryOperator::GreaterEqual,
                left,
                right,
                value_type,
                span,
            } => {
                span.validate(logical_source)?;
                require_bool(value_type, false, "comparison result type")?;
                left.validate(places, records, logical_source)?;
                right.validate(places, records, logical_source)?;
                require_scalar_integer(left.value_type(), "comparison operand")?;
                if !same_scalar_type(left.value_type(), right.value_type()) {
                    return Err("C++ equality requires matching widths and signedness".into());
                }
                Ok(())
            }
            Self::Binary {
                operator: CppBinaryOperator::LogicalAnd,
                left,
                right,
                value_type,
                span,
            } => {
                require_bool(value_type, false, "logical-and result type")?;
                span.validate(logical_source)?;
                left.validate(places, records, logical_source)?;
                right.validate(places, records, logical_source)?;
                require_bool(left.value_type(), false, "logical-and left operand")?;
                require_bool(right.value_type(), false, "logical-and right operand")
            }
        }
    }
}

fn sequence_constructs_record(statements: &[CppStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        CppStatement::Declare { local, .. } => matches!(local.value_type, CppType::Record { .. }),
        CppStatement::Scope { body, .. } => sequence_constructs_record(body),
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_constructs_record(then_branch) || sequence_constructs_record(else_branch),
        CppStatement::TryCatchInt32 {
            try_body, handler, ..
        } => sequence_constructs_record(try_body) || sequence_constructs_record(handler),
        _ => false,
    })
}

// Graph validation needs declaration identities throughout the function, not
// lexical visibility. Build this index once per visited function; lexical
// ValidationPlaces separately rejects uses before construction or after scope
// exit. Borrow keys and places so graph edges never copy a declaration's type.
struct FunctionPlaces<'a> {
    function: &'a CppFunction,
    declarations: BTreeMap<&'a str, &'a CppPlace>,
}

impl<'a> FunctionPlaces<'a> {
    fn new(function: &'a CppFunction) -> Result<Self, String> {
        let mut places = Self {
            function,
            declarations: BTreeMap::new(),
        };
        for parameter in &function.parameters {
            places.insert(parameter)?;
        }
        let mut pending = vec![function.body.as_slice()];
        while let Some(body) = pending.pop() {
            for statement in body {
                crate::instrumentation::record_deterministic_work(1);
                match statement {
                    CppStatement::Declare { local, .. } => places.insert(local)?,
                    CppStatement::Scope { body, .. } => pending.push(body),
                    CppStatement::TryCatchInt32 {
                        try_body,
                        binding,
                        handler,
                        ..
                    } => {
                        places.insert(binding)?;
                        pending.push(try_body);
                        pending.push(handler);
                    }
                    CppStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        pending.push(then_branch);
                        pending.push(else_branch);
                    }
                    _ => {}
                }
            }
        }
        Ok(places)
    }

    fn insert(&mut self, place: &'a CppPlace) -> Result<(), String> {
        crate::instrumentation::record_deterministic_work(1);
        if self
            .declarations
            .insert(&place.declaration_id, place)
            .is_some()
        {
            return Err(format!(
                "duplicate C++ place declaration identity `{}` in function `{}`",
                place.declaration_id, self.function.name
            ));
        }
        Ok(())
    }

    fn place_type(&self, declaration_id: &str) -> Option<&'a CppType> {
        crate::instrumentation::record_deterministic_work(1);
        self.declarations
            .get(declaration_id)
            .map(|place| &place.value_type)
    }
}

fn validate_nested_scope(
    body: &[CppStatement],
    cleanups: &[CppCleanup],
    span: &CppSpan,
    outer_places: &ValidationPlaces<'_>,
    records: &RecordIndex<'_>,
    logical_source: &str,
    function_name: &str,
) -> Result<(), String> {
    span.validate(logical_source)?;
    let mut places = outer_places.child();
    let mut local_count = 0;
    for statement in body {
        if let CppStatement::Declare {
            local: candidate,
            initializer,
            span,
        } = statement
        {
            span.validate(logical_source)?;
            candidate.span.validate(logical_source)?;
            if candidate.declaration_id.is_empty() || candidate.name.is_empty() {
                return Err("C++ local is missing declaration identity".into());
            }
            let CppType::Record {
                declaration_id,
                name,
                ..
            } = &candidate.value_type
            else {
                return Err("the nested-scope slice requires destructible record objects".into());
            };
            let record = validate_record_reference(records, declaration_id, name)?;
            record.require_flat_local_layout()?;
            if record.destructor.is_none()
                || !matches!(initializer, CppInitializer::Constructor { .. })
            {
                return Err(format!(
                    "nested C++ local `{}` requires direct construction and nontrivial destruction",
                    candidate.name
                ));
            }
            initializer.validate_for_local(
                &candidate.value_type,
                &places,
                records,
                logical_source,
            )?;
            if places
                .insert(
                    candidate.declaration_id.clone(),
                    (candidate.name.clone(), candidate.value_type.clone()),
                )
                .is_err()
            {
                return Err(format!(
                    "duplicate C++ local declaration identity `{}`",
                    candidate.declaration_id
                ));
            }
            if !places.insert_name(candidate.name.clone()) {
                return Err(format!(
                    "C++ local `{}` shadows another supported place",
                    candidate.name
                ));
            }
            local_count += 1;
        } else {
            statement.validate(&places, records, logical_source)?;
        }
    }
    if local_count == 0 {
        return Err(format!(
            "nested scope in `{function_name}` must declare at least one destructible object"
        ));
    }
    for cleanup in cleanups {
        cleanup.validate(&places, records, logical_source)?;
    }
    Ok(())
}

fn sequence_always_returns(statements: &[CppStatement]) -> bool {
    statements.iter().any(CppStatement::always_returns)
}

fn sequence_contains_return(statements: &[CppStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        CppStatement::Return { .. } | CppStatement::ReturnCall { .. } => true,
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_contains_return(then_branch) || sequence_contains_return(else_branch),
        CppStatement::Scope { body, .. } => sequence_contains_return(body),
        CppStatement::TryCatchInt32 {
            try_body, handler, ..
        } => sequence_contains_return(try_body) || sequence_contains_return(handler),
        _ => false,
    })
}

fn sequence_contains_throw(statements: &[CppStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        CppStatement::Throw { .. } => true,
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_contains_throw(then_branch) || sequence_contains_throw(else_branch),
        CppStatement::Scope { body, .. } => sequence_contains_throw(body),
        CppStatement::TryCatchInt32 {
            try_body, handler, ..
        } => sequence_contains_throw(try_body) || sequence_contains_throw(handler),
        _ => false,
    })
}

impl CppStatement {
    fn always_returns(&self) -> bool {
        match self {
            Self::Return { .. } | Self::ReturnCall { .. } | Self::Throw { .. } => true,
            Self::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => match condition.constant_boolean() {
                Some(true) => sequence_always_returns(then_branch),
                Some(false) => sequence_always_returns(else_branch),
                None => {
                    sequence_always_returns(then_branch) && sequence_always_returns(else_branch)
                }
            },
            Self::Scope { body, .. } => sequence_always_returns(body),
            Self::TryCatchInt32 {
                try_body, handler, ..
            } => sequence_always_returns(try_body) && sequence_always_returns(handler),
            Self::Declare { .. }
            | Self::Assign { .. }
            | Self::Store { .. }
            | Self::MemberStore { .. }
            | Self::Assume { .. }
            | Self::LibraryAssert { .. }
            | Self::Call { .. } => false,
        }
    }
}

fn validate_reachable_calls(
    declaration_id: &str,
    functions: &BTreeMap<String, &CppFunction>,
    records: &RecordIndex<'_>,
    visiting: &mut Vec<String>,
    visited: &mut BTreeMap<String, usize>,
) -> Result<usize, String> {
    crate::instrumentation::record_deterministic_work(1);
    if let Some(depth) = visited.get(declaration_id) {
        return Ok(*depth);
    }
    if let Some(start) = visiting.iter().position(|active| active == declaration_id) {
        let mut cycle = visiting[start..]
            .iter()
            .filter_map(|identity| {
                functions
                    .get(identity)
                    .map(|function| function.name.as_str())
            })
            .collect::<Vec<_>>();
        cycle.push(
            functions
                .get(declaration_id)
                .map_or("<unknown>", |function| function.name.as_str()),
        );
        return Err(format!(
            "recursive C++ calls are outside the supported slice: {}",
            cycle.join(" -> ")
        ));
    }
    super::budget::limit(
        "call graph depth",
        visiting.len() + 1,
        super::budget::MAX_CALL_DEPTH,
    )?;
    let function = functions.get(declaration_id).ok_or_else(|| {
        format!("C++ reachable graph refers to missing declaration `{declaration_id}`")
    })?;
    visiting.push(declaration_id.to_string());
    let places = FunctionPlaces::new(function)?;
    let mut calls = Vec::new();
    collect_calls(&function.body, &mut calls);
    let mut depth = 1usize;
    for call in calls {
        crate::instrumentation::record_deterministic_work(1);
        let (callee, arguments) = match &call {
            CollectedCall::Ordinary {
                callee, arguments, ..
            }
            | CollectedCall::Constructor {
                callee, arguments, ..
            } => (*callee, *arguments),
            CollectedCall::Destructor { callee, .. } => (*callee, &[][..]),
        };
        callee.span.validate(&function.span.file)?;
        let target = functions.get(&callee.declaration_id).ok_or_else(|| {
            format!(
                "C++ call to `{}` refers to missing reachable definition `{}`",
                callee.name, callee.declaration_id
            )
        })?;
        if target.name != callee.name {
            return Err(format!(
                "C++ declaration `{}` is named `{}`, not `{}`",
                callee.declaration_id, target.name, callee.name
            ));
        }
        match call {
            CollectedCall::Ordinary { destination, .. } => {
                if destination.is_some_and(|value| !same_scalar_type(value, &target.return_type)) {
                    return Err("C++ call result does not match its capture or return type".into());
                }
                if !matches!(
                    target.function_kind,
                    CppFunctionKind::Free
                        | CppFunctionKind::StaticMethod { .. }
                        | CppFunctionKind::Method { .. }
                ) {
                    return Err(format!(
                        "ordinary C++ call from `{}` cannot invoke object operation `{}`",
                        function.name, target.name
                    ));
                }
                validate_call_arguments(
                    &places,
                    target.name.as_str(),
                    &target.parameters,
                    arguments,
                    records,
                )?;
            }
            CollectedCall::Constructor { local, .. } => {
                let CppFunctionKind::Constructor {
                    record_declaration_id,
                    record_name,
                } = &target.function_kind
                else {
                    return Err(format!(
                        "C++ local `{}` construction refers to non-constructor `{}`",
                        local.name, target.name
                    ));
                };
                if !matches!(
                    &local.value_type,
                    CppType::Record { declaration_id, name, .. }
                        if declaration_id == record_declaration_id && name == record_name
                ) {
                    return Err(format!(
                        "C++ constructor `{}` does not construct local `{}`",
                        target.name, local.name
                    ));
                }
                let Some((_, explicit_parameters)) = target.parameters.split_first() else {
                    return Err(format!(
                        "C++ constructor `{}` is missing its object parameter",
                        target.name
                    ));
                };
                validate_call_arguments(
                    &places,
                    target.name.as_str(),
                    explicit_parameters,
                    arguments,
                    records,
                )?;
            }
            CollectedCall::Destructor { object, .. } => {
                let CppFunctionKind::Destructor {
                    record_declaration_id,
                    record_name,
                } = &target.function_kind
                else {
                    return Err(format!(
                        "C++ cleanup for `{}` refers to non-destructor `{}`",
                        object.name, target.name
                    ));
                };
                if !matches!(
                    places.place_type(&object.declaration_id),
                    Some(CppType::Record { declaration_id, name, .. })
                        if declaration_id == record_declaration_id && name == record_name
                ) {
                    return Err(format!(
                        "C++ destructor `{}` does not destroy object `{}`",
                        target.name, object.name
                    ));
                }
                if target.parameters.len() != 1 {
                    return Err(format!(
                        "C++ destructor `{}` has an invalid object interface",
                        target.name
                    ));
                }
            }
        }
        let child_depth = validate_reachable_calls(
            &callee.declaration_id,
            functions,
            records,
            visiting,
            visited,
        )?;
        // Cached subgraphs still contribute their full depth to this path.
        depth = depth.max(child_depth + 1);
        super::budget::limit("call graph depth", depth, super::budget::MAX_CALL_DEPTH)?;
    }
    visiting.pop();
    visited.insert(declaration_id.to_string(), depth);
    Ok(depth)
}

enum CollectedCall<'a> {
    Ordinary {
        callee: &'a CppFunctionReference,
        arguments: &'a [CppCallArgument],
        destination: Option<&'a CppType>,
    },
    Constructor {
        local: &'a CppPlace,
        callee: &'a CppFunctionReference,
        arguments: &'a [CppCallArgument],
    },
    Destructor {
        object: &'a CppPlaceReference,
        callee: &'a CppFunctionReference,
    },
}

fn collect_calls<'a>(statements: &'a [CppStatement], calls: &mut Vec<CollectedCall<'a>>) {
    for statement in statements {
        match statement {
            CppStatement::Declare {
                local,
                initializer:
                    CppInitializer::Call {
                        callee, arguments, ..
                    },
                ..
            } => collect_scalar_call(callee, arguments, Some(&local.value_type), calls),
            CppStatement::Declare {
                local,
                initializer:
                    CppInitializer::Constructor {
                        callee, arguments, ..
                    },
                ..
            } => calls.push(CollectedCall::Constructor {
                local,
                callee,
                arguments,
            }),
            CppStatement::Declare { .. } => {}
            CppStatement::Call {
                callee, arguments, ..
            } => collect_scalar_call(callee, arguments, None, calls),
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                if let CppCondition::Call { call } = condition {
                    collect_scalar_call(
                        &call.callee,
                        &call.arguments,
                        Some(&call.value_type),
                        calls,
                    );
                }
                collect_calls(then_branch, calls);
                collect_calls(else_branch, calls);
            }
            CppStatement::Scope { body, cleanups, .. } => {
                collect_calls(body, calls);
                for cleanup in cleanups {
                    let CppCleanup::Destructor { object, callee, .. } = cleanup;
                    calls.push(CollectedCall::Destructor { object, callee });
                }
            }
            CppStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                collect_calls(try_body, calls);
                collect_calls(handler, calls);
            }
            CppStatement::ReturnCall {
                callee,
                arguments,
                value_type,
                cleanups,
                ..
            } => {
                collect_scalar_call(callee, arguments, Some(value_type), calls);
                for cleanup in cleanups {
                    let CppCleanup::Destructor { object, callee, .. } = cleanup;
                    calls.push(CollectedCall::Destructor { object, callee });
                }
            }
            CppStatement::Return { cleanups, .. } => {
                for cleanup in cleanups {
                    let CppCleanup::Destructor { object, callee, .. } = cleanup;
                    calls.push(CollectedCall::Destructor { object, callee });
                }
            }
            CppStatement::Throw { .. }
            | CppStatement::Assume { .. }
            | CppStatement::LibraryAssert { .. }
            | CppStatement::Assign { .. }
            | CppStatement::Store { .. }
            | CppStatement::MemberStore { .. } => {}
        }
    }
}

fn collect_scalar_call<'a>(
    callee: &'a CppFunctionReference,
    arguments: &'a [CppCallArgument],
    destination: Option<&'a CppType>,
    calls: &mut Vec<CollectedCall<'a>>,
) {
    calls.push(CollectedCall::Ordinary {
        callee,
        arguments,
        destination,
    });
    collect_nested_calls(arguments, calls);
}

fn collect_nested_calls<'a>(arguments: &'a [CppCallArgument], calls: &mut Vec<CollectedCall<'a>>) {
    for argument in arguments {
        if let CppCallArgument::Call {
            callee,
            arguments,
            value_type,
            ..
        } = argument
        {
            calls.push(CollectedCall::Ordinary {
                callee,
                arguments,
                destination: Some(value_type),
            });
            collect_nested_calls(arguments, calls);
        }
    }
}

fn validate_call_arguments(
    caller: &FunctionPlaces<'_>,
    callee_name: &str,
    parameters: &[CppPlace],
    arguments: &[CppCallArgument],
    records: &RecordIndex<'_>,
) -> Result<(), String> {
    if arguments.len() != parameters.len() {
        return Err(format!(
            "C++ call from `{}` to `{}` has {} arguments for {} parameters",
            caller.function.name,
            callee_name,
            arguments.len(),
            parameters.len()
        ));
    }
    for (index, (argument, parameter)) in arguments.iter().zip(parameters).enumerate() {
        let compatible = match (argument, &parameter.value_type) {
            (CppCallArgument::Call { value_type, .. }, expected) => {
                same_scalar_type(value_type, expected)
            }
            (
                CppCallArgument::Value { value },
                CppType::Boolean {
                    bits: 8,
                    is_const: false,
                },
            ) => matches!(
                value.value_type(),
                CppType::Boolean {
                    bits: 8,
                    is_const: false,
                }
            ),
            (CppCallArgument::Value { value }, CppType::Integer { .. }) => {
                same_scalar_type(value.value_type(), &parameter.value_type)
            }
            (
                CppCallArgument::Reference { place },
                CppType::LvalueReference { pointee: expected },
            ) => {
                if let Some(root) = caller.place_type(&place.declaration_id) {
                    let (actual, actual_const) = resolve_reference_type(root, place, records)?;
                    match (actual, expected.as_ref()) {
                        (
                            CppType::Integer {
                                bits: 32,
                                signed: true,
                                ..
                            },
                            CppType::Integer {
                                bits: 32,
                                signed: true,
                                is_const: expected_const,
                                ..
                            },
                        ) => {
                            (!place.projections.is_empty()
                                || matches!(root, CppType::LvalueReference { .. }))
                                && (*expected_const || !actual_const)
                        }
                        (
                            CppType::Record {
                                declaration_id: actual_id,
                                name: actual_name,
                                ..
                            },
                            CppType::Record {
                                declaration_id,
                                name,
                                is_const,
                            },
                        ) => {
                            actual_id == declaration_id
                                && actual_name == name
                                && (*is_const || !actual_const)
                        }
                        _ => false,
                    }
                } else {
                    false
                }
            }
            (CppCallArgument::Value { value }, CppType::Pointer { pointee }) => {
                require_int32(pointee, false, "call pointer parameter").is_ok()
                    && require_mutable_int32_pointer(value.value_type(), "call pointer argument")
                        .is_ok()
            }
            _ => false,
        };
        if !compatible {
            return Err(format!(
                "C++ call from `{}` to `{}` has unsupported argument {} for parameter `{}`",
                caller.function.name,
                callee_name,
                index + 1,
                parameter.name
            ));
        }
    }
    Ok(())
}

struct CheckedConstants<'a> {
    declarations: BTreeMap<String, &'a CppConstant>,
    dependencies: BTreeMap<String, Option<String>>,
}

// Structural dependency order and compiler evaluation agreement are checked
// independently of the inventory budget. Each initializer uses checked prior
// values, rather than recursively expanding the dependency chain.
fn validate_constant_inventory<'a>(
    inventory: &'a [CppConstant],
    logical_source: &str,
    alias_sources: &BTreeSet<String>,
) -> Result<CheckedConstants<'a>, String> {
    let mut constants = BTreeMap::new();
    let mut dependencies = BTreeMap::new();
    for constant in inventory {
        crate::instrumentation::record_deterministic_work(1);
        let dependency = constant.validate(logical_source, alias_sources, &constants)?;
        if constants
            .insert(constant.declaration_id.clone(), constant)
            .is_some()
        {
            return Err(format!(
                "duplicate C++ constant declaration identity `{}`",
                constant.declaration_id
            ));
        }
        dependencies.insert(constant.declaration_id.clone(), dependency);
    }

    Ok(CheckedConstants {
        declarations: constants,
        dependencies,
    })
}

impl CppConstant {
    fn validate(
        &self,
        logical_source: &str,
        alias_sources: &BTreeSet<String>,
        prior_constants: &BTreeMap<String, &CppConstant>,
    ) -> Result<Option<String>, String> {
        if self.declaration_id.is_empty() || self.name.is_empty() {
            return Err("C++ constant is missing declaration identity".into());
        }
        self.span.validate(logical_source)?;
        require_const_signed_int64(&self.value_type, "constant type")?;
        self.value_type.validate_aliases_in(alias_sources)?;
        let (dependency, initializer_value) =
            validate_int64_initializer(&self.initializer, logical_source, prior_constants)?;
        let evaluated = self
            .evaluated_value
            .parse::<i64>()
            .map_err(|_| format!("unsupported C++ constant value `{}`", self.evaluated_value))?;
        if initializer_value != evaluated {
            return Err(format!(
                "C++ constant `{}` initializer disagrees with its evaluated value",
                self.name
            ));
        }
        Ok(dependency)
    }
}

fn validate_int64_initializer(
    expression: &CppExpression,
    logical_source: &str,
    prior_constants: &BTreeMap<String, &CppConstant>,
) -> Result<(Option<String>, i64), String> {
    match expression {
        CppExpression::IntegralCast {
            value,
            value_type,
            span,
        } => {
            span.validate(logical_source)?;
            require_signed_int64(value_type, true, "constant integral cast result")?;
            Ok((
                None,
                i64::from(evaluate_int32_literal(value, logical_source)?),
            ))
        }
        CppExpression::Binary {
            operator: CppBinaryOperator::Multiply,
            left,
            right,
            value_type,
            span,
        } => {
            span.validate(logical_source)?;
            require_signed_int64(value_type, false, "constant multiplication result")?;
            let CppExpression::IntegralCast {
                value: literal,
                value_type: cast_type,
                span: cast_span,
            } = left.as_ref()
            else {
                return Err(
                    "dependent C++ constant multiplication must cast one integer literal".into(),
                );
            };
            cast_span.validate(logical_source)?;
            require_signed_int64(cast_type, false, "constant multiplication left operand")?;
            let multiplier = i64::from(evaluate_int32_literal(literal, logical_source)?);
            let CppExpression::ConstantReference {
                constant,
                value_type: reference_type,
                span: reference_span,
            } = right.as_ref()
            else {
                return Err(
                    "dependent C++ constant multiplication must reference one prior constant"
                        .into(),
                );
            };
            reference_span.validate(logical_source)?;
            constant.span.validate(logical_source)?;
            let dependency = prior_constants
                .get(&constant.declaration_id)
                .ok_or_else(|| {
                    format!(
                        "C++ constant initializer refers to unknown or later declaration `{}`",
                        constant.declaration_id
                    )
                })?;
            if dependency.name != constant.name {
                return Err(format!(
                    "C++ constant declaration `{}` is named `{}`, not `{}`",
                    constant.declaration_id, dependency.name, constant.name
                ));
            }
            if !same_unqualified_integer_type(&dependency.value_type, reference_type) {
                return Err(format!(
                    "C++ constant reference `{}` has a mismatched value type",
                    constant.name
                ));
            }
            let dependency_value = dependency.evaluated_value.parse::<i64>().map_err(|_| {
                format!(
                    "unsupported C++ constant value `{}`",
                    dependency.evaluated_value
                )
            })?;
            let evaluated = multiplier.checked_mul(dependency_value).ok_or_else(|| {
                "supported C++ constant multiplication overflows signed 64-bit".to_string()
            })?;
            Ok((Some(constant.declaration_id.clone()), evaluated))
        }
        _ => Err(
            "supported C++ constants require a literal leaf or one dependent multiplication".into(),
        ),
    }
}

fn evaluate_int32_literal(expression: &CppExpression, logical_source: &str) -> Result<i32, String> {
    let CppExpression::IntegerLiteral {
        value,
        value_type,
        span,
    } = expression
    else {
        return Err("supported C++ constant cast requires one integer literal".into());
    };
    span.validate(logical_source)?;
    require_int32(value_type, false, "constant literal type")?;
    value
        .parse::<i32>()
        .map_err(|_| format!("unsupported C++ integer literal `{value}`"))
}

impl CppFunction {
    fn validate_constant_references(
        &self,
        logical_source: &str,
        constants: &BTreeMap<String, &CppConstant>,
        referenced_constants: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        validate_statement_constant_references(
            &self.body,
            logical_source,
            constants,
            referenced_constants,
        )
    }
}

fn validate_statement_constant_references(
    statements: &[CppStatement],
    logical_source: &str,
    constants: &BTreeMap<String, &CppConstant>,
    referenced_constants: &mut BTreeSet<String>,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            CppStatement::Declare { initializer, .. } => {
                initializer.validate_constant_references(
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::Assign { value, .. }
            | CppStatement::MemberStore { value, .. }
            | CppStatement::Return { value, .. }
            | CppStatement::Throw { value, .. }
            | CppStatement::Assume {
                condition: value, ..
            }
            | CppStatement::LibraryAssert {
                condition: value, ..
            } => {
                value.validate_constant_references(
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::Store { pointer, value, .. } => {
                pointer.validate_constant_references(
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
                value.validate_constant_references(
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::Scope { body, .. } => {
                validate_statement_constant_references(
                    body,
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                validate_statement_constant_references(
                    try_body,
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
                validate_statement_constant_references(
                    handler,
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                condition.validate_constant_references(
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
                validate_statement_constant_references(
                    then_branch,
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
                validate_statement_constant_references(
                    else_branch,
                    logical_source,
                    constants,
                    referenced_constants,
                )?;
            }
            CppStatement::Call { arguments, .. } | CppStatement::ReturnCall { arguments, .. } => {
                for argument in arguments {
                    argument.validate_constant_references(
                        logical_source,
                        constants,
                        referenced_constants,
                    )?;
                }
            }
        }
    }
    Ok(())
}

impl CppInitializer {
    fn validate_constant_references(
        &self,
        logical_source: &str,
        constants: &BTreeMap<String, &CppConstant>,
        referenced_constants: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        match self {
            Self::Value { value } => {
                value.validate_constant_references(logical_source, constants, referenced_constants)
            }
            Self::Call { arguments, .. } | Self::Constructor { arguments, .. } => {
                for argument in arguments {
                    argument.validate_constant_references(
                        logical_source,
                        constants,
                        referenced_constants,
                    )?;
                }
                Ok(())
            }
            Self::Aggregate { fields, .. } => {
                for field in fields {
                    field.value.validate_constant_references(
                        logical_source,
                        constants,
                        referenced_constants,
                    )?;
                }
                Ok(())
            }
        }
    }
}

impl CppCallArgument {
    fn validate_constant_references(
        &self,
        logical_source: &str,
        constants: &BTreeMap<String, &CppConstant>,
        referenced_constants: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        match self {
            Self::Value { value } => {
                value.validate_constant_references(logical_source, constants, referenced_constants)
            }
            Self::Call { arguments, .. } => {
                for argument in arguments {
                    argument.validate_constant_references(
                        logical_source,
                        constants,
                        referenced_constants,
                    )?;
                }
                Ok(())
            }
            Self::Reference { .. } => Ok(()),
        }
    }
}

impl CppExpression {
    fn validate_constant_references(
        &self,
        logical_source: &str,
        constants: &BTreeMap<String, &CppConstant>,
        referenced_constants: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        match self {
            Self::ConstantReference {
                constant,
                value_type,
                ..
            } => {
                constant.span.validate(logical_source)?;
                let resolved = constants.get(&constant.declaration_id).ok_or_else(|| {
                    format!(
                        "C++ expression refers to unknown constant declaration `{}`",
                        constant.declaration_id
                    )
                })?;
                if resolved.name != constant.name {
                    return Err(format!(
                        "C++ constant declaration `{}` is named `{}`, not `{}`",
                        constant.declaration_id, resolved.name, constant.name
                    ));
                }
                if !same_unqualified_integer_type(&resolved.value_type, value_type) {
                    return Err(format!(
                        "C++ constant reference `{}` has a mismatched value type",
                        constant.name
                    ));
                }
                referenced_constants.insert(constant.declaration_id.clone());
                Ok(())
            }
            Self::Dereference { pointer, .. } => pointer.validate_constant_references(
                logical_source,
                constants,
                referenced_constants,
            ),
            Self::IntegralCast { value, .. } => {
                value.validate_constant_references(logical_source, constants, referenced_constants)
            }
            Self::Binary { left, right, .. } => {
                left.validate_constant_references(logical_source, constants, referenced_constants)?;
                right.validate_constant_references(logical_source, constants, referenced_constants)
            }
            Self::IntegerLiteral { .. }
            | Self::CompilerConstant { .. }
            | Self::Load { .. }
            | Self::AddressOf { .. }
            | Self::MemberLoad { .. } => Ok(()),
        }
    }
}

fn valid_relative_source_path(value: &str) -> bool {
    let path = Path::new(value);
    !value.is_empty()
        && !value.as_bytes().contains(&0)
        && !path.is_absolute()
        && path.components().all(|component| {
            matches!(
                component,
                std::path::Component::Normal(_) | std::path::Component::CurDir
            )
        })
}

fn resolve_reference_type<'a>(
    root: &'a CppType,
    place: &CppPlaceReference,
    records: &'a RecordIndex<'a>,
) -> Result<(&'a CppType, bool), String> {
    super::budget::limit(
        "record field projections",
        place.projections.len(),
        super::budget::MAX_RECORDS,
    )?;
    let root_type = match root {
        CppType::LvalueReference { pointee } => pointee.as_ref(),
        value => value,
    };
    // The record profile forbids const embedded declarations and `mutable`
    // fields, so effective constness propagates from the complete root object.
    let root_const = match root_type {
        CppType::Record { is_const, .. } | CppType::Integer { is_const, .. } => *is_const,
        _ => false,
    };
    let (projected, _) = records.resolve_path(root, &place.projections)?;
    Ok((projected, root_const))
}

fn validate_place_reference<'a>(
    reference: &CppPlaceReference,
    places: &'a ValidationPlaces<'_>,
    logical_source: &str,
) -> Result<&'a CppType, String> {
    if !reference.projections.is_empty() {
        return Err("projected C++ places are unsupported in this operation".into());
    }
    validate_root_reference(reference, places, logical_source)
}

fn validate_root_reference<'a>(
    reference: &CppPlaceReference,
    places: &'a ValidationPlaces<'_>,
    logical_source: &str,
) -> Result<&'a CppType, String> {
    reference.span.validate(logical_source)?;
    let Some((name, value_type)) = places.get(&reference.declaration_id) else {
        return Err(format!(
            "C++ expression refers to unknown declaration `{}`",
            reference.declaration_id
        ));
    };
    if name != &reference.name {
        return Err(format!(
            "C++ declaration `{}` is named `{name}`, not `{}`",
            reference.declaration_id, reference.name
        ));
    }
    Ok(value_type)
}

fn validate_record_reference<'a>(
    records: &'a BTreeMap<String, &CppRecord>,
    declaration_id: &str,
    name: &str,
) -> Result<&'a CppRecord, String> {
    let record = records.get(declaration_id).ok_or_else(|| {
        format!("C++ type refers to unknown record declaration `{declaration_id}`")
    })?;
    if record.name != name {
        return Err(format!(
            "C++ record declaration `{declaration_id}` is named `{}`, not `{name}`",
            record.name
        ));
    }
    Ok(record)
}

fn validate_member_reference<'a>(
    object: &CppPlaceReference,
    field: &CppFieldReference,
    places: &'a ValidationPlaces<'_>,
    records: &'a RecordIndex<'a>,
    logical_source: &str,
) -> Result<&'a CppType, String> {
    field.span.validate(logical_source)?;
    if field.declaration_id.is_empty()
        || field.record_declaration_id.is_empty()
        || field.name.is_empty()
    {
        return Err("C++ member reference is missing declaration identity".into());
    }
    let object_type = validate_root_reference(object, places, logical_source)?;
    super::budget::limit(
        "record field projections",
        object.projections.len(),
        super::budget::MAX_RECORDS,
    )?;
    for projection in &object.projections {
        projection.span().validate(logical_source)?;
    }
    let (value_type, _) = records.resolve_path(
        object_type,
        object
            .projections
            .iter()
            .map(CppProjection::as_ref)
            .chain(std::iter::once(ProjectionRef::Field(field))),
    )?;
    Ok(value_type)
}

fn require_int32(value: &CppType, allow_const: bool, label: &str) -> Result<(), String> {
    if Scalar::of(value)
        .is_some_and(|scalar| scalar.kind == ScalarKind::Int32 && (allow_const || !scalar.is_const))
    {
        Ok(())
    } else {
        Err(format!("{label} is outside the first C++ `int` slice"))
    }
}

fn require_signed_int64(value: &CppType, allow_const: bool, label: &str) -> Result<(), String> {
    if Scalar::of(value)
        .is_some_and(|scalar| scalar.kind == ScalarKind::Int64 && (allow_const || !scalar.is_const))
    {
        Ok(())
    } else {
        Err(format!(
            "{label} is outside the supported C++ signed 64-bit slice"
        ))
    }
}

fn require_scalar_integer(value: &CppType, label: &str) -> Result<(), String> {
    if Scalar::mutable_kind(value).is_some_and(ScalarKind::is_integer) {
        Ok(())
    } else {
        Err(format!(
            "{label} requires a mutable signed or unsigned 32/64/128-bit integer"
        ))
    }
}

fn require_integral_scalar(value: &CppType, label: &str) -> Result<(), String> {
    if require_bool(value, false, label).is_ok() {
        Ok(())
    } else {
        require_scalar_integer(value, label)
    }
}

fn require_const_signed_int64(value: &CppType, label: &str) -> Result<(), String> {
    if Scalar::is(value, ScalarKind::Int64, true) {
        Ok(())
    } else {
        Err(format!(
            "{label} is outside the supported C++ `const` signed 64-bit slice"
        ))
    }
}

fn validate_return_types(statements: &[CppStatement], return_type: &CppType) -> Result<(), String> {
    for statement in statements {
        match statement {
            CppStatement::Return { value, .. }
                if !same_scalar_type(value.value_type(), return_type) =>
            {
                return Err("C++ return value does not match the function return type".into());
            }
            CppStatement::ReturnCall { value_type, .. }
                if !same_scalar_type(value_type, return_type) =>
            {
                return Err("C++ return-call value does not match the function return type".into());
            }
            CppStatement::Scope { body, .. } => validate_return_types(body, return_type)?,
            CppStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                validate_return_types(try_body, return_type)?;
                validate_return_types(handler, return_type)?;
            }
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                validate_return_types(then_branch, return_type)?;
                validate_return_types(else_branch, return_type)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn require_mutable_int32_pointer(value: &CppType, label: &str) -> Result<(), String> {
    match value {
        CppType::Pointer { pointee } => require_int32(pointee, false, label),
        _ => Err(format!(
            "{label} is outside the supported C++ mutable `int*` slice"
        )),
    }
}

fn require_bool(value: &CppType, allow_const: bool, label: &str) -> Result<(), String> {
    if Scalar::of(value)
        .is_some_and(|scalar| scalar.kind == ScalarKind::Bool && (allow_const || !scalar.is_const))
    {
        Ok(())
    } else {
        Err(format!("{label} is outside the supported C++ `bool` slice"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cleanup_span() -> CppSpan {
        CppSpan {
            file: "fixture.cpp".into(),
            start_line: 1,
            start_column: 1,
            end_line: 1,
            end_column: 2,
        }
    }

    fn signed_integer(bits: u32, is_const: bool) -> CppType {
        CppType::Integer {
            bits,
            signed: true,
            is_const,
            source_aliases: Vec::new(),
        }
    }

    fn return_call() -> CppStatement {
        CppStatement::ReturnCall {
            callee: CppFunctionReference {
                declaration_id: "callee".into(),
                name: "callee".into(),
                span: cleanup_span(),
            },
            arguments: vec![],
            value_type: signed_integer(32, false),
            cleanups: vec![],
            span: cleanup_span(),
        }
    }

    #[test]
    fn forged_assumptions_cannot_bypass_totality_type_or_place_checks() {
        let places = validation_places([
            ("n".into(), ("n".into(), signed_integer(32, false))),
            (
                "r".into(),
                (
                    "r".into(),
                    CppType::LvalueReference {
                        pointee: Box::new(signed_integer(32, false)),
                    },
                ),
            ),
        ]);
        let literal = || CppExpression::IntegerLiteral {
            value: "0".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let load = |id: &str| CppExpression::Load {
            place: CppPlaceReference {
                projections: Vec::new(),
                declaration_id: id.into(),
                name: id.into(),
                span: cleanup_span(),
            },
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let assume = |left| CppStatement::Assume {
            condition: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterThan,
                left: Box::new(left),
                right: Box::new(literal()),
                value_type: CppType::Boolean {
                    bits: 8,
                    is_const: false,
                },
                span: cleanup_span(),
            },
            span: cleanup_span(),
        };
        let validate = |statement: &CppStatement| {
            statement.validate(&places, &RecordIndex::default(), "fixture.cpp")
        };
        validate(&assume(load("n"))).unwrap();
        assert!(
            validate(&assume(load("r")))
                .unwrap_err()
                .contains("total scalar condition")
        );
        let partial = CppExpression::Binary {
            operator: CppBinaryOperator::Divide,
            left: Box::new(load("n")),
            right: Box::new(literal()),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        assert!(
            validate(&assume(partial))
                .unwrap_err()
                .contains("total scalar condition")
        );
        assert!(
            validate(&assume(load("unknown")))
                .unwrap_err()
                .contains("unknown declaration")
        );
        let non_boolean = CppStatement::Assume {
            condition: literal(),
            span: cleanup_span(),
        };
        assert!(
            validate(&non_boolean)
                .unwrap_err()
                .contains("assumption condition")
        );
    }

    #[test]
    fn recursive_metadata_is_checked_before_unsupported_nested_scope_policy() {
        let span = cleanup_span();
        let literal = CppExpression::IntegerLiteral {
            value: "1".into(),
            value_type: signed_integer(32, false),
            span: span.clone(),
        };
        let mut function = CppFunction {
            declaration_id: "root".into(),
            name: "root".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters: vec![],
            declared_noexcept: true,
            span: span.clone(),
            body: vec![CppStatement::If {
                condition: CppCondition::Expression(CppExpression::IntegralCast {
                    value: Box::new(literal.clone()),
                    value_type: CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                    span: span.clone(),
                }),
                then_branch: vec![CppStatement::Scope {
                    body: vec![CppStatement::Return {
                        value: literal,
                        cleanups: vec![],
                        span: span.clone(),
                    }],
                    cleanups: vec![],
                    span: span.clone(),
                }],
                else_branch: vec![],
                span,
            }],
        };
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        super::super::validity::check_function(&function, "fixture.cpp", &sources).unwrap();
        let validate = |function: &CppFunction| {
            function.validate(
                "fixture.cpp",
                &sources,
                &RecordIndex::default(),
                false,
                CppExceptionBehavior::NormalOnly,
            )
        };
        assert!(validate(&function).unwrap_err().contains("nested scope"));
        let CppStatement::If { then_branch, .. } = &mut function.body[0] else {
            unreachable!()
        };
        let CppStatement::Scope { body, .. } = &mut then_branch[0] else {
            unreachable!()
        };
        let CppStatement::Return { span, .. } = &mut body[0] else {
            unreachable!()
        };
        span.start_line = 0;
        assert!(
            validate(&function)
                .unwrap_err()
                .contains("invalid C++ source span")
        );
    }

    #[test]
    fn lexical_place_environments_borrow_outer_storage_and_own_only_scope_deltas() {
        for (outer_count, sibling_count) in [(4, 4), (32, 16), (256, 64), (2048, 256)] {
            let mut outer = ValidationPlaces::new();
            for index in 0..outer_count {
                let id = format!("outer-{index}");
                assert!(outer.insert_name(id.clone()));
                assert!(
                    outer
                        .insert(id.clone(), (id, signed_integer(32, false)))
                        .is_ok()
                );
            }
            let outer_place = outer.get("outer-0").unwrap();
            let mut owned_entries = 0;
            for _ in 0..sibling_count {
                let mut scope = outer.child();
                assert!(scope.declarations.is_empty());
                assert!(scope.names.is_empty());
                assert!(std::ptr::eq(scope.parent.unwrap(), &outer));
                // A lookup returns the original tuple and type, even after
                // adding local declarations. Nothing copies an outer type.
                for index in 0..2 {
                    let id = format!("local-{index}");
                    assert!(scope.insert_name(id.clone()));
                    assert!(
                        scope
                            .insert(id.clone(), (id, signed_integer(32, false)))
                            .is_ok()
                    );
                }
                assert!(std::ptr::eq(scope.get("outer-0").unwrap(), outer_place));
                assert!(scope.contains_name("outer-0"));
                assert!(!scope.insert_name("outer-0".into()));
                assert!(
                    scope
                        .insert(
                            "outer-0".into(),
                            ("wrong".into(), signed_integer(64, false))
                        )
                        .is_err()
                );
                assert!(std::ptr::eq(scope.get("outer-0").unwrap(), outer_place));
                owned_entries += scope.declarations.len();
                assert_eq!(scope.names.len(), 2);
                // Deeper lexical lookup and shadow checking use the same
                // parent chain, without copying either enclosing scope.
                let nested = scope.child();
                assert!(std::ptr::eq(nested.get("outer-0").unwrap(), outer_place));
                assert!(nested.contains_name("local-0"));
                assert!(nested.declarations.is_empty());
            }
            assert_eq!(owned_entries, sibling_count * 2);
            assert_eq!(outer.declarations.len(), outer_count);
            assert_eq!(outer.names.len(), outer_count);
            assert!(outer.get("local-0").is_none());
            assert!(!outer.contains_name("local-0"));
            let sibling = outer.child();
            let reference = CppPlaceReference {
                projections: Vec::new(),
                declaration_id: "local-0".into(),
                name: "local-0".into(),
                span: cleanup_span(),
            };
            assert!(
                validate_place_reference(&reference, &sibling, "fixture.cpp")
                    .unwrap_err()
                    .contains("unknown declaration")
            );
            let forged_name = CppPlaceReference {
                projections: Vec::new(),
                declaration_id: "outer-0".into(),
                name: "forged".into(),
                span: cleanup_span(),
            };
            assert!(
                validate_place_reference(&forged_name, &sibling, "fixture.cpp")
                    .unwrap_err()
                    .contains("is named")
            );
        }
    }

    fn validation_places<const N: usize>(
        entries: [(String, (String, CppType)); N],
    ) -> ValidationPlaces<'static> {
        let mut places = ValidationPlaces::new();
        for (id, (name, value_type)) in entries {
            assert!(places.insert_name(name.clone()));
            assert!(places.insert(id, (name, value_type)).is_ok());
        }
        places
    }

    #[test]
    fn static_helper_artifacts_require_class_identity_and_scalar_signature() {
        let mut function = CppFunction {
            declaration_id: "static_function".into(),
            name: "Math_echo".into(),
            function_kind: CppFunctionKind::StaticMethod {
                record_declaration_id: "Math_class".into(),
                record_name: "Math".into(),
            },
            return_type: signed_integer(32, false),
            parameters: vec![CppPlace {
                declaration_id: "value".into(),
                name: "value".into(),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            }],
            declared_noexcept: true,
            span: cleanup_span(),
            body: vec![CppStatement::Return {
                value: CppExpression::IntegerLiteral {
                    value: "7".into(),
                    value_type: signed_integer(32, false),
                    span: cleanup_span(),
                },
                cleanups: vec![],
                span: cleanup_span(),
            }],
        };
        let validate = |function: &CppFunction| {
            function.validate(
                "fixture.cpp",
                &BTreeSet::from(["fixture.cpp".into()]),
                &RecordIndex::default(),
                false,
                CppExceptionBehavior::NormalOnly,
            )
        };
        validate(&function).unwrap();
        function.name = "Other_echo".into();
        assert!(validate(&function).unwrap_err().contains("class identity"));
        function.name = "Math_echo".into();
        function.parameters[0].value_type = CppType::LvalueReference {
            pointee: Box::new(signed_integer(32, false)),
        };
        assert!(
            validate(&function)
                .unwrap_err()
                .contains("static helper parameter")
        );
        function.parameters[0].value_type = signed_integer(32, false);
        function.return_type = CppType::Void;
        assert!(
            validate(&function)
                .unwrap_err()
                .contains("static helper return type")
        );
        function.return_type = signed_integer(32, false);
        if let CppFunctionKind::StaticMethod {
            record_declaration_id,
            ..
        } = &mut function.function_kind
        {
            record_declaration_id.clear();
        }
        assert!(validate(&function).unwrap_err().contains("class identity"));
    }

    #[test]
    fn nested_call_sibling_artifacts_require_stable_scalar_storage_and_total_expressions() {
        let places = validation_places([
            (
                "scalar".into(),
                ("scalar".into(), signed_integer(32, false)),
            ),
            (
                "borrow".into(),
                (
                    "borrow".into(),
                    CppType::LvalueReference {
                        pointee: Box::new(signed_integer(32, false)),
                    },
                ),
            ),
        ]);
        let load = |id: &str| CppExpression::Load {
            place: CppPlaceReference {
                projections: Vec::new(),
                declaration_id: id.into(),
                name: id.into(),
                span: cleanup_span(),
            },
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        assert!(stable_scalar_argument(&load("scalar"), &places));
        assert!(!stable_scalar_argument(&load("borrow"), &places));
        let literal = CppExpression::IntegerLiteral {
            value: "7".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        assert!(stable_scalar_argument(&literal, &places));
        assert!(!stable_scalar_argument(
            &CppExpression::Binary {
                operator: CppBinaryOperator::Add,
                left: Box::new(literal.clone()),
                right: Box::new(literal.clone()),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            },
            &places
        ));
        let mut call = return_call();
        let CppStatement::ReturnCall { arguments, .. } = &mut call else {
            unreachable!()
        };
        arguments.push(CppCallArgument::Call {
            callee: CppFunctionReference {
                declaration_id: "inner".into(),
                name: "inner".into(),
                span: cleanup_span(),
            },
            arguments: vec![],
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        });
        arguments.push(CppCallArgument::Value {
            value: load("scalar"),
        });
        assert!(
            call.validate(&places, &RecordIndex::default(), "fixture.cpp")
                .is_ok()
        );
        let CppStatement::ReturnCall { arguments, .. } = &mut call else {
            unreachable!()
        };
        arguments[1] = CppCallArgument::Value {
            value: load("borrow"),
        };
        assert!(
            call.validate(&places, &RecordIndex::default(), "fixture.cpp")
                .unwrap_err()
                .contains("evaluation order")
        );
    }

    #[test]
    fn field_sibling_artifacts_require_a_scalar_isolated_input_call() {
        let record = CppRecord {
            declaration_id: "record".into(),
            name: "Box".into(),
            size_bytes: 4,
            alignment_bytes: 4,
            destructor: None,
            span: cleanup_span(),
            base: None,
            fields: vec![CppField {
                declaration_id: "field".into(),
                name: "value".into(),
                value_type: signed_integer(32, false),
                offset_bytes: 0,
                size_bytes: 4,
                span: cleanup_span(),
            }],
        };
        let records = RecordIndex::new(BTreeMap::from([("record".into(), &record)]));
        let places = validation_places([
            (
                "box".into(),
                (
                    "box".into(),
                    CppType::LvalueReference {
                        pointee: Box::new(CppType::Record {
                            declaration_id: "record".into(),
                            name: "Box".into(),
                            is_const: false,
                        }),
                    },
                ),
            ),
            (
                "borrow".into(),
                (
                    "borrow".into(),
                    CppType::LvalueReference {
                        pointee: Box::new(signed_integer(32, false)),
                    },
                ),
            ),
        ]);
        let reference = |id: &str| CppPlaceReference {
            projections: Vec::new(),
            declaration_id: id.into(),
            name: id.into(),
            span: cleanup_span(),
        };
        let callee = CppFunctionReference {
            declaration_id: "inner".into(),
            name: "inner".into(),
            span: cleanup_span(),
        };
        let value = CppCallArgument::Value {
            value: CppExpression::IntegerLiteral {
                value: "7".into(),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            },
        };
        let inner = |arguments| CppCallArgument::Call {
            callee: callee.clone(),
            arguments,
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let field = CppCallArgument::Value {
            value: CppExpression::MemberLoad {
                object: reference("box"),
                field: CppFieldReference {
                    record_declaration_id: "record".into(),
                    declaration_id: "field".into(),
                    name: "value".into(),
                    span: cleanup_span(),
                },
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            },
        };
        let validate = |argument| {
            validate_call(
                &callee,
                &[argument, field.clone()],
                &cleanup_span(),
                &places,
                &records,
                "fixture.cpp",
            )
        };
        validate(inner(vec![value.clone()])).unwrap();
        for hostile in [
            CppCallArgument::Reference {
                place: reference("borrow"),
            },
            CppCallArgument::Value {
                value: CppExpression::AddressOf {
                    place: reference("borrow"),
                    value_type: CppType::Pointer {
                        pointee: Box::new(signed_integer(32, false)),
                    },
                    span: cleanup_span(),
                },
            },
            inner(vec![value]),
        ] {
            assert!(
                validate(inner(vec![hostile]))
                    .unwrap_err()
                    .contains("evaluation order")
            );
        }
    }

    #[test]
    fn nested_call_artifacts_validate_capture_types_order_and_reachable_graph() {
        let nested = CppCallArgument::Call {
            callee: CppFunctionReference {
                declaration_id: "inner".into(),
                name: "inner".into(),
                span: cleanup_span(),
            },
            arguments: vec![],
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let mut call = return_call();
        let CppStatement::ReturnCall { arguments, .. } = &mut call else {
            unreachable!()
        };
        arguments.push(nested.clone());
        assert!(
            call.validate(
                &ValidationPlaces::new(),
                &RecordIndex::default(),
                "fixture.cpp"
            )
            .is_ok()
        );
        let mut invalid = call.clone();
        let CppStatement::ReturnCall { arguments, .. } = &mut invalid else {
            unreachable!()
        };
        arguments.push(nested.clone());
        assert!(
            invalid
                .validate(
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp"
                )
                .unwrap_err()
                .contains("evaluation order")
        );
        let mut invalid = nested.clone();
        let CppCallArgument::Call { value_type, .. } = &mut invalid else {
            unreachable!()
        };
        *value_type = CppType::Void;
        assert!(
            invalid
                .validate(
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp"
                )
                .is_err()
        );
        let function = |name: &str, body, parameters| CppFunction {
            declaration_id: name.into(),
            name: name.into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters,
            declared_noexcept: true,
            span: cleanup_span(),
            body,
        };
        let caller = function("caller", vec![call], vec![]);
        let callee = function(
            "callee",
            vec![],
            vec![CppPlace {
                declaration_id: "parameter".into(),
                name: "parameter".into(),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            }],
        );
        let inner = function("inner", vec![], vec![]);
        let validate = |inner: &CppFunction| {
            validate_reachable_calls(
                "caller",
                &BTreeMap::from([
                    ("caller".into(), &caller),
                    ("callee".into(), &callee),
                    ("inner".into(), inner),
                ]),
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
        };
        assert!(validate(&inner).is_ok());
        let mut changed = inner.clone();
        changed.return_type = signed_integer(64, false);
        assert!(validate(&changed).unwrap_err().contains("call result"));
        changed = inner.clone();
        changed.name = "wrong".into();
        assert!(validate(&changed).unwrap_err().contains("is named"));
        changed = inner;
        let mut recursive = return_call();
        let CppStatement::ReturnCall { callee, .. } = &mut recursive else {
            unreachable!()
        };
        callee.declaration_id = "caller".into();
        callee.name = "caller".into();
        changed.body.push(recursive);
        assert!(validate(&changed).unwrap_err().contains("recursive"));
    }

    #[test]
    fn nested_call_graph_validation_is_shared_by_initializers_and_discarded_calls() {
        let reference = |name: &str| CppFunctionReference {
            declaration_id: name.into(),
            name: name.into(),
            span: cleanup_span(),
        };
        let arguments = vec![CppCallArgument::Call {
            callee: reference("inner"),
            arguments: vec![],
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        }];
        let local = CppPlace {
            declaration_id: "captured".into(),
            name: "captured".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let function = |name: &str, body, parameters| CppFunction {
            declaration_id: name.into(),
            name: name.into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters,
            declared_noexcept: true,
            span: cleanup_span(),
            body,
        };
        for statement in [
            CppStatement::Declare {
                local: local.clone(),
                initializer: CppInitializer::Call {
                    callee: reference("outer"),
                    arguments: arguments.clone(),
                    span: cleanup_span(),
                },
                span: cleanup_span(),
            },
            CppStatement::Call {
                callee: reference("outer"),
                arguments: arguments.clone(),
                span: cleanup_span(),
            },
        ] {
            let caller = function("caller", vec![statement], vec![]);
            let outer = function("outer", vec![], vec![local.clone()]);
            let mut inner = function("inner", vec![], vec![]);
            let validate = |inner: &CppFunction| {
                validate_reachable_calls(
                    "caller",
                    &BTreeMap::from([
                        ("caller".into(), &caller),
                        ("outer".into(), &outer),
                        ("inner".into(), inner),
                    ]),
                    &RecordIndex::default(),
                    &mut Vec::new(),
                    &mut BTreeMap::new(),
                )
            };
            validate(&inner).unwrap();
            inner.return_type = signed_integer(64, false);
            assert!(validate(&inner).unwrap_err().contains("call result"));
            inner.return_type = signed_integer(32, false);
            inner.name = "forged".into();
            assert!(validate(&inner).unwrap_err().contains("is named"));
        }
        let constructor = CppInitializer::Constructor {
            callee: reference("ctor"),
            arguments,
            span: cleanup_span(),
        };
        assert!(
            constructor
                .validate_for_local(
                    &CppType::Record {
                        declaration_id: "R".into(),
                        name: "R".into(),
                        is_const: false
                    },
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp"
                )
                .unwrap_err()
                .contains("constructor arguments")
        );
    }

    #[test]
    fn return_call_artifacts_require_scalar_types_and_matching_returns() {
        let mut call = return_call();
        assert!(
            call.validate(
                &ValidationPlaces::new(),
                &RecordIndex::default(),
                "fixture.cpp"
            )
            .is_ok()
        );
        assert!(call.always_returns());
        assert!(validate_return_types(&[call.clone()], &signed_integer(64, false)).is_err());
        let CppStatement::ReturnCall {
            value_type,
            cleanups,
            ..
        } = &mut call
        else {
            unreachable!()
        };
        cleanups.clear();
        *value_type = CppType::Void;
        assert!(
            call.validate(
                &ValidationPlaces::new(),
                &RecordIndex::default(),
                "fixture.cpp"
            )
            .is_err()
        );
    }

    #[test]
    fn return_call_graphs_check_callee_identity_destination_arguments_and_cycles() {
        let function = |name: &str, body| CppFunction {
            declaration_id: name.into(),
            name: name.into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters: vec![],
            declared_noexcept: true,
            span: cleanup_span(),
            body,
        };
        let caller = function("caller", vec![return_call()]);
        let callee = function("callee", vec![]);
        let validate = |caller: &CppFunction, callee: &CppFunction| {
            validate_reachable_calls(
                "caller",
                &BTreeMap::from([("caller".into(), caller), ("callee".into(), callee)]),
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
        };
        assert!(validate(&caller, &callee).is_ok());
        let mut changed = callee.clone();
        changed.return_type = signed_integer(64, false);
        assert!(
            validate(&caller, &changed)
                .unwrap_err()
                .contains("call result")
        );
        changed = callee.clone();
        changed.return_type = CppType::Integer {
            bits: 32,
            signed: false,
            is_const: false,
            source_aliases: vec![],
        };
        assert!(
            validate(&caller, &changed)
                .unwrap_err()
                .contains("call result")
        );
        changed = callee.clone();
        changed.name = "other".into();
        assert!(
            validate(&caller, &changed)
                .unwrap_err()
                .contains("is named")
        );
        changed = callee.clone();
        changed.parameters.push(CppPlace {
            declaration_id: "parameter".into(),
            name: "parameter".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        });
        assert!(
            validate(&caller, &changed)
                .unwrap_err()
                .contains("arguments")
        );
        let mut changed_caller = caller.clone();
        let CppStatement::ReturnCall {
            callee: reference, ..
        } = &mut changed_caller.body[0]
        else {
            unreachable!()
        };
        reference.declaration_id = "missing".into();
        assert!(
            validate(&changed_caller, &callee)
                .unwrap_err()
                .contains("missing reachable definition")
        );
        let CppStatement::ReturnCall {
            callee: reference, ..
        } = &mut changed_caller.body[0]
        else {
            unreachable!()
        };
        reference.declaration_id = "caller".into();
        reference.name = "caller".into();
        assert!(
            validate(&changed_caller, &callee)
                .unwrap_err()
                .contains("recursive C++ calls")
        );
    }

    #[test]
    fn method_receiver_constness_and_field_authority_are_checked_in_artifacts() {
        let record = CppRecord {
            declaration_id: "record".into(),
            name: "State".into(),
            size_bytes: 8,
            alignment_bytes: 8,
            destructor: None,
            span: cleanup_span(),
            base: None,
            fields: vec![CppField {
                declaration_id: "field".into(),
                name: "fee".into(),
                value_type: signed_integer(64, false),
                offset_bytes: 0,
                size_bytes: 8,
                span: cleanup_span(),
            }],
        };
        let records = RecordIndex::new(BTreeMap::from([("record".into(), &record)]));
        let mut receiver = CppPlace {
            declaration_id: "self".into(),
            name: "self".into(),
            value_type: CppType::LvalueReference {
                pointee: Box::new(CppType::Record {
                    declaration_id: "record".into(),
                    name: "State".into(),
                    is_const: false,
                }),
            },
            span: cleanup_span(),
        };
        let field = CppFieldReference {
            record_declaration_id: "record".into(),
            declaration_id: "field".into(),
            name: "fee".into(),
            span: cleanup_span(),
        };
        let object = CppPlaceReference {
            projections: Vec::new(),
            declaration_id: "self".into(),
            name: "self".into(),
            span: cleanup_span(),
        };
        let store = CppStatement::MemberStore {
            object: object.clone(),
            field: field.clone(),
            value: CppExpression::MemberLoad {
                object,
                field,
                value_type: signed_integer(64, false),
                span: cleanup_span(),
            },
            span: cleanup_span(),
        };
        let mut function = CppFunction {
            declaration_id: "method".into(),
            name: "State_update".into(),
            function_kind: CppFunctionKind::Method {
                record_declaration_id: "record".into(),
                record_name: "State".into(),
                is_const: false,
            },
            return_type: CppType::Void,
            parameters: vec![receiver.clone()],
            declared_noexcept: true,
            span: cleanup_span(),
            body: vec![store],
        };
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        function
            .validate(
                "fixture.cpp",
                &sources,
                &records,
                false,
                CppExceptionBehavior::NormalOnly,
            )
            .unwrap();
        if let CppType::LvalueReference { pointee } = &mut receiver.value_type
            && let CppType::Record { is_const, .. } = pointee.as_mut()
        {
            *is_const = true;
        }
        function.parameters[0] = receiver;
        assert!(
            function
                .validate(
                    "fixture.cpp",
                    &sources,
                    &records,
                    false,
                    CppExceptionBehavior::NormalOnly
                )
                .unwrap_err()
                .contains("mismatched receiver")
        );
        if let CppFunctionKind::Method { is_const, .. } = &mut function.function_kind {
            *is_const = true;
        }
        assert!(
            function
                .validate(
                    "fixture.cpp",
                    &sources,
                    &records,
                    false,
                    CppExceptionBehavior::NormalOnly
                )
                .unwrap_err()
                .contains("const record reference")
        );

        let actual = function.parameters.clone();
        let arguments = vec![CppCallArgument::Reference {
            place: CppPlaceReference {
                projections: Vec::new(),
                declaration_id: "self".into(),
                name: "self".into(),
                span: cleanup_span(),
            },
        }];
        validate_call_arguments(
            &FunctionPlaces::new(&function).unwrap(),
            "read",
            &actual,
            &arguments,
            &RecordIndex::default(),
        )
        .unwrap();
        let mut writable = actual;
        if let CppType::LvalueReference { pointee } = &mut writable[0].value_type
            && let CppType::Record { is_const, .. } = pointee.as_mut()
        {
            *is_const = false;
        }
        assert!(
            validate_call_arguments(
                &FunctionPlaces::new(&function).unwrap(),
                "write",
                &writable,
                &arguments,
                &RecordIndex::default(),
            )
            .is_err()
        );
    }

    #[test]
    fn compiler_constant_artifacts_reject_out_of_range_unsigned_values() {
        for (bits, value, valid) in [
            (32, "4294967295", true),
            (32, "4294967296", false),
            (64, "18446744073709551615", true),
            (64, "18446744073709551616", false),
            (64, "-1", false),
            (128, "340282366920938463463374607431768211455", true),
            (128, "340282366920938463463374607431768211456", false),
            (128, "-1", false),
        ] {
            let constant = CppExpression::CompilerConstant {
                value: value.into(),
                value_type: CppType::Integer {
                    bits,
                    signed: false,
                    is_const: false,
                    source_aliases: vec![],
                },
                span: cleanup_span(),
            };
            assert_eq!(
                constant
                    .validate(
                        &ValidationPlaces::new(),
                        &RecordIndex::default(),
                        "fixture.cpp"
                    )
                    .is_ok(),
                valid
            );
        }
    }

    #[test]
    fn wide_artifact_function_boundaries_require_matching_types() {
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        let mut function = CppFunction {
            declaration_id: "root".into(),
            name: "root".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(64, false),
            parameters: vec![],
            declared_noexcept: true,
            span: cleanup_span(),
            body: vec![CppStatement::Return {
                value: CppExpression::IntegerLiteral {
                    value: "1".into(),
                    value_type: signed_integer(64, false),
                    span: cleanup_span(),
                },
                cleanups: vec![],
                span: cleanup_span(),
            }],
        };
        let validate = |function: &CppFunction| {
            function.validate(
                "fixture.cpp",
                &sources,
                &RecordIndex::default(),
                false,
                CppExceptionBehavior::NormalOnly,
            )
        };
        validate(&function).unwrap();
        function.return_type = signed_integer(128, false);
        assert!(validate(&function).unwrap_err().contains("return"));
        function.return_type = signed_integer(64, false);
        function.parameters.push(CppPlace {
            declaration_id: "input".into(),
            name: "input".into(),
            value_type: signed_integer(128, false),
            span: cleanup_span(),
        });
        validate(&function).unwrap();
    }

    #[test]
    fn wide_artifacts_admit_only_supported_arithmetic_and_comparisons() {
        for signed in [false, true] {
            let ty = CppType::Integer {
                bits: 128,
                signed,
                is_const: false,
                source_aliases: vec![],
            };
            let literal = CppExpression::IntegerLiteral {
                value: "1".into(),
                value_type: ty.clone(),
                span: cleanup_span(),
            };
            for operator in [
                CppBinaryOperator::Add,
                CppBinaryOperator::Subtract,
                CppBinaryOperator::Multiply,
                CppBinaryOperator::Divide,
                CppBinaryOperator::Remainder,
                CppBinaryOperator::Equal,
                CppBinaryOperator::NotEqual,
                CppBinaryOperator::LessThan,
                CppBinaryOperator::GreaterThan,
                CppBinaryOperator::LessEqual,
                CppBinaryOperator::GreaterEqual,
            ] {
                let comparison = matches!(
                    operator,
                    CppBinaryOperator::Equal
                        | CppBinaryOperator::NotEqual
                        | CppBinaryOperator::LessThan
                        | CppBinaryOperator::GreaterThan
                        | CppBinaryOperator::LessEqual
                        | CppBinaryOperator::GreaterEqual
                );
                let expression = CppExpression::Binary {
                    operator,
                    left: Box::new(literal.clone()),
                    right: Box::new(literal.clone()),
                    value_type: if comparison {
                        CppType::Boolean {
                            bits: 8,
                            is_const: false,
                        }
                    } else {
                        ty.clone()
                    },
                    span: cleanup_span(),
                };
                assert_eq!(
                    expression
                        .validate(
                            &ValidationPlaces::new(),
                            &RecordIndex::default(),
                            "fixture.cpp"
                        )
                        .is_ok(),
                    matches!(
                        operator,
                        CppBinaryOperator::Divide | CppBinaryOperator::Remainder
                    ) || comparison
                        || (signed && operator == CppBinaryOperator::Multiply),
                    "{signed}: {operator:?}"
                );
            }
        }
    }

    #[test]
    fn wide_comparison_artifacts_require_matching_operands_and_boolean_results() {
        for signed in [false, true] {
            for operator in [
                CppBinaryOperator::Equal,
                CppBinaryOperator::NotEqual,
                CppBinaryOperator::LessThan,
                CppBinaryOperator::GreaterThan,
                CppBinaryOperator::LessEqual,
                CppBinaryOperator::GreaterEqual,
            ] {
                for (bits, operand_signed) in [(64, signed), (128, !signed)] {
                    let expression = CppExpression::Binary {
                        operator,
                        left: Box::new(CppExpression::IntegerLiteral {
                            value: "7".into(),
                            value_type: CppType::Integer {
                                bits: 128,
                                signed,
                                is_const: false,
                                source_aliases: vec![],
                            },
                            span: cleanup_span(),
                        }),
                        right: Box::new(CppExpression::IntegerLiteral {
                            value: "3".into(),
                            value_type: CppType::Integer {
                                bits,
                                signed: operand_signed,
                                is_const: false,
                                source_aliases: vec![],
                            },
                            span: cleanup_span(),
                        }),
                        value_type: CppType::Boolean {
                            bits: 8,
                            is_const: false,
                        },
                        span: cleanup_span(),
                    };
                    assert!(
                        expression
                            .validate(
                                &ValidationPlaces::new(),
                                &RecordIndex::default(),
                                "fixture.cpp"
                            )
                            .unwrap_err()
                            .contains("matching widths and signedness")
                    );
                }
                let literal = CppExpression::IntegerLiteral {
                    value: "7".into(),
                    value_type: signed_integer(128, false),
                    span: cleanup_span(),
                };
                let expression = CppExpression::Binary {
                    operator,
                    left: Box::new(literal.clone()),
                    right: Box::new(literal),
                    value_type: signed_integer(128, false),
                    span: cleanup_span(),
                };
                assert!(
                    expression
                        .validate(
                            &ValidationPlaces::new(),
                            &RecordIndex::default(),
                            "fixture.cpp"
                        )
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn wide_division_artifacts_require_compiler_resolved_operand_types() {
        for signed in [false, true] {
            for operator in [CppBinaryOperator::Divide, CppBinaryOperator::Remainder] {
                for (bits, operand_signed) in [(64, signed), (128, !signed)] {
                    let ty = CppType::Integer {
                        bits: 128,
                        signed,
                        is_const: false,
                        source_aliases: vec![],
                    };
                    let operand_ty = CppType::Integer {
                        bits,
                        signed: operand_signed,
                        is_const: false,
                        source_aliases: vec![],
                    };
                    let expression = CppExpression::Binary {
                        operator,
                        left: Box::new(CppExpression::IntegerLiteral {
                            value: "7".into(),
                            value_type: ty.clone(),
                            span: cleanup_span(),
                        }),
                        right: Box::new(CppExpression::IntegerLiteral {
                            value: "3".into(),
                            value_type: operand_ty,
                            span: cleanup_span(),
                        }),
                        value_type: ty,
                        span: cleanup_span(),
                    };
                    assert!(
                        expression
                            .validate(
                                &ValidationPlaces::new(),
                                &RecordIndex::default(),
                                "fixture.cpp"
                            )
                            .unwrap_err()
                            .contains("matching widths and signedness")
                    );
                }
            }
        }
    }

    #[test]
    fn signed_arithmetic_artifacts_reject_mixed_width_operands() {
        let literal = CppExpression::IntegerLiteral {
            value: "1".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let cast = CppExpression::IntegralCast {
            value: Box::new(literal.clone()),
            value_type: signed_integer(64, false),
            span: cleanup_span(),
        };
        let mut expression = CppExpression::Binary {
            operator: CppBinaryOperator::Add,
            left: Box::new(cast.clone()),
            right: Box::new(cast),
            value_type: signed_integer(64, false),
            span: cleanup_span(),
        };
        for operator in [
            CppBinaryOperator::Add,
            CppBinaryOperator::Subtract,
            CppBinaryOperator::Multiply,
            CppBinaryOperator::Divide,
            CppBinaryOperator::Remainder,
        ] {
            if let CppExpression::Binary { operator: slot, .. } = &mut expression {
                *slot = operator;
            }
            expression
                .validate(
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp",
                )
                .unwrap();
        }
        if let CppExpression::Binary { right, .. } = &mut expression {
            **right = literal;
        }
        assert!(
            expression
                .validate(
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp"
                )
                .unwrap_err()
                .contains("matching widths and signedness")
        );
        if let CppExpression::Binary { right, .. } = &mut expression {
            let mut unsigned = signed_integer(64, false);
            if let CppType::Integer { signed, .. } = &mut unsigned {
                *signed = false;
            }
            **right = CppExpression::IntegerLiteral {
                value: "1".into(),
                value_type: unsigned,
                span: cleanup_span(),
            };
        }
        assert!(
            expression
                .validate(
                    &ValidationPlaces::new(),
                    &RecordIndex::default(),
                    "fixture.cpp"
                )
                .unwrap_err()
                .contains("matching widths and signedness")
        );
    }

    fn coin_constant() -> CppConstant {
        CppConstant {
            declaration_id: "coin".into(),
            name: "COIN".into(),
            value_type: signed_integer(64, true),
            initializer: CppExpression::IntegralCast {
                value: Box::new(CppExpression::IntegerLiteral {
                    value: "100000000".into(),
                    value_type: signed_integer(32, false),
                    span: cleanup_span(),
                }),
                value_type: signed_integer(64, true),
                span: cleanup_span(),
            },
            evaluated_value: "100000000".into(),
            span: cleanup_span(),
        }
    }

    fn max_money_constant(evaluated_value: &str) -> CppConstant {
        CppConstant {
            declaration_id: "max_money".into(),
            name: "MAX_MONEY".into(),
            value_type: signed_integer(64, true),
            initializer: CppExpression::Binary {
                operator: CppBinaryOperator::Multiply,
                left: Box::new(CppExpression::IntegralCast {
                    value: Box::new(CppExpression::IntegerLiteral {
                        value: "21000000".into(),
                        value_type: signed_integer(32, false),
                        span: cleanup_span(),
                    }),
                    value_type: signed_integer(64, false),
                    span: cleanup_span(),
                }),
                right: Box::new(CppExpression::ConstantReference {
                    constant: CppConstantReference {
                        declaration_id: "coin".into(),
                        name: "COIN".into(),
                        span: cleanup_span(),
                    },
                    value_type: signed_integer(64, false),
                    span: cleanup_span(),
                }),
                value_type: signed_integer(64, false),
                span: cleanup_span(),
            },
            evaluated_value: evaluated_value.into(),
            span: cleanup_span(),
        }
    }

    #[test]
    fn constant_inventory_checks_long_chains_and_rejects_malformed_dependencies() {
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        for size in [8, 32, 128, 512] {
            let mut constants = vec![coin_constant()];
            for index in 1..size {
                let mut dependent = max_money_constant("100000000");
                dependent.declaration_id = format!("constant_{index}");
                dependent.name = format!("C{index}");
                let CppExpression::Binary { left, right, .. } = &mut dependent.initializer else {
                    unreachable!()
                };
                let CppExpression::IntegralCast { value, .. } = left.as_mut() else {
                    unreachable!()
                };
                let CppExpression::IntegerLiteral { value, .. } = value.as_mut() else {
                    unreachable!()
                };
                *value = "1".into();
                let CppExpression::ConstantReference { constant, .. } = right.as_mut() else {
                    unreachable!()
                };
                constant.declaration_id = constants[index - 1].declaration_id.clone();
                constant.name = constants[index - 1].name.clone();
                constants.push(dependent);
            }
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_constant_inventory(&constants, "fixture.cpp", &sources)
            });
            assert_eq!(checked.unwrap().declarations.len(), size);
            assert!(
                work >= size && work <= 3 * size,
                "{size} constants: {work} work"
            );
            let mut wrong_value = constants.clone();
            wrong_value[size - 1].evaluated_value = "1".into();
            assert!(
                validate_constant_inventory(&wrong_value, "fixture.cpp", &sources)
                    .err()
                    .unwrap()
                    .contains("disagrees")
            );
            let mut duplicate = constants.clone();
            duplicate.push(coin_constant());
            assert!(
                validate_constant_inventory(&duplicate, "fixture.cpp", &sources)
                    .err()
                    .unwrap()
                    .contains("duplicate")
            );
            let mut cyclic = constants.clone();
            let CppExpression::Binary { right, .. } = &mut cyclic[1].initializer else {
                unreachable!()
            };
            let CppExpression::ConstantReference { constant, .. } = right.as_mut() else {
                unreachable!()
            };
            constant.declaration_id = constants[size - 1].declaration_id.clone();
            constant.name = constants[size - 1].name.clone();
            assert!(
                validate_constant_inventory(&cyclic, "fixture.cpp", &sources)
                    .err()
                    .unwrap()
                    .contains("unknown or later")
            );
        }
        let leaves = [coin_constant(), {
            let mut leaf = coin_constant();
            leaf.declaration_id = "other".into();
            leaf.name = "OTHER".into();
            leaf
        }];
        validate_constant_inventory(&leaves, "fixture.cpp", &sources).unwrap();
    }

    #[test]
    fn graph_reference_checks_index_growing_caller_places_once() {
        for size in [4usize, 32, 256, 2048] {
            let reference_type = CppType::LvalueReference {
                pointee: Box::new(signed_integer(32, false)),
            };
            let place = |id: String, value_type| CppPlace {
                name: id.clone(),
                declaration_id: id,
                value_type,
                span: cleanup_span(),
            };
            let mut caller = CppFunction {
                declaration_id: "caller".into(),
                name: "caller".into(),
                function_kind: CppFunctionKind::Free,
                return_type: signed_integer(32, false),
                parameters: (0..size)
                    .map(|index| place(format!("parameter-{index}"), reference_type.clone()))
                    .collect(),
                declared_noexcept: true,
                span: cleanup_span(),
                body: Vec::new(),
            };
            for index in 0..size {
                caller.body.push(CppStatement::Declare {
                    local: place(format!("local-{index}"), signed_integer(32, false)),
                    initializer: CppInitializer::Value {
                        value: CppExpression::IntegerLiteral {
                            value: "0".into(),
                            value_type: signed_integer(32, false),
                            span: cleanup_span(),
                        },
                    },
                    span: cleanup_span(),
                });
                caller.body.push(CppStatement::Call {
                    callee: CppFunctionReference {
                        declaration_id: "read".into(),
                        name: "read".into(),
                        span: cleanup_span(),
                    },
                    arguments: vec![CppCallArgument::Reference {
                        place: CppPlaceReference {
                            projections: Vec::new(),
                            declaration_id: format!("parameter-{}", size - 1),
                            name: format!("parameter-{}", size - 1),
                            span: cleanup_span(),
                        },
                    }],
                    span: cleanup_span(),
                });
            }
            let callee = CppFunction {
                declaration_id: "read".into(),
                name: "read".into(),
                function_kind: CppFunctionKind::Free,
                return_type: signed_integer(32, false),
                parameters: vec![place("parameter-0".into(), reference_type)],
                declared_noexcept: true,
                span: cleanup_span(),
                body: vec![],
            };
            let functions = BTreeMap::from([("caller".into(), &caller), ("read".into(), &callee)]);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_reachable_calls(
                    "caller",
                    &functions,
                    &RecordIndex::default(),
                    &mut Vec::new(),
                    &mut BTreeMap::new(),
                )
            });
            assert_eq!(result.unwrap(), 2);
            assert!(
                work >= size && work <= 10 * size + 16,
                "{size} places and reference edges: {work} work"
            );
            let places = FunctionPlaces::new(&caller).unwrap();
            assert_eq!(places.declarations.len(), 2 * size);
            assert!(std::ptr::eq(
                places.place_type("parameter-0").unwrap(),
                &caller.parameters[0].value_type
            ));
            assert!(places.place_type("unknown").is_none());
        }
    }

    #[test]
    fn function_place_index_rejects_identity_reuse_across_lexical_scopes() {
        let place = |id: &str| CppPlace {
            declaration_id: id.into(),
            name: "same_spelling".into(),
            value_type: signed_integer(32, false),
            span: cleanup_span(),
        };
        let declaration = |id: &str| CppStatement::Declare {
            local: place(id),
            initializer: CppInitializer::Value {
                value: CppExpression::IntegerLiteral {
                    value: "0".into(),
                    value_type: signed_integer(32, false),
                    span: cleanup_span(),
                },
            },
            span: cleanup_span(),
        };
        let scope = |id: &str| CppStatement::Scope {
            body: vec![declaration(id)],
            cleanups: vec![],
            span: cleanup_span(),
        };
        let mut function = CppFunction {
            declaration_id: "root".into(),
            name: "root".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters: vec![place("parameter")],
            declared_noexcept: false,
            span: cleanup_span(),
            body: vec![
                scope("first"),
                CppStatement::If {
                    condition: CppCondition::Expression(CppExpression::IntegerLiteral {
                        value: "1".into(),
                        value_type: signed_integer(32, false),
                        span: cleanup_span(),
                    }),
                    then_branch: vec![scope("then")],
                    else_branch: vec![scope("else")],
                    span: cleanup_span(),
                },
                CppStatement::TryCatchInt32 {
                    try_body: vec![scope("try")],
                    binding: place("catch"),
                    handler: vec![scope("handler")],
                    span: cleanup_span(),
                },
            ],
        };
        let places = FunctionPlaces::new(&function).unwrap();
        for id in [
            "parameter",
            "first",
            "then",
            "else",
            "try",
            "catch",
            "handler",
        ] {
            assert!(places.place_type(id).is_some(), "missing {id}");
        }
        assert_eq!(places.declarations.len(), 7);
        for id in [
            "first",
            "parameter",
            "catch",
            "then",
            "else",
            "try",
            "handler",
        ] {
            function.body.push(scope(id));
            let functions = BTreeMap::from([("root".into(), &function)]);
            let error = validate_reachable_calls(
                "root",
                &functions,
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
            .unwrap_err();
            assert!(
                error.contains("duplicate C++ place declaration identity"),
                "{error}"
            );
            assert!(error.contains(id), "{error}");
            function.body.pop();
        }
    }

    #[test]
    fn call_depth_budget_accounts_for_previously_checked_subgraphs() {
        for size in [8usize, 32, 63, 64] {
            let reference = |index| CppFunctionReference {
                declaration_id: format!("f{index}"),
                name: format!("f{index}"),
                span: cleanup_span(),
            };
            let mut functions = (0..size)
                .map(|index| CppFunction {
                    declaration_id: format!("f{index}"),
                    name: format!("f{index}"),
                    function_kind: CppFunctionKind::Free,
                    return_type: signed_integer(32, false),
                    parameters: vec![],
                    declared_noexcept: true,
                    span: cleanup_span(),
                    body: if index == 0 {
                        vec![]
                    } else {
                        vec![CppStatement::ReturnCall {
                            callee: reference(index - 1),
                            arguments: vec![],
                            value_type: signed_integer(32, false),
                            cleanups: vec![],
                            span: cleanup_span(),
                        }]
                    },
                })
                .collect::<Vec<_>>();
            let mut root = functions[0].clone();
            root.name = "root".into();
            root.declaration_id = "root".into();
            // Check short subgraphs first, so every following link uses a cache hit.
            root.body = (0..size)
                .map(|index| CppStatement::Call {
                    callee: reference(index),
                    arguments: vec![],
                    span: cleanup_span(),
                })
                .collect();
            functions.push(root);
            let index = functions
                .iter()
                .map(|function| (function.declaration_id.clone(), function))
                .collect();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_reachable_calls(
                    "root",
                    &index,
                    &RecordIndex::default(),
                    &mut Vec::new(),
                    &mut BTreeMap::new(),
                )
            });
            if size < super::super::budget::MAX_CALL_DEPTH {
                assert_eq!(result.unwrap(), size + 1);
            } else {
                assert!(
                    result
                        .unwrap_err()
                        .contains("artifact budget exhausted: call graph depth")
                );
            }
            assert!(
                work >= size && work <= 8 * size + 16,
                "{size} graph nodes: {work} work"
            );
        }
    }

    #[test]
    fn record_inventory_reachability_rejects_unused_layouts() {
        let record = CppRecord {
            declaration_id: "record".into(),
            name: "R".into(),
            size_bytes: 4,
            alignment_bytes: 4,
            destructor: None,
            span: cleanup_span(),
            base: None,
            fields: vec![CppField {
                declaration_id: "field".into(),
                name: "value".into(),
                value_type: signed_integer(32, false),
                offset_bytes: 0,
                size_bytes: 4,
                span: cleanup_span(),
            }],
        };
        let sources = BTreeSet::from(["fixture.cpp".into(), "record.h".into()]);
        for source in ["fixture.cpp", "record.h"] {
            for size in [8, 32, 128, 256] {
                let inventory = (0..size)
                    .map(|index| {
                        let mut copy = record.clone();
                        copy.span.file = source.into();
                        copy.fields[0].span.file = source.into();
                        copy.declaration_id = format!("record_{index}");
                        copy.name = format!("R{index}");
                        copy.fields[0].declaration_id = format!("field_{index}");
                        copy
                    })
                    .collect::<Vec<_>>();
                let (indexed, work) = crate::instrumentation::measure_deterministic_work(|| {
                    validate_record_inventory(&inventory, "fixture.cpp", &sources)
                });
                assert_eq!(indexed.unwrap().len(), size);
                assert!(
                    work >= size && work <= 7 * size,
                    "{size} layouts: {work} work"
                );
            }
        }
        let mut duplicate_field = record.clone();
        duplicate_field.declaration_id = "second".into();
        duplicate_field.name = "Second".into();
        assert!(
            validate_record_inventory(
                &[record.clone(), duplicate_field.clone()],
                "fixture.cpp",
                &sources
            )
            .unwrap_err()
            .contains("duplicate C++ field")
        );
        duplicate_field.fields[0].declaration_id = "other_field".into();
        duplicate_field.name = "R".into();
        assert!(
            validate_record_inventory(&[record.clone(), duplicate_field], "fixture.cpp", &sources)
                .unwrap_err()
                .contains("same-named record layouts")
        );
        record
            .validate(
                "fixture.cpp",
                &sources,
                &RecordIndex::new(BTreeMap::from([("record".into(), &record)])),
            )
            .unwrap();
        let records = RecordIndex::new(BTreeMap::from([("record".into(), &record)]));
        assert!(
            validate_reachable_records(&BTreeMap::new(), &records)
                .unwrap_err()
                .contains("outside the selected")
        );
        let function = CppFunction {
            declaration_id: "function".into(),
            name: "read".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            declared_noexcept: true,
            span: cleanup_span(),
            body: vec![],
            parameters: vec![CppPlace {
                declaration_id: "parameter".into(),
                name: "r".into(),
                span: cleanup_span(),
                value_type: CppType::LvalueReference {
                    pointee: Box::new(CppType::Record {
                        declaration_id: "record".into(),
                        name: "R".into(),
                        is_const: false,
                    }),
                },
            }],
        };
        validate_reachable_records(&BTreeMap::from([("function".into(), &function)]), &records)
            .unwrap();
    }

    #[test]
    fn embedded_record_graph_validation_is_linear_and_rejects_cycles() {
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        for size in [8, 32, 128, 256] {
            let mut inventory = (0..size)
                .map(|index| CppRecord {
                    declaration_id: format!("r{index}"),
                    name: format!("R{index}"),
                    size_bytes: 4,
                    alignment_bytes: 4,
                    destructor: None,
                    span: cleanup_span(),
                    base: None,
                    fields: vec![CppField {
                        declaration_id: format!("f{index}"),
                        name: "value".into(),
                        value_type: if index + 1 == size {
                            signed_integer(32, false)
                        } else {
                            CppType::Record {
                                declaration_id: format!("r{}", index + 1),
                                name: format!("R{}", index + 1),
                                is_const: false,
                            }
                        },
                        offset_bytes: 0,
                        size_bytes: 4,
                        span: cleanup_span(),
                    }],
                })
                .collect::<Vec<_>>();
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_record_inventory(&inventory, "fixture.cpp", &sources)
            });
            let checked = checked.unwrap();
            assert!(
                work >= size && work <= 8 * size,
                "{size} nested declarations: {work} work"
            );
            assert_eq!(
                record_layout_order(&checked).unwrap().first().unwrap().name,
                format!("R{}", size - 1)
            );
            let root = CppType::Record {
                declaration_id: "r0".into(),
                name: "R0".into(),
                is_const: false,
            };
            let path = (0..size)
                .map(|index| CppFieldReference {
                    record_declaration_id: format!("r{index}"),
                    declaration_id: format!("f{index}"),
                    name: "value".into(),
                    span: cleanup_span(),
                })
                .collect::<Vec<_>>();
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                checked.resolve_path(&root, &path)
            });
            assert_eq!(resolved.unwrap(), (&signed_integer(32, false), 0));
            assert_eq!(work, size);
            let mut const_root = root.clone();
            let CppType::Record { is_const, .. } = &mut const_root else {
                unreachable!()
            };
            *is_const = true;
            let reference = CppPlaceReference {
                declaration_id: "root".into(),
                name: "root".into(),
                span: cleanup_span(),
                projections: path.into_iter().map(CppProjection::Field).collect(),
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                resolve_reference_type(&const_root, &reference, &checked)
            });
            assert_eq!(resolved.unwrap(), (&signed_integer(32, false), true));
            assert_eq!(work, size);
            inventory[size - 1].fields[0].value_type = CppType::Record {
                declaration_id: "r0".into(),
                name: "R0".into(),
                is_const: false,
            };
            assert!(
                validate_record_inventory(&inventory, "fixture.cpp", &sources)
                    .unwrap_err()
                    .contains("by-value cycle")
            );
        }
    }

    #[test]
    fn field_projection_lookup_does_not_scan_sibling_fields() {
        for size in [8usize, 32, 128, 256] {
            let record = CppRecord {
                declaration_id: "r".into(),
                name: "R".into(),
                size_bytes: size as u32 * 4,
                alignment_bytes: 4,
                destructor: None,
                span: cleanup_span(),
                base: None,
                fields: (0..size)
                    .map(|index| CppField {
                        declaration_id: format!("f{index}"),
                        name: format!("value{index}"),
                        value_type: signed_integer(32, false),
                        offset_bytes: index as u32 * 4,
                        size_bytes: 4,
                        span: cleanup_span(),
                    })
                    .collect(),
            };
            let (records, work) = crate::instrumentation::measure_deterministic_work(|| {
                RecordIndex::new(BTreeMap::from([("r".into(), &record)]))
            });
            assert_eq!(work, size);
            let root = CppType::Record {
                declaration_id: "r".into(),
                name: "R".into(),
                is_const: false,
            };
            let field = CppFieldReference {
                record_declaration_id: "r".into(),
                declaration_id: format!("f{}", size - 1),
                name: format!("value{}", size - 1),
                span: cleanup_span(),
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                records.resolve_path(&root, [&field])
            });
            assert_eq!(
                resolved.unwrap(),
                (&signed_integer(32, false), (size - 1) as u32 * 4)
            );
            assert_eq!(work, 1);
            let reference = CppPlaceReference {
                declaration_id: "root".into(),
                name: "root".into(),
                span: cleanup_span(),
                projections: vec![CppProjection::Field(field)],
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                resolve_reference_type(&root, &reference, &records)
            });
            assert_eq!(resolved.unwrap(), (&signed_integer(32, false), false));
            assert_eq!(work, 1);
        }
    }

    #[test]
    fn schema_refuses_unknown_fields() {
        let input = br#"{"schema":1,"surprise":1}"#;
        let error = serde_json::from_slice::<CppExport>(input).unwrap_err();
        assert!(error.to_string().contains("unknown field"));
    }

    #[test]
    fn dependent_constant_requires_prior_identity_and_matching_checked_value() {
        let coin = coin_constant();
        let prior = BTreeMap::from([(coin.declaration_id.clone(), &coin)]);
        let sources = BTreeSet::from(["fixture.cpp".to_string()]);
        assert_eq!(
            max_money_constant("2100000000000000")
                .validate("fixture.cpp", &sources, &prior)
                .unwrap(),
            Some("coin".into())
        );

        let error = max_money_constant("2100000000000000")
            .validate("fixture.cpp", &sources, &BTreeMap::new())
            .unwrap_err();
        assert!(error.contains("unknown or later declaration"), "{error}");

        let error = max_money_constant("2099999999999999")
            .validate("fixture.cpp", &sources, &prior)
            .unwrap_err();
        assert!(
            error.contains("disagrees with its evaluated value"),
            "{error}"
        );
    }
    #[test]
    fn return_analysis_rejects_missing_return_in_the_reachable_constant_arm() {
        let condition = |value: &str| CppExpression::IntegralCast {
            value: Box::new(CppExpression::CompilerConstant {
                value: value.into(),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            }),
            value_type: CppType::Boolean {
                bits: 8,
                is_const: false,
            },
            span: cleanup_span(),
        };
        let returned = CppStatement::Return {
            value: CppExpression::IntegerLiteral {
                value: "7".into(),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            },
            cleanups: vec![],
            span: cleanup_span(),
        };
        let branch = |condition: CppExpression, then_branch, else_branch| CppStatement::If {
            condition: condition.into(),
            then_branch,
            else_branch,
            span: cleanup_span(),
        };
        assert!(branch(condition("1"), vec![returned.clone()], vec![]).always_returns());
        assert!(!branch(condition("0"), vec![returned.clone()], vec![]).always_returns());
        assert!(branch(condition("0"), vec![], vec![returned.clone()]).always_returns());
        assert!(!branch(condition("1"), vec![], vec![returned.clone()]).always_returns());
        let unknown = CppExpression::Load {
            place: CppPlaceReference {
                projections: Vec::new(),
                declaration_id: "flag".into(),
                name: "flag".into(),
                span: cleanup_span(),
            },
            value_type: CppType::Boolean {
                bits: 8,
                is_const: false,
            },
            span: cleanup_span(),
        };
        assert!(!branch(unknown, vec![returned], vec![]).always_returns());
    }
    #[test]
    fn single_base_inventory_walks_have_linear_work_and_reject_cycles() {
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        for size in [8, 32, 128] {
            let mut inventory = (0..size)
                .map(|index| CppRecord {
                    declaration_id: format!("r{index}"),
                    name: format!("R{index}"),
                    size_bytes: 4,
                    alignment_bytes: 4,
                    destructor: None,
                    span: cleanup_span(),
                    base: (index + 1 < size).then(|| CppBase {
                        value_type: CppType::Record {
                            declaration_id: format!("r{}", index + 1),
                            name: format!("R{}", index + 1),
                            is_const: false,
                        },
                        offset_bytes: 0,
                        size_bytes: 4,
                        span: cleanup_span(),
                    }),
                    fields: if index + 1 == size {
                        vec![CppField {
                            declaration_id: "leaf".into(),
                            name: "value".into(),
                            value_type: signed_integer(32, false),
                            offset_bytes: 0,
                            size_bytes: 4,
                            span: cleanup_span(),
                        }]
                    } else {
                        Vec::new()
                    },
                })
                .collect::<Vec<_>>();
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_record_inventory(&inventory, "fixture.cpp", &sources)
            });
            let checked = checked.unwrap();
            assert!(
                work >= size && work <= 8 * size,
                "{size} base declarations: {work} work"
            );
            assert_eq!(
                record_layout_order(&checked).unwrap().first().unwrap().name,
                format!("R{}", size - 1)
            );
            let mut path = (0..size - 1)
                .map(|index| CppProjection::Base {
                    base: CppBaseReference {
                        record_declaration_id: format!("r{index}"),
                        base_declaration_id: format!("r{}", index + 1),
                        base_name: format!("R{}", index + 1),
                        span: cleanup_span(),
                    },
                })
                .collect::<Vec<_>>();
            path.push(CppProjection::Field(CppFieldReference {
                record_declaration_id: format!("r{}", size - 1),
                declaration_id: "leaf".into(),
                name: "value".into(),
                span: cleanup_span(),
            }));
            let place = CppPlaceReference {
                declaration_id: "root".into(),
                name: "root".into(),
                span: cleanup_span(),
                projections: path,
            };
            for is_const in [false, true] {
                let root = CppType::Record {
                    declaration_id: "r0".into(),
                    name: "R0".into(),
                    is_const,
                };
                let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                    resolve_reference_type(&root, &place, &checked)
                });
                assert_eq!(resolved.unwrap(), (&signed_integer(32, false), is_const));
                assert_eq!(work, size);
            }
            inventory[size - 1].fields.clear();
            inventory[size - 1].base = Some(CppBase {
                value_type: CppType::Record {
                    declaration_id: "r0".into(),
                    name: "R0".into(),
                    is_const: false,
                },
                offset_bytes: 0,
                size_bytes: 4,
                span: cleanup_span(),
            });
            assert!(
                validate_record_inventory(&inventory, "fixture.cpp", &sources)
                    .unwrap_err()
                    .contains("by-value cycle")
            );
        }
    }

    #[test]
    fn cross_header_call_origins_have_linear_graph_work() {
        let span_in = |source: String| CppSpan {
            file: source,
            ..cleanup_span()
        };
        let function = |name: String, source: String, body| CppFunction {
            declaration_id: name.clone(),
            name,
            function_kind: CppFunctionKind::Free,
            return_type: CppType::Void,
            parameters: vec![],
            declared_noexcept: true,
            span: span_in(source),
            body,
        };
        let call = |name: String, source: String| CppStatement::Call {
            callee: CppFunctionReference {
                declaration_id: name.clone(),
                name,
                span: span_in(source.clone()),
            },
            arguments: vec![],
            span: span_in(source),
        };
        for size in [4, 16, 64, 128] {
            let mut functions = vec![function("leaf".into(), "leaf.h".into(), vec![])];
            for index in 0..size {
                let source = format!("header-{index}.h");
                functions.push(function(
                    format!("helper-{index}"),
                    source.clone(),
                    vec![call("leaf".into(), source)],
                ));
            }
            functions.push(function(
                "root".into(),
                "fixture.cpp".into(),
                (0..size)
                    .map(|index| call(format!("helper-{index}"), "fixture.cpp".into()))
                    .collect(),
            ));
            let sources = functions
                .iter()
                .map(|function| function.span.file.clone())
                .collect();
            for function in &functions {
                super::super::validity::check_function(function, &function.span.file, &sources)
                    .unwrap();
            }
            let index = functions
                .iter()
                .map(|function| (function.declaration_id.clone(), function))
                .collect();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_reachable_calls(
                    "root",
                    &index,
                    &RecordIndex::default(),
                    &mut Vec::new(),
                    &mut BTreeMap::new(),
                )
            });
            assert_eq!(result.unwrap(), 3);
            assert!(work <= 12 * size + 16, "{size}: {work}");
            let mut forged = functions[1].clone();
            let CppStatement::Call { callee, .. } = &mut forged.body[0] else {
                unreachable!()
            };
            callee.span.file = "leaf.h".into();
            let mut index = index.clone();
            index.insert(forged.declaration_id.clone(), &forged);
            assert!(
                validate_reachable_calls(
                    "root",
                    &index,
                    &RecordIndex::default(),
                    &mut Vec::new(),
                    &mut BTreeMap::new()
                )
                .unwrap_err()
                .contains("source span")
            );
        }
    }
}
