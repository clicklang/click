//! Compiler-owned typed Rust source vocabulary. No printed compiler dumps.
use serde::{Deserialize, Serialize};

pub const SCHEMA: u32 = 8;
pub const TARGET: &str = "x86_64-unknown-linux-gnu";

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RustExport {
    pub schema: u32,
    pub compiler_commit: String,
    pub target: String,
    pub edition: String,
    pub overflow_checks: bool,
    pub panic: String,
    pub mir_opt_level: u32,
    pub logical_source: String,
    pub records: Vec<Record>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub enums: Vec<Enum>,
    pub functions: Vec<Function>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Span {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Type {
    // Named Charon-only shared-byte chunk protocol; not general external ADTs.
    ChunkIterator,
    ChunkOption,
    SharedArrayIterator {
        element: Box<Type>,
    },
    SharedArrayOption {
        element: Box<Type>,
    },
    SharedScalarSlice {
        element: Box<Type>,
    },
    I32,
    U8,
    U16,
    U32,
    Usize,
    ByteSlice {
        mutable: bool,
    },
    Array {
        element: Box<Type>,
        length: u64,
    },
    Bool,
    Unit,
    Reference {
        mutable: bool,
        pointee: Box<Type>,
    },
    Record {
        name: String,
    },
    /// A value of a crate enum, which the sidecar names as a `spec enum` of
    /// the same name.
    Enum {
        name: String,
    },
    /// What a reference to a type parameter bound by a crate trait, `&T`
    /// for `T: Shape`, or a `&dyn Shape` refers to: a value of a type the
    /// function does not know, which it reaches only through the trait's
    /// methods. It is never a value by itself.
    TraitObject,
    /// A value of a type parameter bound by nothing a proof reads, `x: T` of
    /// `impl<T> Keep<T> for Echo`: a value of an abstract type, compared
    /// with `==` only, verified once for every type.
    Parameter {
        name: String,
    },
    /// A safe Rust-ABI function pointer of scalar parameters and result,
    /// `fn(i32) -> i32`.
    FnPointer {
        parameters: Vec<Type>,
        result: Box<Type>,
    },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub name: String,
    pub size: u32,
    pub alignment: u32,
    pub fields: Vec<Field>,
    pub destructor: Option<String>,
}
/// A crate enum whose fields are scalars: its values are values of the
/// `spec enum` of the same name, which the import declares for the sidecar.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Enum {
    pub name: String,
    pub variants: Vec<Variant>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Variant {
    pub name: String,
    /// A struct variant's field names, in declaration order; empty for a
    /// tuple or unit variant.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub field_names: Vec<String>,
    pub fields: Vec<Type>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Field {
    pub name: String,
    pub offset: u32,
    pub value_type: Type,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Place {
    pub name: String,
    pub value_type: Type,
    pub span: Span,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Function {
    pub name: String,
    pub return_type: Type,
    pub parameters: Vec<Place>,
    pub body: Vec<Statement>,
    pub mir: Option<MirBody>,
    /// A `safe fn` declared in an `unsafe extern` block, with no body: its
    /// calls are checked against the sidecar's `extern fn` contract.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub external: bool,
    /// A closure's leading parameters that are the variables it captures,
    /// fixed where an instance of it is created.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub captures: usize,
    /// A crate trait method's implementation: the external function that
    /// stands for the trait method, `traits::Shape::area`, whose contract
    /// this function must refine.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub implements: Option<String>,
    /// A generic function's instance at the scalar types a call gives its
    /// type parameters, declared with no body: the generic function, named
    /// here, is verified once for every type, and the instance's contract
    /// is its contract at these types.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instance_of: Option<String>,
    pub span: Span,
}

fn is_zero(count: &usize) -> bool {
    *count == 0
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Expression {
    IntegerFrom {
        value: Box<Self>,
        source_type: Type,
        value_type: Type,
    },
    SharedArrayHasNext {
        iterator: String,
    },
    SharedArrayOptionElement {
        option: String,
    },
    SharedArrayOptionTag {
        option: String,
    },
    ChunkHasNext {
        iterator: String,
    },
    ChunkOptionSlice {
        option: String,
    },
    ChunkOptionTag {
        option: String,
    },
    ChunkRemainder {
        iterator: String,
    },
    ArrayToSlice {
        array: Box<Self>,
        mutable: bool,
    },
    Array {
        elements: Vec<Self>,
    },
    Repeat {
        value: Box<Self>,
        length: u64,
    },
    Integer {
        value: i32,
    },
    UnsignedInteger {
        value: u32,
        value_type: Type,
    },
    UsizeInteger {
        value: u64,
    },
    SliceLength {
        slice: Box<Self>,
    },
    Index {
        slice: Box<Self>,
        index: Box<Self>,
    },
    Boolean {
        value: bool,
    },
    Local {
        name: String,
    },
    Binary {
        operator: String,
        left_type: Type,
        right_type: Type,
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        value: Box<Self>,
    },
    BitwiseNot {
        value: Box<Self>,
        value_type: Type,
    },
    Cast {
        value: Box<Self>,
        value_type: Type,
    },
    Borrow {
        place: Box<Self>,
        value_type: Type,
    },
    Deref {
        reference: Box<Self>,
        value_type: Type,
    },
    Field {
        base: Box<Self>,
        record: String,
        field: String,
    },
    Call {
        function: String,
        arguments: Vec<Self>,
    },
    /// A function item reified as a function pointer, `twice as fn(i32) -> i32`.
    FunctionAddress {
        function: String,
        value_type: Type,
    },
    /// A value of enum `name`'s `variant`, from its fields in declaration order.
    EnumConstruct {
        name: String,
        variant: String,
        fields: Vec<Self>,
    },
    /// Field `index` of `base`, an enum value a `match` arm has found to be
    /// `variant`.
    EnumField {
        base: Box<Self>,
        name: String,
        variant: String,
        index: usize,
    },
    /// A new instance of a closure that captures `captures`, as a callable
    /// value of `value_type`: `&|y| y + k as &dyn Fn(i32) -> i32`.
    ClosureInstance {
        function: String,
        captures: Vec<Self>,
        value_type: Type,
    },
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
    ChunkDeclare {
        iterator: String,
        slice: Expression,
        size: Expression,
    },
    ChunkFor {
        iterator: String,
        binding: Place,
        body: Vec<Self>,
    },
    // Compiler-resolved shared slice split, with the tuple destructured locally.
    SliceSplit {
        slice: Expression,
        midpoint: Expression,
        left: Place,
        right: Place,
    },
    // Compiler-resolved slice iterator protocol, not an index-loop rewrite.
    SliceFor {
        iterator: String,
        slice: Expression,
        binding: Place,
        by_reference: bool,
        body: Vec<Self>,
    },
    While {
        condition: Expression,
        body: Vec<Self>,
    },
    Declare {
        place: Place,
        initializer: Expression,
    },
    Assign {
        target: Expression,
        value: Expression,
    },
    If {
        condition: Expression,
        then_body: Vec<Self>,
        else_body: Vec<Self>,
    },
    Return {
        value: Option<Expression>,
    },
    Call {
        function: String,
        arguments: Vec<Expression>,
    },
}

// Drop-elaborated MIR with validated acyclic regions and natural while loops. Ownership events remain explicit in the
// artifact and are checked by live-value assertions in direct lowering.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBody {
    pub locals: Vec<Place>,
    pub blocks: Vec<MirBlock>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub terminator: MirTerminator,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MirStatement {
    SliceSplit {
        slice: Expression,
        midpoint: Expression,
        left: String,
        right: String,
    },
    SharedArrayInitialize {
        target: String,
        source: Expression,
    },
    SharedArrayMove {
        target: String,
        source: String,
    },
    SharedArrayNext {
        iterator: String,
        option: String,
    },
    ChunkInitialize {
        target: String,
        slice: Expression,
        size: Expression,
    },
    ChunkMove {
        target: String,
        source: String,
    },
    ChunkNext {
        iterator: String,
        option: String,
    },
    Assign {
        target: Expression,
        value: Expression,
    },
    Initialize {
        target: String,
        record: String,
        fields: Vec<Expression>,
    },
    Move {
        target: String,
        source: String,
        record: String,
    },
    Copy {
        target: String,
        source: String,
        record: String,
    },
    BeginStorage {
        local: String,
    },
    EndStorage {
        local: String,
    },
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MirTerminator {
    Goto {
        target: usize,
    },
    If {
        condition: Expression,
        then_target: usize,
        else_target: usize,
    },
    Drop {
        local: String,
        record: String,
        target: usize,
    },
    Call {
        function: String,
        arguments: Vec<Expression>,
        #[serde(default)]
        owned_arguments: Vec<OwnedArgument>,
        destination: String,
        target: usize,
        /// A call through the function pointer the local `function` holds.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        through_pointer: bool,
    },
    /// A `match`: the case whose label the scrutinee has, else `otherwise`.
    /// An enum's cases are its variants; an integer's are its values.
    Switch {
        scrutinee: Expression,
        cases: Vec<SwitchCase>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        otherwise: Option<usize>,
    },
    Return,
    Unreachable,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SwitchCase {
    pub label: SwitchLabel,
    pub target: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum SwitchLabel {
    /// An integer scrutinee's value, a constant expression of its type.
    Value { value: Expression },
    /// An enum scrutinee's variant.
    Variant { name: String },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OwnedArgument {
    pub index: usize,
    pub local: String,
    pub record: String,
    pub moved: bool,
}
