//! Compiler-owned typed Rust source vocabulary. No printed compiler dumps.
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

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
    /// `Enumerate<Iter<T>>` over a slice of integers: the slice iterator's
    /// state and the count of values it has yielded.
    EnumerateIterator {
        element: Box<Type>,
    },
    /// The `Option<(usize, &T)>` an enumerated slice iterator yields.
    EnumerateOption {
        element: Box<Type>,
    },
    /// A `core::ops::Range` of an integer, `start..end`, held as its two
    /// bounds; the state of a `for` over it. An `inclusive` range,
    /// `start..=end`, also holds whether it is exhausted.
    Range {
        element: Box<Type>,
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        inclusive: bool,
    },
    /// `&[T]` or `&mut [T]` of a scalar `T` other than `u8`, whose slices
    /// are `ByteSlice`.
    ScalarSlice {
        element: Box<Type>,
        mutable: bool,
    },
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
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
    /// An owning `Box<R>` of a crate struct, carried as the address of its
    /// heap allocation; also the `*const R` the compiler reads it through,
    /// which only a box's own pointer becomes.
    Box {
        pointee: Box<Type>,
    },
    /// An `Option<Box<R>>`: the address of the box's allocation, or null
    /// for `None`.
    OptionBox {
        pointee: Box<Type>,
    },
    /// A `Vec<T>` of a scalar: the value of the library's primitive type
    /// `Vec<T>`, the sequence the vector holds. Its heap buffer and capacity
    /// are outside the model.
    Vec {
        element: Box<Type>,
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

impl Type {
    /// The width in bits of a Rust integer type; `isize` and `usize` are the
    /// pinned target's 64 bits.
    pub fn integer_bits(&self) -> Option<u32> {
        Some(match self {
            Type::I8 | Type::U8 => 8,
            Type::I16 | Type::U16 => 16,
            Type::I32 | Type::U32 => 32,
            Type::I64 | Type::Isize | Type::U64 | Type::Usize => 64,
            _ => return None,
        })
    }

    pub fn is_integer(&self) -> bool {
        self.integer_bits().is_some()
    }

    pub fn is_signed_integer(&self) -> bool {
        matches!(
            self,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize
        )
    }

    /// Whether every value of this integer type is a value of `target`, as
    /// a core `From` conversion between them requires.
    pub fn converts_losslessly_to(&self, target: &Type) -> bool {
        match (self.integer_bits(), target.integer_bits()) {
            (Some(source), Some(destination)) => {
                match (self.is_signed_integer(), target.is_signed_integer()) {
                    (false, false) | (true, true) => source <= destination,
                    (false, true) => source < destination,
                    (true, false) => false,
                }
            }
            _ => false,
        }
    }

    /// A scalar's Rust name, `i64` or `bool`.
    pub fn scalar_name(&self) -> Option<&'static str> {
        Some(match self {
            Type::I8 => "i8",
            Type::I16 => "i16",
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::Isize => "isize",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::U64 => "u64",
            Type::Usize => "usize",
            Type::Bool => "bool",
            _ => return None,
        })
    }

    /// An integer or `bool`: what a scalar parameter, result or field is.
    pub fn is_scalar(&self) -> bool {
        self.is_integer() || *self == Type::Bool
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub name: String,
    pub size: u32,
    pub alignment: u32,
    pub fields: Vec<Field>,
    pub destructor: Option<String>,
    /// An instance of a generic struct at an abstract type, `Cell<T>`: its
    /// size and its fields' offsets are terms the instance fixes, so `size`
    /// and each field's `offset` are 0 and unused.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub symbolic: bool,
}
/// An enum whose fields are scalars: its values are values of the
/// `spec enum` of the same name, which the import declares for the sidecar.
/// An instance of a generic enum, `Option<u32>`, names the `spec enum`
/// `generic` at `arguments`, and its variants' fields are at those arguments.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Enum {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generic: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<Type>,
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
    /// A Rust core method, `u32::min`, declared with no body: its contract
    /// is the library's, stating its result with the specification
    /// function of this path, `click::rust::u32::min`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub core_method: Option<String>,
    pub span: Span,
    /// The function's statements as written, by their `statement(i)...`
    /// paths, in preorder; a MIR `Site` names one by its index here.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sites: Vec<Vec<u32>>,
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
    /// The index of the element an enumerated iterator's `Some` holds.
    EnumerateOptionIndex {
        option: String,
    },
    /// Whether range `iterator` has a next value, `start < end`.
    RangeHasNext {
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
    /// Whether the enum `value` is its variant `variant`: the test a
    /// `match` on a crate iterator's `next()` makes for `Some`.
    VariantIs {
        value: Box<Self>,
        variant: String,
    },
    ChunkRemainder {
        iterator: String,
    },
    /// The result of the call step `call`, a call to `function` that ran
    /// just before the statement reading it: a value of the source
    /// expression that holds the call, never a local of the program.
    CallResult {
        call: u32,
        function: String,
        /// Whether this read leaves the result for a later read: a `match`'s
        /// test of it, before the arm that reads its payload.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        keeps: bool,
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
        value: u64,
        value_type: Type,
    },
    /// An `i8`, `i16`, `i64` or `isize` constant; an `i32` one is an
    /// `Integer`.
    SignedInteger {
        value: i64,
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
    /// The `None` of an `Option<Box<R>>`: the null address.
    NoneBox,
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
// artifact; rustc has decided them.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBody {
    pub locals: Vec<Place>,
    pub blocks: Vec<MirBlock>,
    /// The local MIR returns, `_0`, named `result` as contracts name the
    /// returned value, unless a source local has that name. A function
    /// whose return the importer reads directly (`ReturnValue`) has none.
    #[serde(default = "return_place_name")]
    pub return_place: String,
    /// The locals whose source name is bound more than once in the
    /// function, by their key in `locals`, with that source name. Each is
    /// its own declaration spelled as the source spells it; a proof's
    /// `word` names the innermost live one, as in C.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub spellings: BTreeMap<String, String>,
    /// Local keys for which the compiler supplied no source spelling.
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub unnamed_locals: BTreeSet<String>,
    /// Materialized aggregate literals, keyed by MIR local, with their source occurrence ordinal.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub compound_literals: BTreeMap<String, u32>,
    /// Unnamed scalar storage associated with a written borrow occurrence.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub borrowed_scalars: BTreeMap<String, u32>,
}

/// The name of a function's return place.
pub fn return_place_name() -> String {
    "result".into()
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub terminator: MirTerminator,
    /// The source statement the terminator comes from
    /// (`Function::sites`), when it comes from one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub terminator_site: Option<u32>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MirStatement {
    /// The statements after this one in its block, up to the next `Site`,
    /// come from source statement `site` of the function
    /// (`Function::sites`). It runs nothing.
    Site {
        site: u32,
    },
    /// A Rust panic guarded by `condition`, `assert!(condition)`: the
    /// verifier proves `condition` holds. `message` names the panic.
    Assert {
        condition: Expression,
        message: String,
    },
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
        /// The local the `Option` `next` returns is built in; `None` once
        /// the `for` loop reads only its element, which `payload` binds.
        option: Option<String>,
        /// The local bound by the yielding arm. A reference receives the
        /// yielded address, and an integer pattern receives its value.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<String>,
        /// Whether the iterator yields, when its `for` header's test already
        /// decided it: the statement is then that arm alone.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        taken: Option<bool>,
    },
    /// `target = source.enumerate()` of a slice iterator.
    EnumerateInitialize {
        target: String,
        source: String,
    },
    EnumerateMove {
        target: String,
        source: String,
    },
    EnumerateNext {
        iterator: String,
        /// The local the `Option` is built in; `None` once the loop reads only
        /// its index and element, which `index` and `element` bind.
        option: Option<String>,
        /// The local the yielded index is bound to.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        index: Option<String>,
        /// The local the yielded element's reference is bound to.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        element: Option<String>,
        /// Whether the iterator yields, when its `for` header's test already
        /// decided it: the statement is then that arm alone.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        taken: Option<bool>,
    },
    /// `target = start..end`.
    RangeInitialize {
        target: String,
        start: Expression,
        end: Expression,
    },
    RangeMove {
        target: String,
        source: String,
    },
    /// `option = iterator.next()`: `Some(start)`, advancing `start`, while
    /// `start < end`, else `None`. `option` is a value of the `Option`
    /// enum `option_type`.
    RangeNext {
        iterator: String,
        /// The local the `Option` `next` returns is built in; `None` once
        /// the `for` loop reads only its payload, which `payload` binds.
        option: Option<String>,
        option_type: String,
        /// The local the yielded value is bound to, the `for` loop's own
        /// variable, when the `Some` arm's first statement binds it: the
        /// yielding arm assigns it directly and builds no `Option`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<String>,
        /// Whether the range yields, when its `for` header's test already
        /// decided it: the statement is then that arm alone. An inclusive
        /// range's arm that yields is `if start < end { start += 1 } else
        /// { done = true }`, an ordinary branch of the loop body.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        taken: Option<bool>,
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
        /// The local the `Option` is built in; `None` once the loop reads only
        /// its chunk, which `payload` binds.
        option: Option<String>,
        /// The slice local the yielded chunk is bound to.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<String>,
        /// Whether the iterator yields, when its `for` header's test already
        /// decided it: the statement is then that arm alone.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        taken: Option<bool>,
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
        /// A local written by the call, absent for a discarded or retained result.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        destination: Option<String>,
        target: usize,
        /// A call through the function pointer the local `function` holds.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        through_pointer: bool,
        /// The call step whose result an expression reads as `Expression::CallResult`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        result: Option<u32>,
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
    /// `return value`: the function returns `value` itself. MIR writes the
    /// return place `_0` and then returns; when nothing runs between the
    /// write and the return, the importer returns the written value here
    /// and `_0` is not a local.
    ReturnValue {
        value: Expression,
    },
    Unreachable,
    /// A Rust panic, `assert!` or `panic!`: the verifier proves the block is
    /// never reached. `message` names the panic in a refusal.
    Panic {
        message: String,
    },
    /// The drop of the box `local`: run the record's drop `glue`, if it has
    /// one, on a non-null box, then free its allocation.
    BoxFree {
        local: String,
        record: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        glue: Option<String>,
        /// Whether `local` is an `Option<Box<R>>`, null for `None`.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        optional: bool,
        target: usize,
    },
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
