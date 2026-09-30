//! Compiler-owned typed Rust source vocabulary. No printed compiler dumps.
use serde::{Deserialize, Serialize};

pub const SCHEMA: u32 = 1;
pub const COMPILER_COMMIT: &str = "01dfd79246f1b2d5f146616deff08223a840a9ae";
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
    pub logical_source: String,
    pub records: Vec<Record>,
    pub functions: Vec<Function>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Span {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Type {
    I32,
    Bool,
    Unit,
    Reference { mutable: bool, pointee: Box<Type> },
    Record { name: String },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub name: String,
    pub size: u32,
    pub alignment: u32,
    pub fields: Vec<Field>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Field {
    pub name: String,
    pub offset: u32,
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
    pub span: Span,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Expression {
    Integer {
        value: i32,
    },
    Boolean {
        value: bool,
    },
    Local {
        name: String,
    },
    Binary {
        operator: String,
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        value: Box<Self>,
    },
    Borrow {
        place: Box<Self>,
    },
    Deref {
        reference: Box<Self>,
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
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
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
