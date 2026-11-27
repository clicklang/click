//! Typed Surface: the proof as elaboration understood it.
//!
//! Parsing produces Syntax (`SyntaxProposition`, `SyntaxTerm`), the proof as
//! written. Elaboration turns Syntax into Surface, deciding every distinction
//! the kernel makes from the syntactic context, and lowering builds kernel
//! terms from Surface without inferring anything (`design/typed-surface.md`).
//!
//! The migration types one construct at a time. Comparisons are typed first:
//! a Surface comparison records its kind, which elaboration chose from the
//! operands and which lowering only reads. Operands not yet migrated are
//! carried as Syntax in `SurfaceTerm::Untyped`.
use super::{ComparisonOperator, SyntaxTerm};

/// Which kind of comparison a written comparison is.
///
/// Elaboration decides this from both operands, so it cannot be decided one
/// operand at a time inside lowering. A native comparison's format, and
/// whether it compares machine words, pointers, Bools or floats, is the
/// operands' own type, built bottom-up from them; it is recorded here once
/// program expressions are typed Surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ComparisonKind {
    /// A comparison of program values, at the operands' C type.
    Native,
    /// A comparison of mathematical Integers; machine operands are observed.
    Integer,
    /// Equality of algebraic values.
    Algebraic,
    /// Equality of sequences, or membership with `in`.
    Sequence,
}

/// Which arithmetic an operation is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ArithmeticKind {
    /// Mathematical Integer arithmetic, which does not wrap.
    Integer,
    /// The program's own arithmetic at its operands' C type. Its format is
    /// the operands' type, which the kernel builds bottom-up from them when
    /// it evaluates the operation; it becomes a recorded field once Surface
    /// operands are typed.
    Native,
}

/// A binary arithmetic or bitwise operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ArithmeticOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    /// Rust's `<<`, whose shift count rules differ from C's.
    RustShiftLeft,
    ShiftRight,
    /// Rust's `>>`.
    RustShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

/// The type a Surface leaf, a literal or a name, has.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LeafType {
    /// A mathematical Integer.
    Integer,
    /// A C value of this type. For an unsuffixed decimal literal it is the
    /// type C gives the constant: `int32` when the value fits, else `int64`,
    /// else `uint64`. For a name it is the name's declared C type.
    Program(super::ProgramType),
}

/// A typed Surface term.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SurfaceTerm {
    /// An integer literal as written, with its type.
    IntegerLiteral { text: String, ty: LeafType },
    /// A name as written, with its type: an Integer binder, or a C variable
    /// at its declared type, which lowering resolves at the program point.
    Name { name: String, ty: LeafType },
    /// `left op right` in the arithmetic `kind` names.
    Binary {
        op: ArithmeticOperator,
        kind: ArithmeticKind,
        left: Box<SurfaceTerm>,
        right: Box<SurfaceTerm>,
    },
    /// `-operand` in the arithmetic `kind` names.
    Negate {
        kind: ArithmeticKind,
        operand: Box<SurfaceTerm>,
    },
    /// `~operand`, which exists only on machine words.
    BitwiseNot { operand: Box<SurfaceTerm> },
    /// C pointer arithmetic: `pointer` moved by `elements` whole elements of
    /// `element_width` bytes, backward when `backward` (`p - k`). The width
    /// is the pointee's size, which elaboration reads from the pointer's
    /// type.
    PointerStep {
        pointer: Box<SurfaceTerm>,
        elements: Box<SurfaceTerm>,
        element_width: u32,
        backward: bool,
    },
    /// A term elaboration has not typed yet; lowering reads it the old way,
    /// as the surrounding typed node says.
    Untyped(SyntaxTerm),
}

impl SurfaceTerm {
    /// The Syntax of a term not yet typed. Only Integer and native
    /// comparisons' operands have typed forms so far, so every other
    /// comparison's operands are `Untyped`.
    pub(crate) fn untyped_syntax(&self) -> &SyntaxTerm {
        match self {
            Self::Untyped(term) => term,
            typed => unreachable!("only Integer and native operands are typed so far: {typed:?}"),
        }
    }
}

/// A typed Surface proposition.
///
/// Constructs not yet moved to Surface are carried as `Untyped`, a borrow of
/// the Syntax they were elaborated from, which lowering reads the old way.
/// The borrow is transitional: once every construct is typed, Surface owns
/// all of its parts and the lifetime goes away.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SurfaceProposition<'s> {
    Comparison {
        kind: ComparisonKind,
        left: SurfaceTerm,
        operator: ComparisonOperator,
        right: SurfaceTerm,
    },
    And(Box<SurfaceProposition<'s>>, Box<SurfaceProposition<'s>>),
    Or(Box<SurfaceProposition<'s>>, Box<SurfaceProposition<'s>>),
    Implies(Box<SurfaceProposition<'s>>, Box<SurfaceProposition<'s>>),
    Not(Box<SurfaceProposition<'s>>),
    // Built by `Elaborator::elaborate_clause`, which only tests call until
    // contracts are elaborated before lowering.
    #[cfg_attr(not(test), allow(dead_code))]
    /// `forall` or `exists` over `name` at its declared type, with the body
    /// elaborated where `name` has that type. `syntax` is the quantifier as
    /// written, which lowering reads until it lowers the Surface body.
    Quantified {
        quantifier: Quantifier,
        name: super::binders::SurfaceBinder,
        click_type: super::ClickType,
        body: Box<SurfaceProposition<'s>>,
        syntax: &'s super::SyntaxProposition,
    },
    #[cfg_attr(not(test), allow(dead_code))]
    /// A range form over `item`, which ranges over `item_type`, the type
    /// elaboration gives the range from its endpoints, with the body
    /// elaborated where `item` has that type. `syntax` is the range as
    /// written, which lowering reads until it lowers the Surface body.
    Range {
        quantifier: Quantifier,
        item: super::binders::SurfaceBinder,
        item_type: super::ProgramType,
        body: Box<SurfaceProposition<'s>>,
        syntax: &'s super::SyntaxProposition,
    },
    Untyped(&'s super::SyntaxProposition),
}

/// Whether a binder form states its body for every value or for some value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) enum Quantifier {
    All,
    Some,
}

/// Elaborate a proposition's connective structure: `&&`, `||`, `implies` and
/// `!` become Surface connectives, and every other construct is carried as
/// `Untyped`. No connective needs a type, so this reads nothing but the
/// proposition. Iterative, so a long chain needs no deep stack.
pub(crate) fn elaborate_connectives(
    proposition: &super::SyntaxProposition,
) -> SurfaceProposition<'_> {
    use super::SyntaxProposition as Syntax;
    enum Frame<'s> {
        Visit(&'s Syntax),
        BuildAnd,
        BuildOr,
        BuildImplies,
        BuildNot,
    }
    let mut frames = vec![Frame::Visit(proposition)];
    let mut built = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(Syntax::And(left, right)) => {
                frames.extend([Frame::BuildAnd, Frame::Visit(right), Frame::Visit(left)]);
            }
            Frame::Visit(Syntax::Or(left, right)) => {
                frames.extend([Frame::BuildOr, Frame::Visit(right), Frame::Visit(left)]);
            }
            Frame::Visit(Syntax::Implies(left, right)) => {
                frames.extend([Frame::BuildImplies, Frame::Visit(right), Frame::Visit(left)]);
            }
            Frame::Visit(Syntax::Not(body)) => {
                frames.extend([Frame::BuildNot, Frame::Visit(body)]);
            }
            Frame::Visit(other) => built.push(SurfaceProposition::Untyped(other)),
            Frame::BuildNot => {
                let body = built.pop().expect("elaborated negation body");
                built.push(SurfaceProposition::Not(Box::new(body)));
            }
            frame => {
                let right = Box::new(built.pop().expect("elaborated right operand"));
                let left = Box::new(built.pop().expect("elaborated left operand"));
                built.push(match frame {
                    Frame::BuildAnd => SurfaceProposition::And(left, right),
                    Frame::BuildOr => SurfaceProposition::Or(left, right),
                    _ => SurfaceProposition::Implies(left, right),
                });
            }
        }
    }
    built.pop().expect("elaborated proposition has one root")
}

/// Whether a term is an Integer by its own spelling, whatever its context:
/// an explicit `(.. : Integer)`, a `to_integer(..)` or a named truncation, a
/// call to a function returning Integer, or arithmetic, a negation or a state
/// of such a term.
///
/// Elaboration's type synthesis (`contract_expression_click_type_in_scope`)
/// gives Integer for every such term; it may give Integer for more, such as a
/// name bound to an Integer. Printing uses only this test, so a comparison it
/// prints without an Integer marking reads back as Integer exactly when
/// elaboration would say so from the spelling alone.
pub(crate) fn spells_integer(term: &SyntaxTerm, returns_integer: &dyn Fn(&str) -> bool) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term {
            SyntaxTerm::IntegerContext(_) => return true,
            SyntaxTerm::Call { name, .. }
                if name == "to_integer"
                    || super::integer_truncation::is_integer_truncation(name)
                    || returns_integer(name) =>
            {
                return true;
            }
            SyntaxTerm::Negate(inner)
            | SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => pending.push(inner),
            SyntaxTerm::Add(left, right)
            | SyntaxTerm::Subtract(left, right)
            | SyntaxTerm::Multiply(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            _ => {}
        }
    }
    false
}

/// The Syntax that prints a Surface comparison: its operands as written,
/// with an Integer marking on the left exactly when the kind is Integer and
/// neither operand spells an Integer (`spells_integer`), so that elaborating
/// the printed form gives the same kind back.
pub(crate) fn print_comparison(
    kind: ComparisonKind,
    left: SyntaxTerm,
    operator: ComparisonOperator,
    right: SyntaxTerm,
    returns_integer: &dyn Fn(&str) -> bool,
) -> super::SyntaxProposition {
    let left = if kind == ComparisonKind::Integer
        && !spells_integer(&left, returns_integer)
        && !spells_integer(&right, returns_integer)
    {
        SyntaxTerm::IntegerContext(Box::new(left))
    } else {
        left
    };
    super::SyntaxProposition::Comparison {
        left,
        operator,
        right,
    }
}
