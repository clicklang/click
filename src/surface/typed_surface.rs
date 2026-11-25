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

/// A typed Surface term.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SurfaceTerm {
    /// A term elaboration has not typed yet; lowering reads it the old way,
    /// as the surrounding typed node says.
    Untyped(SyntaxTerm),
}

impl SurfaceTerm {
    pub(crate) fn syntax(&self) -> &SyntaxTerm {
        match self {
            Self::Untyped(term) => term,
        }
    }
}

/// A typed Surface proposition.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SurfaceProposition {
    Comparison {
        kind: ComparisonKind,
        left: SurfaceTerm,
        operator: ComparisonOperator,
        right: SurfaceTerm,
    },
    And(Box<SurfaceProposition>, Box<SurfaceProposition>),
    Not(Box<SurfaceProposition>),
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
