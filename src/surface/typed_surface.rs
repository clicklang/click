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
