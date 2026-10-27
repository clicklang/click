//! Click `Bool`, the logical sort (`design/machine-integers.md`, Stage 5).
//!
//! A `Bool` term is a [`ConditionTerm`]. `Constant` and `Variable` are its
//! literals and binders, and every comparison is a `Bool` value. Four forms
//! are values that are not comparisons: [`ConditionTerm::BoolApplication`],
//! [`ConditionTerm::BoolIf`], [`ConditionTerm::BoolEqual`] and
//! [`ConditionTerm::BoolLoad`]. This module holds their constructors, the
//! structural helpers every traversal uses for them, and the statements of
//! the logic rules:
//!
//! - **L-If** ([`ConditionTerm::open_bool_if`]):
//!   `ConditionIs(if c { a } else { b }, t)` holds exactly when
//!   `(c and ConditionIs(a, t)) or (not c and ConditionIs(b, t))`. It is
//!   opened only on demand: by a decision of the conditional itself, which
//!   reads its condition first (`PureFactContext::decide_bool_if`), or by a
//!   proof step that asks for the split. Assuming a conditional files it as
//!   one fact; nothing expands it.
//! - **L-Eq** ([`ConditionTerm::bool_equal`]): `ConditionIs(a == b, true)`
//!   holds exactly when `a` and `b` have the same truth. A true one merges
//!   the two values' classes in the e-graph, which then share their truth;
//!   a false one contradicts the merge.
//! - **L-Unfold** ([`ConditionTerm::bool_unfold_equation`]): unfolding a
//!   `-> Bool` function's application files `application == body`.
//!
//! Soundness: these are the two-valued meaning of `if` and of logical
//! equality, and the defining equation of a total pure function, whose
//! termination is checked where it is declared. No rule here reads an
//! integer value of a `Bool`: the sort has none.

use super::{ConditionTerm, Pointer, Proposition, PureFunctionArgument, SharedCMemory};
use crate::kernel::SharedPureApplication;

impl ConditionTerm {
    /// Whether this is one of the `Bool` value forms that are not
    /// comparisons. One match on the root.
    pub(crate) fn is_bool_value_form(&self) -> bool {
        matches!(
            self,
            Self::BoolApplication(_)
                | Self::BoolIf { .. }
                | Self::BoolEqual(..)
                | Self::BoolLoad(..)
        )
    }

    /// The application of the `-> Bool` pure function `name`.
    pub(crate) fn bool_application(name: &str, arguments: Vec<PureFunctionArgument>) -> Self {
        Self::BoolApplication(SharedPureApplication::intern(name.to_owned(), arguments))
    }

    /// `if condition { then } else { else }` over `Bool`, folded where its
    /// shape decides it: a constant condition selects its branch, and equal
    /// branches are that branch. Neither fold reads a fact.
    pub(crate) fn bool_if(condition: Self, then_condition: Self, else_condition: Self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match condition {
            Self::Constant(true) => then_condition,
            Self::Constant(false) => else_condition,
            condition if then_condition == else_condition => {
                let _ = condition;
                then_condition
            }
            // Rule L-If at constant branches: `if c { true } else { false }`
            // is `c`.
            condition
                if then_condition == Self::Constant(true)
                    && else_condition == Self::Constant(false) =>
            {
                condition
            }
            condition => Self::BoolIf {
                condition: Box::new(condition),
                then_condition: Box::new(then_condition),
                else_condition: Box::new(else_condition),
            },
        }
    }

    /// The logical equality `left == right` of two `Bool` values. A value
    /// is equal to itself, so equal operands fold to `true`.
    pub(crate) fn bool_equal(left: Self, right: Self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        if left == right {
            return Self::Constant(true);
        }
        Self::BoolEqual(Box::new(left), Box::new(right))
    }

    /// The read of the one-byte `bool` cell at `pointer` in `memory`.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn bool_load(memory: SharedCMemory, pointer: Pointer) -> Self {
        Self::BoolLoad(memory, Box::new(pointer))
    }

    /// Rule L-If: the case split `ConditionIs(self, value)` means, for a
    /// conditional `if c { a } else { b }`:
    /// `(ConditionIs(c, true) and ConditionIs(a, value)) or
    /// (ConditionIs(c, false) and ConditionIs(b, value))`.
    /// `None` for every other condition. It opens one level; the branches
    /// stay as they are, so the work is constant.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn open_bool_if(&self, value: bool) -> Option<Proposition> {
        let Self::BoolIf {
            condition,
            then_condition,
            else_condition,
        } = self
        else {
            return None;
        };
        crate::instrumentation::record_deterministic_work(1);
        let arm = |selected: bool, branch: &ConditionTerm| {
            Proposition::And(
                Box::new(Proposition::ConditionIs(
                    condition.as_ref().clone(),
                    selected,
                )),
                Box::new(Proposition::ConditionIs(branch.clone(), value)),
            )
        };
        Some(Proposition::Or(
            Box::new(arm(true, then_condition)),
            Box::new(arm(false, else_condition)),
        ))
    }

    /// Rule L-Unfold: the defining equation `application == body` of a
    /// `-> Bool` pure function's application, as the fact unfolding files.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn bool_unfold_equation(
        application: SharedPureApplication,
        body: Self,
    ) -> Proposition {
        Proposition::ConditionIs(
            Self::BoolEqual(Box::new(Self::BoolApplication(application)), Box::new(body)),
            true,
        )
    }

    /// The child conditions of a `Bool` value form, in order: a
    /// conditional's condition and branches, an equality's operands. Empty
    /// for an application, a read and every other condition.
    pub(crate) fn bool_children(&self) -> impl Iterator<Item = &ConditionTerm> {
        let children: [Option<&ConditionTerm>; 3] = match self {
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => [Some(condition), Some(then_condition), Some(else_condition)],
            Self::BoolEqual(left, right) => [Some(left), Some(right), None],
            _ => [None, None, None],
        };
        children.into_iter().flatten()
    }

    /// A `Bool` value form rebuilt with `child` applied to each child
    /// condition, `argument` to each argument of an application, and `read`
    /// to a read's snapshot and pointer; `None` for every other condition.
    /// The constructors are the plain nodes, not the folding ones, so a
    /// substitution changes only what it rewrites.
    pub(crate) fn map_bool_value_form(
        &self,
        mut child: impl FnMut(&ConditionTerm) -> ConditionTerm,
        mut argument: impl FnMut(&PureFunctionArgument) -> PureFunctionArgument,
        read: impl FnOnce(&SharedCMemory, &Pointer) -> (SharedCMemory, Pointer),
    ) -> Option<ConditionTerm> {
        Some(match self {
            Self::BoolApplication(application) => {
                Self::BoolApplication(SharedPureApplication::intern(
                    application.name().to_owned(),
                    application.arguments().iter().map(&mut argument).collect(),
                ))
            }
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => Self::BoolIf {
                condition: Box::new(child(condition)),
                then_condition: Box::new(child(then_condition)),
                else_condition: Box::new(child(else_condition)),
            },
            Self::BoolEqual(left, right) => {
                Self::BoolEqual(Box::new(child(left)), Box::new(child(right)))
            }
            Self::BoolLoad(memory, pointer) => {
                let (memory, pointer) = read(memory, pointer);
                Self::BoolLoad(memory, Box::new(pointer))
            }
            _ => return None,
        })
    }
}

impl crate::kernel::Bitvector32Term {
    /// Rule C1: the integer value of the `Bool` `value` at format `to`,
    /// `value as to`. A constant folds to its word, 1 or 0; nothing else is
    /// read.
    pub(crate) fn bool_cast(to: crate::kernel::MachineIntegerType, value: ConditionTerm) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match value {
            ConditionTerm::Constant(value) => Self::Constant(u32::from(value)),
            value => Self::BoolCast {
                to,
                value: Box::new(value),
            },
        }
    }

    /// The `Bool` whose integer value this term is (rule C1), or `None`.
    pub(crate) fn bool_cast_operand(&self) -> Option<&ConditionTerm> {
        match self {
            Self::BoolCast { value, .. } => Some(value),
            _ => None,
        }
    }
}

impl ConditionTerm {
    /// The `Bool` a `CValue::Bool` word carries. A specification `Bool`
    /// travels as its cast `b as uint8` (rule C1), whose operand is `b`; a
    /// constant is its truth; and any other word, a C `bool` value this
    /// stage still holds as an integer, reaches `Bool` by C's test
    /// `w != 0`.
    pub(crate) fn truth_of_bool_word(word: &crate::kernel::Bitvector32Term) -> Self {
        use crate::kernel::Bitvector32Term;
        if let Some(value) = word.bool_cast_operand() {
            return value.clone();
        }
        match word {
            Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
                Self::Constant(*value != 0)
            }
            word => Self::bool_if(
                Self::equal(word.clone(), Bitvector32Term::Constant(0)),
                Self::Constant(false),
                Self::Constant(true),
            ),
        }
    }
}
