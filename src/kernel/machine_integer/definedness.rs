//! Structural adapters between ordinary exact-result bounds and the private
//! overflow queries used by existing interval reasoning. Generated arithmetic
//! domains are ordinary propositions; these adapters never file an opaque
//! overflow fact or alter a lowered term.
//! A single bound identifies a candidate query, but only both bounds establish
//! representability. Unsigned overflow remains wrapping arithmetic.

use super::{FORMATS, Operation, comparison::ComparisonOperand, range, representation};
#[cfg(test)]
use crate::kernel::Bitvector32Term;
use crate::kernel::{ConditionTerm, IntegerTerm, MachineIntegerType, Proposition};

/// The formats whose definedness facts the kernel files, narrowest first:
/// those where C arithmetic's overflow is undefined behavior
/// (`representation::files_definedness`).
pub(crate) fn defined_formats() -> impl Iterator<Item = MachineIntegerType> {
    FORMATS
        .into_iter()
        .filter(|ty| representation::files_definedness(*ty))
}

/// The two Integer bounds a definedness fact is exactly equivalent to:
/// `defined(a + b)` on `int32` holds exactly when
/// `to_integer(a) + to_integer(b) <= 2147483647` and
/// `to_integer(a) + to_integer(b) >= -2147483648`, and likewise for `-`
/// and `*` and for every format with an overflow test. A refutation may
/// read the definedness fact as these bounds
/// ([`definedness_of_integer_bound`] checks a listed one).
pub(crate) fn integer_bounds_of_definedness(proposition: &Proposition) -> Vec<Proposition> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return Vec::new();
    };
    let Some((ty, operation, left, right)) = representation::overflow_operation(condition) else {
        return Vec::new();
    };
    let (Some(left), Some(right)) = (
        IntegerTerm::from_machine(ty, left.clone()),
        IntegerTerm::from_machine(ty, right.clone()),
    ) else {
        return Vec::new();
    };
    ordinary_bounds(ty, operation.exact(left, right)).into()
}

pub(crate) fn ordinary_bounds(format: MachineIntegerType, exact: IntegerTerm) -> [Proposition; 2] {
    let (minimum, maximum) = range::range(format);
    [
        Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(exact.clone(), IntegerTerm::constant(maximum)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::integer_greater_equal(exact, IntegerTerm::constant(minimum)),
            true,
        ),
    ]
}

/// The definedness fact whose Integer bound
/// ([`integer_bounds_of_definedness`]) is exactly `bound`, if any, at a
/// format whose definedness facts are filed ([`defined_formats`]). The
/// candidate is recomputed through the forward map, so only an exact
/// reading is accepted.
pub(crate) fn definedness_of_integer_bound(bound: &Proposition) -> Option<Proposition> {
    overflow_fact_of_integer_bound(bound, defined_formats())
}

/// The fact `not Overflows(F, op, a, b)`, for `F` among `formats`, whose
/// Integer bound ([`integer_bounds_of_definedness`]) is exactly `bound`,
/// if any: the converse of the equivalence, at any format.
pub(crate) fn overflow_fact_of_integer_bound(
    bound: &Proposition,
    formats: impl Iterator<Item = MachineIntegerType>,
) -> Option<Proposition> {
    let query = overflow_query_of_integer_bound(bound, formats)?;
    Some(Proposition::ConditionIs(query.boxed_condition()?, false))
}

/// Private query over the original operand handles. Ordinary bounds remain
/// the facts; materializing a legacy condition is a compatibility output only.
#[derive(Clone)]
pub(crate) struct OverflowQueryView {
    pub(crate) format: MachineIntegerType,
    pub(crate) operation: Operation,
    pub(crate) operands: [ComparisonOperand<'static>; 2],
    exact: IntegerTerm,
}

impl OverflowQueryView {
    pub(crate) fn from_operands(
        format: MachineIntegerType,
        operation: Operation,
        operands: [crate::kernel::MachineOperandView<'_>; 2],
    ) -> Option<Self> {
        if !representation::has_overflow_test(format) {
            return None;
        }
        let exact = operation.exact(operands[0].observe(format)?, operands[1].observe(format)?);
        Some(Self {
            format,
            operation,
            operands: operands.map(|operand| match operand {
                crate::kernel::MachineOperandView::Legacy(term) => {
                    ComparisonOperand::Constant(term.clone())
                }
                crate::kernel::MachineOperandView::Shared(_) => {
                    ComparisonOperand::Observation(operand.retain(format))
                }
            }),
            exact,
        })
    }
    pub(crate) fn operation_kind(&self) -> crate::kernel::OverflowOperation {
        match self.operation {
            Operation::Add => crate::kernel::OverflowOperation::Add,
            Operation::Subtract => crate::kernel::OverflowOperation::Subtract,
            Operation::Multiply => crate::kernel::OverflowOperation::Multiply,
        }
    }

    pub(crate) fn bounds(&self) -> [Proposition; 2] {
        ordinary_bounds(self.format, self.exact.clone())
    }

    fn boxed_condition(&self) -> Option<ConditionTerm> {
        representation::overflow_condition(
            self.format,
            self.operation,
            Box::new(self.operands[0].boxed_value().clone()),
            Box::new(self.operands[1].boxed_value().clone()),
        )
    }
}

pub(crate) fn overflow_query_of_integer_bound(
    bound: &Proposition,
    formats: impl Iterator<Item = MachineIntegerType>,
) -> Option<OverflowQueryView> {
    let Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(first, second)
        | ConditionTerm::IntegerGreaterEqual(first, second),
        true,
    ) = bound
    else {
        return None;
    };
    let exact = if Operation::of_exact(first).is_some() {
        first
    } else {
        second
    };
    let (operation, left, right) = Operation::of_exact(exact)?;
    if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
        return None;
    }
    let carrier =
        |ty: MachineIntegerType, side: &IntegerTerm| -> Option<ComparisonOperand<'static>> {
            match side {
                IntegerTerm::Machine(machine) => {
                    let view = machine.operand_view();
                    if machine.ty().format().bits() == ty.format().bits()
                        && view.observe(ty).as_ref() == Some(side)
                    {
                        return Some(ComparisonOperand::Observation(view.retain(ty)));
                    }
                    let widened = machine.cast_operand(ty);
                    (widened.operand_view().observe(ty).as_ref() == Some(side))
                        .then_some(ComparisonOperand::Observation(widened))
                }
                IntegerTerm::Constant(value) => {
                    range::constant_word(ty, value).map(ComparisonOperand::Constant)
                }
                _ => None,
            }
        };
    formats
        .filter(|ty| representation::has_overflow_test(*ty))
        .find_map(|format| {
            let operands = [carrier(format, left)?, carrier(format, right)?];
            let query = OverflowQueryView {
                format,
                operation,
                operands,
                exact: exact.as_ref().clone(),
            };
            query
                .bounds()
                .iter()
                .any(|expected| same_integer_bound(expected, bound))
                .then_some(query)
        })
}

/// The two order spellings of an ordinary bound are the same proposition.
/// This is comparison matching, never a change to either stored term.
fn same_integer_bound(left: &Proposition, right: &Proposition) -> bool {
    left == right
        || matches!((left, right),
        (Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true),
         Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(c, d), true)) |
        (Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(a, b), true),
         Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(c, d), true))
        if a == d && b == c)
}

/// Read one explicitly supplied ordinary range conjunction as an arithmetic
/// query. This is a structural adapter for existing interval certificates;
/// it neither adds an overflow fact nor searches the context for bounds.
pub(crate) fn ordinary_arithmetic_guard(proposition: &Proposition) -> Option<ConditionTerm> {
    ordinary_arithmetic_guard_view(proposition)?.boxed_condition()
}

pub(crate) fn ordinary_arithmetic_guard_view(
    proposition: &Proposition,
) -> Option<OverflowQueryView> {
    let Proposition::And(first, second) = proposition else {
        return None;
    };
    let query = overflow_query_of_integer_bound(first, defined_formats())?;
    let [upper, lower] = query.bounds();
    ((same_integer_bound(first, &upper) && same_integer_bound(second, &lower))
        || (same_integer_bound(first, &lower) && same_integer_bound(second, &upper)))
    .then_some(query)
}

/// Read a complete ordinary range domain or an explicitly written legacy
/// nonoverflow condition, retaining the operand handles in either case.
pub(crate) fn range_domain_query(proposition: &Proposition) -> Option<OverflowQueryView> {
    if let Some(query) = ordinary_arithmetic_guard_view(proposition) {
        return Some(query);
    }
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    let (format, operation, left, right) = representation::overflow_operation(condition)?;
    OverflowQueryView::from_operands(
        format,
        operation,
        [
            crate::kernel::MachineOperandView::Legacy(left),
            crate::kernel::MachineOperandView::Legacy(right),
        ],
    )
}

/// Private input form for the existing interval proof rules. Stored facts,
/// obligations and certificate results keep the ordinary propositions. This
/// adapter reads only the explicit proposition, never the ambient context.
pub(crate) fn interval_query_form(proposition: &Proposition) -> Option<Proposition> {
    if let Some(condition) = ordinary_arithmetic_guard(proposition) {
        return Some(Proposition::ConditionIs(condition, false));
    }
    if let Proposition::And(left, right) = proposition {
        let a = interval_query_form(left);
        let b = interval_query_form(right);
        if a.is_some() || b.is_some() {
            return Some(Proposition::And(
                Box::new(a.unwrap_or_else(|| *left.clone())),
                Box::new(b.unwrap_or_else(|| *right.clone())),
            ));
        }
    }
    None
}

#[cfg(test)]
mod shared_query_tests {
    use super::*;
    fn legacy_overflow_query(
        bound: &Proposition,
        formats: impl Iterator<Item = MachineIntegerType>,
    ) -> Option<Proposition> {
        let Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(first, second)
            | ConditionTerm::IntegerGreaterEqual(first, second),
            true,
        ) = bound
        else {
            return None;
        };
        // The comparison constructors may put the constant on either side.
        let exact = if Operation::of_exact(first).is_some() {
            first
        } else {
            second
        };
        let (_, left, right) = Operation::of_exact(exact)?;
        // An operand is an observation in the operation's format, or a
        // constant, which the forward map produces for a literal operand such
        // as `x + 1`. An `int32` observation of a narrow load or of a widened
        // narrow value reads as the narrow format's
        // (`IntegerTerm::from_machine`), so an operand's word is the one, as
        // written or widened, whose observation in the format gives the
        // operand back.
        let carrier = |ty: MachineIntegerType, side: &IntegerTerm| -> Option<Bitvector32Term> {
            match side {
                IntegerTerm::Machine(machine) => {
                    let word = machine.value().clone();
                    let widened = Bitvector32Term::MachineIntegerCast {
                        value: Box::new(word.clone()),
                        source: machine.ty(),
                        destination: ty,
                    };
                    // A value of another width is never `ty`'s word as written:
                    // its word in `ty` is its widening, a node of its own.
                    let as_written =
                        (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                    as_written.into_iter().chain([widened]).find(|word| {
                        IntegerTerm::from_machine(ty, word.clone()).as_ref() == Some(side)
                    })
                }
                IntegerTerm::Constant(value) => range::constant_word(ty, value),
                _ => None,
            }
        };
        if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
            return None;
        }
        formats
            .filter_map(|ty| {
                let (a, b) = (Box::new(carrier(ty, left)?), Box::new(carrier(ty, right)?));
                Some(Operation::ALL.map(|operation| {
                    representation::overflow_condition(ty, operation, a.clone(), b.clone())
                }))
            })
            .flatten()
            .flatten()
            .find_map(|condition| {
                let fact = Proposition::ConditionIs(condition, false);
                integer_bounds_of_definedness(&fact)
                    .iter()
                    .any(|expected| same_integer_bound(expected, bound))
                    .then_some(fact)
            })
    }

    #[test]
    fn shared_overflow_queries_preserve_the_legacy_reverse_map() {
        use crate::kernel::{MachineBinaryOp, Variable};
        let _session = crate::kernel::VerificationSession::enter();
        for format in FORMATS {
            let variable = Bitvector32Term::Variable(Variable(982201));
            let words = [
                variable.clone(),
                Bitvector32Term::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(variable.clone()),
                    right: Box::new(variable.clone()),
                },
                Bitvector32Term::MachineIntegerCast {
                    source: MachineIntegerType::Int32,
                    destination: format,
                    value: Box::new(variable),
                },
            ];
            for word in words {
                let Some(observed) = IntegerTerm::from_machine(format, word) else {
                    continue;
                };
                for operation in Operation::ALL {
                    let exact = operation.exact(observed.clone(), IntegerTerm::constant(1.into()));
                    for bounds_format in FORMATS {
                        let (min, max) = range::range(bounds_format);
                        for bound in [
                            Proposition::ConditionIs(
                                ConditionTerm::integer_less_equal(
                                    exact.clone(),
                                    IntegerTerm::constant(max),
                                ),
                                true,
                            ),
                            Proposition::ConditionIs(
                                ConditionTerm::integer_greater_equal(
                                    exact.clone(),
                                    IntegerTerm::constant(min),
                                ),
                                true,
                            ),
                        ] {
                            assert_eq!(
                                overflow_fact_of_integer_bound(&bound, FORMATS.into_iter()),
                                legacy_overflow_query(&bound, FORMATS.into_iter()),
                                "{format:?} {operation:?}: {bound:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/machine_integer/definedness/tests.rs");
    }
}
