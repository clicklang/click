//! Local Euclidean remainder identities for machine integers. Every signed
//! identity carries nonnegative, non-wrapping guards; uint64 divisors are
//! checked at their full width.
use super::{Bitvector32Term as B, ConditionTerm as C};
use crate::kernel::MachineBinaryOp;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, cast_term};

impl C {
    /// In the nonnegative signed-word range, both signed and unsigned
    /// quotient/remainder results stay nonnegative and below the dividend.
    /// The divisor must be strictly positive; no zero/negative case is used.
    pub(crate) fn nonnegative_division_bound_guards(&self) -> Option<Vec<Self>> {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{
                comparison_view, condition_for_operand_views, structural_native_comparison_view,
            },
        };
        let view = if matches!(self, C::Compare { .. }) {
            comparison_view(self, true)?
        } else {
            structural_native_comparison_view(self, true)?
        };
        if view.format != MachineIntegerType::Int32 || view.relation != Relation::LessEqual {
            return None;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let (result, upper) = if left.word32_constant() == Some(0) {
            (right, None)
        } else {
            (left, Some(right))
        };
        let cast_operands;
        let [n, d] = if let Some((_, _, operands)) = division_operands(result) {
            operands
        } else {
            use crate::kernel::MachineCastSpelling as Encoding;
            let (Encoding::Generic, source, destination, operand) = result.cast()? else {
                return None;
            };
            if source != MachineIntegerType::UInt32 || destination != MachineIntegerType::Int32 {
                return None;
            }
            let (format, _, operands) = division_operands(operand)?;
            if format != source {
                return None;
            }
            cast_operands = operands.map(|operand| signed_division_guard_operand(operand));
            cast_operands.each_ref().map(DivisionGuardOperand::view)
        };
        let compare = |relation, a, b| {
            condition_for_operand_views(MachineIntegerType::Int32, relation, [a, b])
        };
        let zero = B::constant(0);
        let mut guards = vec![
            compare(CompareRelation::LessEqual, V::Legacy(&zero), n),
            compare(CompareRelation::LessThan, V::Legacy(&zero), d),
        ];
        if let Some(upper) = upper
            && !same_division_guard_operand(n, upper)
        {
            guards.push(compare(CompareRelation::LessEqual, n, upper));
        }
        Some(guards)
    }
}

fn same_division_guard_operand(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> bool {
    use crate::kernel::{KernelTermImport, MachineOperandView as V};
    match (left, right) {
        (V::Legacy(a), V::Legacy(b)) => a == b,
        (V::Shared(a), V::Shared(b)) => {
            a.with_machine_observation_type(MachineIntegerType::Int32)
                == b.with_machine_observation_type(MachineIntegerType::Int32)
        }
        (V::Shared(shared), V::Legacy(native)) | (V::Legacy(native), V::Shared(shared)) => {
            KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, native)
                .as_ref()
                == Some(&shared.with_machine_observation_type(MachineIntegerType::Int32))
        }
    }
}

fn division_operands(
    value: crate::kernel::MachineOperandView<'_>,
) -> Option<(
    MachineIntegerType,
    MachineBinaryOp,
    [crate::kernel::MachineOperandView<'_>; 2],
)> {
    value.binary().filter(|(format, op, _)| {
        matches!(
            format,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32
        ) && matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::Remainder)
    })
}

enum DivisionGuardOperand {
    Native(B),
    Shared(crate::kernel::SharedMachineIntegerTerm),
}
impl DivisionGuardOperand {
    fn view(&self) -> crate::kernel::MachineOperandView<'_> {
        match self {
            Self::Native(value) => crate::kernel::MachineOperandView::Legacy(value),
            Self::Shared(value) => value.operand_view(),
        }
    }
}

// Preserve the native checking constructor's constant and cast-composition
// conventions. This is a checking premise, not a rewrite of a stored term.
fn signed_division_guard_operand(
    operand: crate::kernel::MachineOperandView<'_>,
) -> DivisionGuardOperand {
    use crate::kernel::MachineOperandView as V;
    use MachineIntegerType::{Int32, UInt32};
    match operand {
        V::Legacy(value) => {
            DivisionGuardOperand::Native(B::sign_cast32(UInt32, Int32, value.clone()))
        }
        V::Shared(_) => {
            DivisionGuardOperand::Shared(operand.retain(UInt32).checking_cast_operand(Int32))
        }
    }
}

impl B {
    pub(crate) fn guarded_remainder_rewrite(&self) -> Option<(Vec<C>, Self)> {
        match self {
            B::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: _,
                right: d,
            } if d.uint64_as_const() == Some(1) => Some((Vec::new(), B::uint64_constant(0))),
            // `n - n % d` is a multiple of `d`: the difference does not wrap,
            // since a remainder is at most its dividend.
            B::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: n,
                right: d,
            } if d.uint64_as_const().is_some_and(|d| d != 0)
                && matches!(
                    n.as_ref(),
                    B::Binary { format: MachineIntegerType::UInt64, op: MachineBinaryOp::Subtract, left: original, right: tail }
                        if matches!(
                            tail.as_ref(),
                            B::Binary { format: MachineIntegerType::UInt64, op: MachineBinaryOp::Remainder, left: tail_original, right: tail_d }
                                if tail_original == original && tail_d == d
                        )
                ) =>
            {
                Some((Vec::new(), B::uint64_constant(0)))
            }
            // `(n - d) % d` is `n % d` when `d <= n`, where the difference
            // does not wrap.
            B::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: n,
                right: d,
            } if d.uint64_as_const().is_some_and(|d| d != 0)
                && matches!(n.as_ref(), B::Binary { format: MachineIntegerType::UInt64, op: MachineBinaryOp::Subtract, left: _, right: step } if step == d) =>
            {
                let B::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Subtract,
                    left: original,
                    right: _,
                } = n.as_ref()
                else {
                    unreachable!("matched above")
                };
                Some((
                    vec![C::uint64_less_equal(
                        d.as_ref().clone(),
                        original.as_ref().clone(),
                    )],
                    B::uint64_remainder(original.as_ref().clone(), d.as_ref().clone()),
                ))
            }
            B::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: n,
                right: d,
            } => Some((
                vec![C::uint64_less_than(n.as_ref().clone(), d.as_ref().clone())],
                n.as_ref().clone(),
            )),
            binary_term!(Int32, Remainder, _, d) if d.as_const() == Some(1) => {
                Some((Vec::new(), B::constant(0)))
            }
            binary_term!(Int32, Remainder, n, d) => {
                let k = d.as_const()? as i32;
                if k <= 0 {
                    return None;
                }
                // The low word is a word of no signedness; σ of it, `x as
                // uint32 as int32`, has its bits.
                let low = match n.as_ref() {
                    B::Cast {
                        spelling: MachineCastSpelling::Generic,
                        value,
                        from: MachineIntegerType::UInt32,
                        to: MachineIntegerType::Int32,
                    } => value.as_ref(),
                    n => n,
                };
                if let cast_term!(UInt32From64, wide) = low
                    && let B::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Subtract,
                        left: original,
                        right: tail,
                    } = wide.as_ref()
                    && let B::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Remainder,
                        left: other_original,
                        right: other_d,
                    } = tail.as_ref()
                    && original == other_original
                    && other_d.uint64_as_const() == Some(k as u64)
                {
                    return Some((
                        vec![C::uint64_less_equal(
                            original.as_ref().clone(),
                            B::uint64_constant(i32::MAX as u64),
                        )],
                        B::constant(0),
                    ));
                }
                if let binary_term!(Int32, Subtract, original, step) = n.as_ref()
                    && step == d
                {
                    return Some((
                        vec![C::signed_less_equal(
                            d.as_ref().clone(),
                            original.as_ref().clone(),
                        )],
                        B::remainder(original.as_ref().clone(), d.as_ref().clone()),
                    ));
                }
                Some((
                    vec![
                        C::signed_less_equal(B::constant(0), n.as_ref().clone()),
                        C::signed_less_than(n.as_ref().clone(), d.as_ref().clone()),
                    ],
                    n.as_ref().clone(),
                ))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;
    use crate::kernel::proof::term_rewrite::TermRewrite;
    use std::collections::HashMap;

    #[test]
    fn shared_division_bounds_keep_native_guard_shapes_without_exports() {
        use crate::kernel::machine_integer::comparison::{
            condition_for_operand_views, structural_native_comparison_of_integer_observation,
        };
        use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};
        let _session = crate::kernel::VerificationSession::enter();
        let n = B::add(B::Variable(Variable(990101)), B::Variable(Variable(990102)));
        let d = B::add(B::Variable(Variable(990103)), B::constant(1));
        let narrow = B::machine_integer_cast(
            MachineIntegerType::UInt16,
            MachineIntegerType::UInt32,
            B::Variable(Variable(990104)),
        );
        for n in [n, narrow, B::constant(5)] {
            for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
                for op in [MachineBinaryOp::Divide, MachineBinaryOp::Remainder] {
                    let result = B::Binary {
                        format,
                        op,
                        left: Box::new(n.clone()),
                        right: Box::new(d.clone()),
                    };
                    let mut results = vec![result.clone()];
                    if format == MachineIntegerType::UInt32 {
                        results.push(B::sign_cast32(format, MachineIntegerType::Int32, result));
                    }
                    for result in results {
                        for (left, right) in [
                            (B::constant(0), result.clone()),
                            (result.clone(), n.clone()),
                            (result, B::constant(99)),
                        ] {
                            for relation in [
                                CompareRelation::LessEqual,
                                CompareRelation::GreaterEqual,
                                CompareRelation::LessThan,
                                CompareRelation::Equal,
                            ] {
                                let native = C::machine_compare(
                                    MachineIntegerType::Int32,
                                    relation,
                                    left.clone(),
                                    right.clone(),
                                );
                                let expected = native.nonnegative_division_bound_guards();
                                let [a, b] = [&left, &right].map(|term| {
                                    KernelTermImport::default()
                                        .machine_arithmetic(MachineIntegerType::Int32, term)
                                        .unwrap()
                                });
                                let shared = condition_for_operand_views(
                                    MachineIntegerType::Int32,
                                    relation,
                                    [V::Shared(&a), V::Shared(&b)],
                                );
                                let exports = KernelTermExport::machine_export_count();
                                let actual = shared.nonnegative_division_bound_guards();
                                assert_eq!(KernelTermExport::machine_export_count(), exports);
                                let actual = actual.map(|guards| {
                                    guards
                                        .into_iter()
                                        .map(|condition| {
                                            structural_native_comparison_of_integer_observation(
                                                &condition, true,
                                            )
                                            .map(|(native, truth)| {
                                                assert!(truth);
                                                native
                                            })
                                            .unwrap_or(condition)
                                        })
                                        .collect::<Vec<_>>()
                                });
                                assert_eq!(actual, expected, "{native:?}");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn quotient_and_remainder_bounds_need_every_signed_range_guard() {
        let n = B::Variable(Variable(100));
        let d = B::Variable(Variable(101));
        for result in [
            binary_node!(Int32, Divide, Box::new(n.clone()), Box::new(d.clone())),
            binary_node!(UInt32, Divide, Box::new(n.clone()), Box::new(d.clone())),
            binary_node!(Int32, Remainder, Box::new(n.clone()), Box::new(d.clone())),
            binary_node!(UInt32, Remainder, Box::new(n.clone()), Box::new(d.clone())),
        ] {
            for goal in [
                C::signed_less_equal(B::constant(0), result.clone()),
                C::signed_less_equal(result, B::constant(65535)),
            ] {
                let guards = goal.nonnegative_division_bound_guards().unwrap();
                let facts: HashMap<_, _> =
                    guards.iter().cloned().map(|guard| (guard, true)).collect();
                assert_eq!(
                    TermRewrite::for_conditions(&facts).condition(&goal),
                    C::Constant(true)
                );
                for omitted in &guards {
                    let mut missing = facts.clone();
                    missing.remove(omitted);
                    assert_ne!(
                        TermRewrite::for_conditions(&missing).condition(&goal),
                        C::Constant(true)
                    );
                    missing.insert(omitted.clone(), false);
                    assert_ne!(
                        TermRewrite::for_conditions(&missing).condition(&goal),
                        C::Constant(true)
                    );
                }
            }
        }
    }

    #[test]
    fn remainder_rewrites_require_nonnegative_and_full_width_guards() {
        let n = B::Variable(Variable(100));
        let d = B::constant(4);
        let input = B::remainder(B::subtract(n.clone(), d.clone()), d.clone());
        let guard = C::signed_less_equal(d.clone(), n.clone());
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::new()).bits(&input),
            input
        );
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::from([(guard.clone(), false)])).bits(&input),
            input
        );
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::from([(guard, true)])).bits(&input),
            B::remainder(n.clone(), d)
        );

        let wide_d = B::uint64_constant(4);
        let complete = B::uint32_from_64(B::uint64_subtract(
            n.clone(),
            B::uint64_remainder(n.clone(), wide_d),
        ));
        let input = B::remainder(complete, B::constant(4));
        let guard = C::uint64_less_equal(n.clone(), B::uint64_constant(i32::MAX as u64));
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::new()).bits(&input),
            input
        );
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::from([(guard, true)])).bits(&input),
            B::constant(0)
        );

        for divisor in [0u32, u32::MAX] {
            let input = B::remainder(
                B::subtract(n.clone(), B::constant(divisor)),
                B::constant(divisor),
            );
            assert_eq!(
                TermRewrite::for_conditions(&HashMap::new()).bits(&input),
                input
            );
        }
    }

    #[test]
    fn remainder_small_dividend_needs_both_signed_bounds() {
        let n = B::Variable(Variable(100));
        let input = B::remainder(n.clone(), B::constant(4));
        let lower = C::signed_less_equal(B::constant(0), n.clone());
        let upper = C::signed_less_than(n.clone(), B::constant(4));
        for facts in [
            HashMap::new(),
            HashMap::from([(lower.clone(), true)]),
            HashMap::from([(upper.clone(), true)]),
        ] {
            assert_eq!(TermRewrite::for_conditions(&facts).bits(&input), input);
        }
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::from([(lower, true), (upper, true)]))
                .bits(&input),
            n
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/remainder_rules/tests.rs");
    }
}
