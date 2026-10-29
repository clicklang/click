//! Local Euclidean remainder identities for machine integers. Every signed
//! identity carries nonnegative, non-wrapping guards; uint64 divisors are
//! checked at their full width.
use super::{Bitvector32Term as B, ConditionTerm as C};
use crate::kernel::MachineBinaryOp;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};

impl C {
    /// In the nonnegative signed-word range, both signed and unsigned
    /// quotient/remainder results stay nonnegative and below the dividend.
    /// The divisor must be strictly positive; no zero/negative case is used.
    pub(crate) fn nonnegative_division_bound_guards(&self) -> Option<Vec<Self>> {
        let (left, right) = match self {
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => (left, right),
            C::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => (right, left),
            _ => return None,
        };
        let (result, upper) = if left.as_const() == Some(0) {
            (right.as_ref(), None)
        } else {
            (left.as_ref(), Some(right.as_ref()))
        };
        let (n, d) = match result {
            binary_term!(Int32, Divide, n, d)
            | binary_term!(UInt32, Divide, n, d)
            | binary_term!(Int32, Remainder, n, d)
            | binary_term!(UInt32, Remainder, n, d) => (n, d),
            _ => return None,
        };
        let mut guards = vec![
            C::signed_less_equal(B::Constant(0), n.as_ref().clone()),
            C::signed_less_than(B::Constant(0), d.as_ref().clone()),
        ];
        if let Some(upper) = upper
            && n.as_ref() != upper
        {
            guards.push(C::signed_less_equal(n.as_ref().clone(), upper.clone()));
        }
        Some(guards)
    }

    pub(crate) fn uint64_remainder_bound_guard(&self) -> Option<Self> {
        let (left, right, strict) = match self {
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (a.as_ref(), b.as_ref(), false),
            C::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (a.as_ref(), b.as_ref(), true),
            _ => return None,
        };
        let B::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Remainder,
            left: n,
            right: d,
        } = left
        else {
            return None;
        };
        if (!strict && n.as_ref() == right) || (strict && d.as_ref() == right) {
            Some(C::uint64_less_than(
                B::UInt64Constant(0),
                d.as_ref().clone(),
            ))
        } else {
            None
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
            } if d.uint64_as_const() == Some(1) => Some((Vec::new(), B::UInt64Constant(0))),
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
                Some((Vec::new(), B::UInt64Constant(0)))
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
                Some((Vec::new(), B::Constant(0)))
            }
            binary_term!(Int32, Remainder, n, d) => {
                let k = d.as_const()? as i32;
                if k <= 0 {
                    return None;
                }
                if let B::UInt32From64(wide) = n.as_ref()
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
                            B::UInt64Constant(i32::MAX as u64),
                        )],
                        B::Constant(0),
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
                        C::signed_less_equal(B::Constant(0), n.as_ref().clone()),
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
                C::signed_less_equal(B::Constant(0), result.clone()),
                C::signed_less_equal(result, B::Constant(65535)),
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
        let d = B::Constant(4);
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

        let wide_d = B::UInt64Constant(4);
        let complete = B::uint32_from_64(B::uint64_subtract(
            n.clone(),
            B::uint64_remainder(n.clone(), wide_d),
        ));
        let input = B::remainder(complete, B::Constant(4));
        let guard = C::uint64_less_equal(n.clone(), B::UInt64Constant(i32::MAX as u64));
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::new()).bits(&input),
            input
        );
        assert_eq!(
            TermRewrite::for_conditions(&HashMap::from([(guard, true)])).bits(&input),
            B::Constant(0)
        );

        for divisor in [0u32, u32::MAX] {
            let input = B::remainder(
                B::subtract(n.clone(), B::Constant(divisor)),
                B::Constant(divisor),
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
        let input = B::remainder(n.clone(), B::Constant(4));
        let lower = C::signed_less_equal(B::Constant(0), n.clone());
        let upper = C::signed_less_than(n.clone(), B::Constant(4));
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
