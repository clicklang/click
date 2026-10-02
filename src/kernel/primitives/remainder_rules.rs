//! Local Euclidean remainder identities for machine integers. Every signed
//! identity carries nonnegative, non-wrapping guards; uint64 divisors are
//! checked at their full width.
use super::{Bitvector32Term as B, ConditionTerm as C};

impl C {
    pub(crate) fn uint64_remainder_bound_guard(&self) -> Option<Self> {
        let (left, right, strict) = match self {
            C::Bitvector64UnsignedLessEqual(a, b) => (a.as_ref(), b.as_ref(), false),
            C::Bitvector64UnsignedLessThan(a, b) => (a.as_ref(), b.as_ref(), true),
            _ => return None,
        };
        let B::UInt64Remainder(n, d) = left else {
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
            B::UInt64Remainder(_, d) if d.uint64_as_const() == Some(1) => {
                Some((Vec::new(), B::UInt64Constant(0)))
            }
            B::Remainder(_, d) if d.as_const() == Some(1) => Some((Vec::new(), B::Constant(0))),
            B::Remainder(n, d) => {
                let k = d.as_const()? as i32;
                if k <= 0 {
                    return None;
                }
                if let B::UInt32From64(wide) = n.as_ref()
                    && let B::UInt64Subtract(original, tail) = wide.as_ref()
                    && let B::UInt64Remainder(other_original, other_d) = tail.as_ref()
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
                if let B::Subtract(original, step) = n.as_ref()
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

    #[test]
    fn remainder_guard_lookup_ignores_unrelated_conditions() {
        let n = B::Variable(Variable(100));
        let input = B::remainder(B::subtract(n.clone(), B::Constant(4)), B::Constant(4));
        let guard = C::signed_less_equal(B::Constant(4), n.clone());
        let mut measured = Vec::new();
        for count in [0, 32, 128, 512] {
            let mut facts = HashMap::from([(guard.clone(), true)]);
            for i in 0..count {
                facts.insert(
                    C::equal(B::Variable(Variable(1000 + i)), B::Constant(i as u32)),
                    true,
                );
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                TermRewrite::for_conditions(&facts).bits(&input)
            });
            assert_eq!(result, B::remainder(n.clone(), B::Constant(4)));
            measured.push(work);
        }
        assert!(
            measured.iter().all(|work| *work == measured[0]),
            "{measured:?}"
        );
    }
}
