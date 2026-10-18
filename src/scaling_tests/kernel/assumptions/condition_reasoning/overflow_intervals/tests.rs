// Scaling tests of `src/kernel/assumptions/condition_reasoning/overflow_intervals.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn widened_unsigned_sum_bounds_are_sound_and_flat_in_unrelated_facts() {
    let a = Bitvector32Term::Variable(Variable(97001));
    let b = Bitvector32Term::Variable(Variable(97002));
    let sum = Bitvector32Term::int64_add(
        Bitvector32Term::int64_from_uint32(a.clone()),
        Bitvector32Term::int64_from_uint32(b.clone()),
    );
    let goal = ConditionTerm::int64_signed_less_equal(
        sum.clone(),
        Bitvector32Term::Int64Constant(u32::MAX as i64),
    );
    let too_small = ConditionTerm::int64_signed_less_equal(
        sum,
        Bitvector32Term::Int64Constant(u32::MAX as i64 - 1),
    );
    let mut works = Vec::new();
    for size in [8, 32, 128] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::unsigned_less_equal(
                    Bitvector32Term::Variable(Variable(98000 + index)),
                    Bitvector32Term::Constant(123),
                ),
                true,
            );
        }
        facts = facts
            .assume_condition(
                ConditionTerm::unsigned_less_equal(
                    a.clone(),
                    Bitvector32Term::Constant(u32::MAX - 255),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(b.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(b.clone(), Bitvector32Term::Constant(255)),
                true,
            );
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.decide_widened_sum_bound(&goal)
        });
        assert_eq!(answer, Some(true));
        assert_eq!(facts.decide_widened_sum_bound(&too_small), None);
        let selected = facts.widened_unsigned_sum_bound_premises(&goal).unwrap();
        let selected_context = selected
            .iter()
            .fold(PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            });
        assert_eq!(selected_context.decide_widened_sum_bound(&goal), Some(true));
        use crate::kernel::proof::arithmetic_special::{
            SpecialArithmeticCertificate, SpecialArithmeticNode,
        };
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                bounds: (0..selected.len()).collect(),
                result: Proposition::ConditionIs(goal.clone(), true),
            }],
            conclusion: 0,
        };
        certificate
            .check(&Proposition::ConditionIs(goal.clone(), true), &selected)
            .unwrap();
        let forged = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                bounds: (0..selected.len()).collect(),
                result: Proposition::ConditionIs(too_small.clone(), true),
            }],
            conclusion: 0,
        };
        assert!(
            forged
                .check(
                    &Proposition::ConditionIs(too_small.clone(), true),
                    &selected
                )
                .is_err()
        );
        let invalid =
            ConditionTerm::unsigned_greater_equal(b.clone(), Bitvector32Term::Constant(256));
        // The signed byte facts alone do not index the biased operand.
        let facts = facts.assume_condition(
            ConditionTerm::unsigned_less_than(b.clone(), Bitvector32Term::Constant(8)),
            true,
        );
        let (answer, order_work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.decide_indexed_greater_equal(&invalid)
        });
        assert_eq!(answer, Some(false));
        works.push(work + order_work);
    }
    assert!(works.iter().all(|work| *work == works[0]), "{works:?}");
    let unknown = PureFactContext::new();
    assert_eq!(unknown.decide_widened_sum_bound(&goal), None);
}

/// The `int32_defined` / `int64_defined` closer selects each operand's
/// constant bounds by keyed lookup. Its deterministic work must be flat
/// in the number of unrelated constant-bound facts of either width, and
/// the selected facts must satisfy the kernel checker.
#[test]
fn signed_constant_bound_selection_is_flat_in_unrelated_bounds() {
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    for width in [SignedDefinedWidth::Int32, SignedDefinedWidth::Int64] {
        let constant = |value: i64| match width {
            SignedDefinedWidth::Int32 => Bitvector32Term::Constant(value as i32 as u32),
            SignedDefinedWidth::Int64 => Bitvector32Term::Int64Constant(value),
        };
        let less = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::signed_less_than(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_less_than(left, right),
        };
        let at_least = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::signed_greater_equal(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_greater_equal(left, right),
        };
        let equal = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::equal(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_equal(left, right),
        };
        let a = Bitvector32Term::Variable(Variable(94_001));
        let b = Bitvector32Term::Variable(Variable(94_002));
        let goal = Proposition::ConditionIs(
            match width {
                SignedDefinedWidth::Int32 => ConditionTerm::Bitvector32SignedAddOverflows(
                    Box::new(a.clone()),
                    Box::new(b.clone()),
                ),
                SignedDefinedWidth::Int64 => ConditionTerm::Bitvector64SignedAddOverflows(
                    Box::new(a.clone()),
                    Box::new(b.clone()),
                ),
            },
            false,
        );
        let mut works = Vec::new();
        for size in [8_u64, 16, 32, 64] {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                let unrelated = Bitvector32Term::Variable(Variable(95_000 + index));
                let fact = match index % 3 {
                    0 => less(unrelated, constant(1_000)),
                    1 => at_least(unrelated, constant(-1_000)),
                    _ => equal(unrelated, constant(7)),
                };
                assumptions = assumptions.assume_condition(fact, true);
            }
            assumptions = assumptions
                .assume_condition(less(a.clone(), constant(100)), true)
                .assume_condition(at_least(a.clone(), constant(-5)), true)
                .assume_condition(equal(b.clone(), constant(1)), true);
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut facts = assumptions.signed_constant_bound_facts(width, &a);
                facts.extend(assumptions.signed_constant_bound_facts(width, &b));
                facts
            });
            assert_eq!(facts.len(), 3, "{width:?} at {size}: {facts:?}");
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::SignedDefined {
                    width,
                    bounds: (0..facts.len()).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            assert_eq!(certificate.check(&goal, &facts), Ok(()), "{width:?}");
            works.push(work);
        }
        assert!(
            works.iter().all(|work| *work == works[0]),
            "{width:?} bound selection work grew with unrelated bounds: {works:?}"
        );
    }
}

#[test]
fn equal_value_interval_queries_scale_with_delta_and_skip_unrelated_facts() {
    let mut works = Vec::new();
    for size in [32u64, 64, 128] {
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let root = Bitvector32Term::Variable(Variable(200_000 + size * 10));
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(root.clone(), 0u32.into()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(root.clone(), 100u32.into()),
                    true,
                );
            PureFactContext::reset_signed_interval_fallback_fact_visits();
            for index in 0..size {
                let alias = Bitvector32Term::Variable(Variable(300_000 + size * 10 + index));
                let unrelated = Bitvector32Term::Variable(Variable(400_000 + size * 10 + index));
                facts = facts
                    .assume_condition(
                        ConditionTerm::signed_less_equal(unrelated, 1000u32.into()),
                        true,
                    )
                    .assume_condition(ConditionTerm::equal(root.clone(), alias.clone()), true);
                assert_eq!(facts.signed_interval(&alias), Some((0, 100)));
            }
            assert_eq!(PureFactContext::signed_interval_fallback_fact_visits(), 0);
        });
        assert!(work < 1000 * size as usize, "size={size}, work={work}");
        works.push(work);
    }
    assert!(
        works[2] < 6 * works[0],
        "interval lookup work grew too fast: {works:?}"
    );
}

/// The chain walk reads the facts on the chain alone: its work grows
/// linearly with the chain length and not at all with unrelated order
/// facts, including unrelated chains.
#[test]
fn order_chain_bound_work_is_linear_in_the_chain_and_flat_in_unrelated_facts() {
    let chain_context = |length: u64, unrelated: u64| {
        let mut assumptions = PureFactContext::new();
        for index in 0..unrelated {
            let a = Bitvector32Term::Variable(Variable(97_000 + 2 * index));
            let b = Bitvector32Term::Variable(Variable(97_001 + 2 * index));
            assumptions = assumptions
                .assume_condition(ConditionTerm::signed_less_equal(a, b.clone()), true)
                .assume_condition(
                    ConditionTerm::signed_less_than(b, Bitvector32Term::Constant(50)),
                    true,
                );
        }
        let link = |index: u64| Bitvector32Term::Variable(Variable(98_000 + index));
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), link(0)),
            true,
        );
        for index in 0..length {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(link(index), link(index + 1)),
                true,
            );
        }
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_than(link(length), Bitvector32Term::Constant(1000)),
            true,
        );
        (assumptions, link(0))
    };
    let measure = |length: u64, unrelated: u64| {
        let (assumptions, start) = chain_context(length, unrelated);
        let (bound, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.chained_signed_constant_bound(&start, true)
        });
        assert_eq!(bound, Some(999), "length {length}, unrelated {unrelated}");
        work
    };
    let flat = [0, 4, 16, 64].map(|unrelated| measure(8, unrelated));
    assert!(
        flat.iter().all(|work| *work == flat[0]),
        "chain walk work grew with unrelated facts: {flat:?}"
    );
    let by_length = [4, 8, 16, 32].map(|length| measure(length, 16));
    for pair in by_length.windows(2) {
        // Each link is filed at both endpoints, so doubling the chain at
        // most doubles the entries read, plus a constant.
        assert!(
            pair[1] <= 2 * pair[0] + 4,
            "chain walk work is not linear in the chain: {by_length:?}"
        );
    }
    assert!(by_length[3] > by_length[0], "{by_length:?}");
}

#[test]
fn int64_guard_work_is_independent_of_unrelated_facts() {
    let n = Bitvector32Term::Variable(Variable(95_111));
    let d = Bitvector32Term::Variable(Variable(95_112));
    let constant = Bitvector32Term::Int64Constant;
    let mut work_counts = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Variable(Variable(96_000 + index)),
                    constant(123),
                ),
                true,
            );
        }
        facts = facts
            .assume_condition(ConditionTerm::int64_equal(n.clone(), constant(7)), true)
            .assume_condition(
                ConditionTerm::int64_signed_greater_than(d.clone(), constant(0)),
                true,
            );
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::int64_signed_divide_overflows(
                    n.clone(),
                    d.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_multiply_overflows(
                    n.clone(),
                    constant(2),
                )),
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    n.clone(),
                    n.clone(),
                )),
            ]
        });
        assert_eq!(answers, [Some(false); 3]);
        work_counts.push(work);
    }
    assert!(
        work_counts.iter().all(|work| *work == work_counts[0]),
        "{work_counts:?}"
    );
    assert!(work_counts[0] > 0);
}

#[test]
fn int64_zero_alias_addition_and_subtraction_are_safe_and_indexed() {
    let x = Bitvector32Term::Variable(Variable(96_001));
    let zero = Bitvector32Term::Variable(Variable(96_002));
    let constant = Bitvector32Term::Int64Constant;
    let mut baseline_work = None;
    for population in [8u64, 32, 128, 512] {
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
        for i in 0..population {
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Variable(Variable(97_000 + i)),
                    constant(100),
                ),
                true,
            );
        }
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    x.clone(),
                    zero.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    zero.clone(),
                    x.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    x.clone(),
                    zero.clone(),
                )),
                facts.decide(&ConditionTerm::int64_equal(
                    Bitvector32Term::int64_add(x.clone(), zero.clone()),
                    x.clone(),
                )),
                facts.decide(&ConditionTerm::int64_equal(
                    Bitvector32Term::int64_subtract(x.clone(), zero.clone()),
                    x.clone(),
                )),
            ]
        });
        assert_eq!(
            answers,
            [
                Some(false),
                Some(false),
                Some(false),
                Some(true),
                Some(true)
            ]
        );
        assert!(work > 0);
        assert_eq!(
            facts.decide(&ConditionTerm::int64_equal(
                Bitvector32Term::int64_add(x.clone(), constant(1)),
                x.clone()
            )),
            None
        );
        if let Some(baseline) = baseline_work {
            assert_eq!(work, baseline);
        } else {
            baseline_work = Some(work);
        }
        // An unknown nonzero addend/subtrahend can still overflow.
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_add_overflows(
                x.clone(),
                constant(1)
            )),
            None
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                x.clone(),
                constant(1)
            )),
            None
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                zero.clone(),
                x.clone()
            )),
            None
        );
    }
    for edge in [i64::MIN, i64::MAX] {
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_add_overflows(
                constant(edge),
                zero.clone()
            )),
            Some(false)
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                constant(edge),
                zero.clone()
            )),
            Some(false)
        );
    }
}

#[test]
fn int64_zero_identity_chains_scale_with_the_queried_term() {
    let x = Bitvector32Term::Variable(Variable(98_001));
    let zero = Bitvector32Term::Variable(Variable(98_002));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::int64_equal(zero.clone(), Bitvector32Term::Int64Constant(0)),
        true,
    );
    let mut previous = None;
    for depth in [8usize, 32, 128, 512] {
        let mut term = x.clone();
        for _ in 0..depth {
            term = Bitvector32Term::int64_add(term, zero.clone());
        }
        let query = ConditionTerm::int64_equal(term, x.clone());
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        assert!(work > 0);
        if let Some((old_depth, old_work)) = previous {
            assert!(
                work <= old_work * depth / old_depth + 32,
                "{depth}: {work}, previous {old_work}"
            );
        }
        previous = Some((depth, work));
    }
}

#[test]
fn bit_preserving_64_bit_conversion_equalities_are_indexed_and_scale() {
    let value = Bitvector32Term::Variable(Variable(99_001));
    let mut baseline = None;
    for population in [8u64, 32, 128] {
        let mut facts = PureFactContext::new();
        for index in 0..population {
            facts = facts.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(100_000 + index)),
                    Bitvector32Term::UInt64Constant(0),
                ),
                true,
            );
        }
        let query = ConditionTerm::uint64_equal(
            Bitvector32Term::UInt64FromInt64(Box::new(value.clone())),
            value.clone(),
        );
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        if let Some(previous) = baseline {
            assert_eq!(work, previous);
        } else {
            baseline = Some(work);
        }
    }
    let facts = PureFactContext::new();
    let mut previous = None;
    for depth in [8usize, 32, 128, 512] {
        let mut term = value.clone();
        for _ in 0..depth {
            term = Bitvector32Term::UInt64FromInt64(Box::new(term));
        }
        let query = ConditionTerm::uint64_equal(term, value.clone());
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        if let Some((old_depth, old_work)) = previous {
            assert!(
                work <= old_work * depth / old_depth + 32,
                "{depth}: {work}, previous {old_work}"
            );
        }
        previous = Some((depth, work));
    }
}
