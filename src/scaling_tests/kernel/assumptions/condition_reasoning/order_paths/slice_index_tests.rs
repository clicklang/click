// Scaling tests of `src/kernel/assumptions/condition_reasoning/order_paths.rs` (module `slice_index_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn wide_order_chain_work_follows_the_chain_and_not_unrelated_facts() {
    let v = |n: u64| Bitvector32Term::Variable(Variable(996000 + n));
    let lt = ConditionTerm::uint64_less_than;
    let u = Bitvector32Term::UInt64Constant;
    // A chain of fixed length beside a growing set of unrelated facts,
    // some sharing a literal endpoint with the question.
    let mut beside = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut facts = PureFactContext::new();
        for i in 0..4 {
            facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
        }
        facts = facts.assume_condition(lt(v(4), u(1000)), true);
        for i in 0..size {
            facts = facts
                .assume_condition(lt(v(10_000 + i), v(20_000 + i)), true)
                .assume_condition(lt(u(0), v(30_000 + i)), true)
                .assume_condition(lt(v(40_000 + i), u(1000)), true);
        }
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&lt(v(0), v(4))),
                facts.decide(&lt(v(0), u(1000))),
                facts.decide(&lt(v(4), v(0))),
            ]
        });
        assert_eq!(answers, [Some(true), Some(true), Some(false)]);
        beside.push(work);
    }
    assert!(beside.iter().all(|work| *work == beside[0]), "{beside:?}");
    // A growing chain costs work linear in its length.
    let mut along = Vec::new();
    for size in [8u64, 16, 32, 64] {
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
        }
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&lt(v(0), v(size))));
        assert_eq!(answer, Some(true));
        along.push(work);
    }
    for pair in along.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{along:?}");
    }
}

#[test]
fn uint64_constant_order_strengthening_is_sound_at_full_width_and_scales() {
    let n = Bitvector32Term::Variable(Variable(998001));
    let c = Bitvector32Term::UInt64Constant;
    let mut work_counts = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut facts = PureFactContext::new();
        for i in 0..size {
            // Shared endpoints exercise the dangerous constant-index shape.
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_than(
                    c(0),
                    Bitvector32Term::Variable(Variable(999000 + i)),
                ),
                true,
            );
        }
        facts = facts.assume_condition(
            ConditionTerm::uint64_greater_than(n.clone(), c(4294967295)),
            true,
        );
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
                facts.decide(&ConditionTerm::uint64_less_equal(n.clone(), c(65535))),
                facts.decide(&ConditionTerm::uint64_less_than(c(0), n.clone())),
                facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(0))),
            ]
        });
        assert_eq!(answers, [Some(false), Some(false), Some(true), Some(false)]);
        work_counts.push(work);
    }
    assert!(work_counts[0] > 0);
    assert!(
        work_counts.iter().all(|work| *work == work_counts[0]),
        "{work_counts:?}"
    );
    for bound in [
        0,
        253,
        65535,
        4294967295,
        i64::MAX as u64,
        i64::MAX as u64 + 1,
        u64::MAX,
    ] {
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(bound)), true);
        assert_eq!(
            facts.decide(&ConditionTerm::uint64_greater_than(n.clone(), c(bound))),
            Some(false)
        );
        if bound < u64::MAX {
            assert_eq!(
                facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound + 1))),
                Some(true)
            );
            assert_eq!(
                facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(bound + 1))),
                Some(false)
            );
        }
        assert_ne!(
            facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound))),
            Some(true)
        );
    }
    let negative = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(65535)), false);
    assert_eq!(
        negative.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
        Some(false)
    );
    assert_eq!(
        PureFactContext::new().decide(&ConditionTerm::uint64_less_than(n, c(253))),
        None
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn uint64_slice_remainder_bounds_ignore_unrelated_facts() {
    let length = Bitvector32Term::Variable(Variable(993001));
    let midpoint = Bitvector32Term::Variable(Variable(993002));
    let difference = Bitvector32Term::uint64_subtract(length.clone(), midpoint.clone());
    let positive =
        ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), difference.clone());
    let bounded = ConditionTerm::uint64_less_equal(difference, length.clone());
    let mut work = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut context = PureFactContext::new();
        for n in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(994000 + n)),
                    Bitvector32Term::UInt64Constant(100),
                ),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::uint64_less_than(midpoint.clone(), length.clone()),
            true,
        );
        let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(context.decide_condition_for_simp(&positive), Some(true));
            assert_eq!(context.decide_condition_for_simp(&bounded), Some(true));
        });
        work.push(used);
    }
    assert!(work.iter().all(|used| *used == work[0]), "{work:?}");
    let unbounded = PureFactContext::new();
    assert_ne!(unbounded.decide_condition_for_simp(&positive), Some(true));
    assert_ne!(unbounded.decide_condition_for_simp(&bounded), Some(true));
    let underflow = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_greater_than(midpoint, length), true);
    assert_ne!(underflow.decide_condition_for_simp(&bounded), Some(true));
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_slice_index_transport_is_sound_and_ignores_unrelated_bounds() {
    let index = Bitvector32Term::Variable(Variable(991001));
    let length = Bitvector32Term::Variable(Variable(991002));
    let index_word = Bitvector32Term::uint32_from_64(index.clone());
    let length_word = Bitvector32Term::uint32_from_64(length.clone());
    let goal = ConditionTerm::signed_less_than(index_word.clone(), length_word);
    let mut work = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut context = PureFactContext::new();
        for n in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(992000 + n)),
                    Bitvector32Term::UInt64Constant(100),
                ),
                true,
            );
        }
        context = context
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), length.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    length.clone(),
                    Bitvector32Term::UInt64Constant(i32::MAX as u64),
                ),
                true,
            );
        let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(context.decide_small_uint64_index_order(&goal), Some(true));
            assert_eq!(
                context.decide_small_uint64_index_order(&ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    index_word.clone()
                )),
                Some(true)
            );
        });
        work.push(used);
    }
    assert!(work.iter().all(|used| *used == work[0]), "{work:?}");
    let unbounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_than(index.clone(), length.clone()),
        true,
    );
    assert_eq!(unbounded.decide_small_uint64_index_order(&goal), None);
    let high = unbounded.assume_condition(
        ConditionTerm::uint64_less_equal(length, Bitvector32Term::UInt64Constant(4294967296)),
        true,
    );
    assert_eq!(high.decide_small_uint64_index_order(&goal), None);
    let reversed = PureFactContext::new()
        .assume_condition(
            ConditionTerm::uint64_less_equal(index.clone(), Bitvector32Term::UInt64Constant(10)),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_less_equal(
                Bitvector32Term::Variable(Variable(991002)),
                Bitvector32Term::UInt64Constant(10),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_greater_equal(index, Bitvector32Term::Variable(Variable(991002))),
            true,
        );
    assert_eq!(reversed.decide_small_uint64_index_order(&goal), Some(false));
}
