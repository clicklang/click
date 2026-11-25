// Scaling tests of `src/kernel/assumptions.rs` (module `stated_requirement_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn stated_query_work_is_independent_of_unrelated_facts() {
    let goal = crate::kernel::quantifiers::test_exists(
        "goal".into(),
        Variable(300),
        Sort::Bitvector32,
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(300))),
                right: Box::new(OldMachineTerm::constant(5)),
            },
            true,
        ),
    );
    let small = PureFactContext::new().assume_proposition(requirement(301, "fact"));
    let mut large = small.clone();
    for index in 0..128 {
        large = large.assume_proposition(distinct_requirement(10_000 + index, "unrelated"));
        large = large.assume_proposition(Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(20_000 + index))),
                right: Box::new(OldMachineTerm::constant(index as u32)),
            },
            true,
        ));
    }
    small.build_stated_proposition_index();
    large.build_stated_proposition_index();
    let (_, small_work) =
        crate::instrumentation::measure_deterministic_work(|| small.states_required_goal(&goal));
    let (_, large_work) =
        crate::instrumentation::measure_deterministic_work(|| large.states_required_goal(&goal));
    assert_eq!(small_work, large_work);
    // Keep the branch alive to pin persistent sibling independence.
    assert!(!small.states_required_goal(&goal));
}

#[test]
fn stated_query_scaling_ignores_unrelated_same_sort_quantifiers() {
    let goal = requirement(40_000, "goal");
    let mut work = Vec::new();
    for size in [4usize, 8, 16, 32] {
        let mut context = PureFactContext::new().assume_proposition(goal.clone());
        for index in 0..size {
            context = context.assume_proposition(distinct_requirement(
                50_000 + index as u64,
                "same-sort-unrelated",
            ));
        }
        context.build_stated_proposition_index();
        let (available, measured) = crate::instrumentation::measure_deterministic_work(|| {
            context.states_required_goal(&goal)
        });
        assert!(available);
        work.push(measured);
    }
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "stated-query work scanned same-sort facts: {work:?}"
    );
}

/// The stated index keys each fact change once, when a query first
/// needs it: never for a context nobody asks, and only its own suffix for
/// a sibling that shares an already built prefix.
#[test]
fn stated_index_keys_each_fact_once_and_only_when_asked() {
    let goal = requirement(45_000, "goal");
    let mut base = PureFactContext::new().assume_proposition(goal.clone());
    for index in 0..64 {
        base = base.assume_proposition(distinct_requirement(46_000 + index, "unrelated"));
    }
    let key_work = |context: &PureFactContext| {
        crate::instrumentation::measure_deterministic_work(|| {
            context.build_stated_proposition_index()
        })
        .1
    };
    let left = base
        .clone()
        .assume_proposition(distinct_requirement(47_000, "left"));
    let right = base
        .clone()
        .assume_proposition(distinct_requirement(47_001, "right"));
    let unasked_fact = distinct_requirement(47_002, "unasked");
    // A new fact's comparison observations are interned when it is first
    // assumed anywhere; warm that so the measurement is the assumption alone.
    let _ = PureFactContext::new().assume_proposition(unasked_fact.clone());
    let (_, unasked) = crate::instrumentation::measure_deterministic_work(|| {
        base.clone().assume_proposition(unasked_fact.clone())
    });
    let first = key_work(&left);
    let sibling = key_work(&right);
    let again = key_work(&left);
    assert!(
        unasked < sibling,
        "assuming a fact computed a key: {unasked} vs one key {sibling}"
    );
    assert!(
        first > 32 * sibling,
        "the first query keys the shared prefix: {first} vs {sibling}"
    );
    assert_eq!(again, 0, "a built index is not rebuilt");
    assert!(left.states_required_goal(&goal) && right.states_required_goal(&goal));
}

/// Rule K6: a 32-bit equality filed at `uint32` and the same equality at
/// `int32` are one fact. A lookup at either signedness finds a fact filed
/// at the other, at the work of a lookup at its own, however many unrelated
/// equalities the context holds; nothing is filed twice.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn a_32_bit_equality_is_one_fact_at_either_signedness() {
    let x = OldMachineTerm::Variable(Variable(31_000));
    let equality = |format, right: u32| OldConditionTerm::Compare {
        format,
        relation: CompareRelation::Equal,
        left: Box::new(x.clone()),
        right: Box::new(OldMachineTerm::constant(right)),
    };
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        for (filed, queried) in [
            (MachineIntegerType::UInt32, MachineIntegerType::Int32),
            (MachineIntegerType::Int32, MachineIntegerType::UInt32),
        ] {
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::Variable(Variable(
                            32_000 + u64::from(index),
                        ))),
                        right: Box::new(OldMachineTerm::constant(index)),
                    },
                    true,
                );
            }
            let context = context.assume_condition(equality(filed, u32::MAX), true);
            let twice = context
                .clone()
                .assume_condition(equality(queried, u32::MAX), true);
            assert_eq!(
                twice.fact_counts().0,
                context.fact_counts().0,
                "the other signedness files no second fact, size {size}"
            );
            let (own, own_work) = crate::instrumentation::measure_deterministic_work(|| {
                context.exact_condition_value(&equality(filed, u32::MAX))
            });
            let (other, other_work) = crate::instrumentation::measure_deterministic_work(|| {
                context.exact_condition_value(&equality(queried, u32::MAX))
            });
            assert_eq!(own, Some(true), "size {size}");
            assert_eq!(other, own, "{filed:?} found at {queried:?}, size {size}");
            assert_eq!(other_work, own_work, "size {size}");
            assert_eq!(
                context.exact_condition_value(&equality(queried, 7)),
                context.exact_condition_value(&equality(filed, 7)),
                "size {size}"
            );
            samples.push(other_work);
        }
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "lookup work grew with unrelated equalities: {samples:?}"
    );
}

#[test]
fn arithmetic_evaluation_domains_do_not_force_unrelated_stated_facts() {
    use crate::kernel::machine_integer::{Operation, definedness};
    let format = MachineIntegerType::Int32;
    let index = OldMachineTerm::Variable(Variable(880_000));
    let exact = Operation::Add.exact(
        IntegerTerm::from_machine(format, index.clone()).unwrap(),
        IntegerTerm::constant(1.into()),
    );
    let [upper, lower] = definedness::ordinary_bounds(format, exact);
    let goal = Proposition::And(Box::new(upper), Box::new(lower));
    for mode in 0..4 {
        let mut samples = Vec::new();
        for count in [0, 4, 16, 64] {
            let mut context = PureFactContext::new();
            if mode == 1 {
                context = context
                    .assume_condition(
                        OldConditionTerm::signed_less_equal(
                            OldMachineTerm::constant(0),
                            index.clone(),
                        ),
                        true,
                    )
                    .assume_condition(
                        OldConditionTerm::signed_less_equal(
                            index.clone(),
                            OldMachineTerm::constant(64),
                        ),
                        true,
                    );
            } else if mode == 2 {
                context = context.assume_proposition(goal.clone());
            } else if mode == 3 {
                let Proposition::And(first, second) = &goal else {
                    unreachable!()
                };
                context = context
                    .assume_proposition((**first).clone())
                    .assume_proposition((**second).clone());
            }
            for offset in 0..count {
                context =
                    context.assume_proposition(distinct_requirement(890_000 + offset, "unrelated"));
            }
            // Deliberately leave the stated-proposition index cold.
            let (established, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::ProofObligation::evaluation_requirement_is_established(
                    &context, &goal,
                )
            });
            assert_eq!(established, mode != 0);
            // Warm the selected expression caches with a separate context.
            // Each measured sample still starts with its own cold stated index.
            if count != 0 {
                samples.push(work);
            }
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "mode={mode}: {samples:?}"
        );
    }
}
