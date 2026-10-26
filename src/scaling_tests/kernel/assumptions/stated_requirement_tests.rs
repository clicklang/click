// Scaling tests of `src/kernel/assumptions.rs` (module `stated_requirement_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn stated_query_work_is_independent_of_unrelated_facts() {
    let goal = Proposition::Exists {
        name: "goal".into(),
        var: Variable(300),
        sort: Sort::Bitvector32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::Variable(Variable(300))),
                right: Box::new(Bitvector32Term::Constant(5)),
            },
            true,
        )),
    };
    let small = PureFactContext::new().assume_proposition(requirement(301, "fact"));
    let mut large = small.clone();
    for index in 0..128 {
        large = large.assume_proposition(requirement(10_000 + index, "unrelated"));
        large = large.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::Variable(Variable(20_000 + index))),
                right: Box::new(Bitvector32Term::Constant(index as u32)),
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
            context = context
                .assume_proposition(requirement(50_000 + index as u64, "same-sort-unrelated"));
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
        base = base.assume_proposition(requirement(46_000 + index, "unrelated"));
    }
    let key_work = |context: &PureFactContext| {
        crate::instrumentation::measure_deterministic_work(|| {
            context.build_stated_proposition_index()
        })
        .1
    };
    let left = base.clone().assume_proposition(requirement(47_000, "left"));
    let right = base
        .clone()
        .assume_proposition(requirement(47_001, "right"));
    let (_, unasked) = crate::instrumentation::measure_deterministic_work(|| {
        base.clone()
            .assume_proposition(requirement(47_002, "unasked"))
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
fn a_32_bit_equality_is_one_fact_at_either_signedness() {
    let x = Bitvector32Term::Variable(Variable(31_000));
    let equality = |format, right: u32| ConditionTerm::Compare {
        format,
        relation: CompareRelation::Equal,
        left: Box::new(x.clone()),
        right: Box::new(Bitvector32Term::Constant(right)),
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
                    ConditionTerm::Compare {
                        format: MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: Box::new(Bitvector32Term::Variable(Variable(
                            32_000 + u64::from(index),
                        ))),
                        right: Box::new(Bitvector32Term::Constant(index)),
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
