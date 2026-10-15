// Scaling tests of `src/kernel/assumptions.rs` (module `stated_requirement_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn stated_query_work_is_independent_of_unrelated_facts() {
    let goal = Proposition::Exists {
        name: "goal".into(),
        var: Variable(300),
        sort: Sort::Bitvector32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(300))),
                Box::new(Bitvector32Term::Constant(5)),
            ),
            true,
        )),
    };
    let small = PureFactContext::new().assume_proposition(requirement(301, "fact"));
    let mut large = small.clone();
    for index in 0..128 {
        large = large.assume_proposition(requirement(10_000 + index, "unrelated"));
        large = large.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(20_000 + index))),
                Box::new(Bitvector32Term::Constant(index as u32)),
            ),
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
