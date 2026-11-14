use super::*;

fn candidate_work(steps: u64, unrelated: u64) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(977_000));
    let held = ResourceFact::own_allocation(base.clone(), 4);
    let mut resources = ResourceContext::new().unchecked_with_fact(held.clone());
    for i in 0..unrelated {
        resources = resources.unchecked_with_fact(ResourceFact::own_allocation(
            Pointer::symbolic(Variable(978_000 + i)),
            4,
        ));
    }
    let mut facts = PureFactContext::new();
    resources.synchronize_memory_equalities(&facts);
    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
        let mut previous = base;
        for i in 0..steps {
            let next = Pointer::symbolic(Variable(979_000 + i));
            facts = facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_value_equal(
                    PointerValue::new(previous, ProgramType::Int32Pointer),
                    PointerValue::new(next.clone(), ProgramType::Int32Pointer),
                ),
                true,
            ));
            let required = ResourceFact::own_allocation(next.clone(), 4);
            assert_eq!(
                resources.directly_supporting_fact(&required, &facts),
                Some(&held)
            );
            previous = next;
        }
    });
    work
}

#[test]
fn token_candidates_follow_growing_classes_incrementally() {
    let unrelated = [0, 16, 64, 256].map(|n| candidate_work(8, n));
    assert!(
        unrelated.iter().all(|w| *w <= unrelated[0] + 64),
        "{unrelated:?}"
    );
    let chain = [8, 16, 32, 64].map(|n| candidate_work(n, 64));
    assert!(chain[0] > 0);
    assert!(chain.windows(2).all(|p| p[1] <= 3 * p[0]), "{chain:?}");
}
