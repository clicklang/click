use super::*;

#[test]
fn typed_held_observation_ignores_unrelated_mutexes_and_facts() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let mut context = MutexContext::new(ExecutionState::new())
            .initialize_empty(address(0), 40)
            .unwrap();
        let mut assumptions = PureFactContext::new();
        for index in 1..size {
            context = context.initialize_empty(address(index), 40).unwrap();
            assumptions = assumptions.assume_proposition(Proposition::condition_is(
                OldConditionTerm::Variable(Variable(800000 + index as u64)),
                true,
            ));
        }
        let empty = observe(context.state(), &PureFactContext::new());
        let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
            observe(context.state(), &assumptions)
        });
        assert_eq!(path.proposition, empty.proposition);
        assert_eq!(path.obligations, empty.obligations);
        measurements.push(work);
    }
    assert!(
        measurements[2] <= measurements[0] * 2 + 32,
        "held lookup work: {measurements:?}"
    );
}

#[test]
fn typed_held_observation_does_not_search_a_growing_alias_class() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let context = MutexContext::new(ExecutionState::new())
            .initialize_empty(address(0), 40)
            .unwrap();
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            let alias = Address::new(
                AddressBase::Symbolic(Variable(810000 + index as u64)),
                AddressOffset::constant(0),
            );
            assumptions = assumptions.assume_proposition(Proposition::condition_is(
                OldConditionTerm::AddressEqual(Box::new(address(0)), Box::new(alias)),
                true,
            ));
        }
        let baseline = observe(context.state(), &PureFactContext::new());
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            observe(context.state(), &assumptions)
        });
        assert_eq!(selected.proposition, baseline.proposition);
        assert_eq!(selected.obligations, baseline.obligations);
        measurements.push(work);
    }
    assert!(
        measurements[2] <= measurements[0] * 2 + 32,
        "related alias work: {measurements:?}"
    );
}
