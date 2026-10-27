#[test]
fn ambient_loadability_enumeration_charges_every_visited_fact() {
    for size in [8u64, 32, 128] {
        let state = crate::kernel::CState::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: state.memory().clone(),
                base: Pointer::symbolic(Variable(670_000 + index)),
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            });
        }
        let (visited, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .memory_loadable_fact_propositions(SearchPermission::new())
                .count()
        });
        assert_eq!(visited, size as usize);
        assert_eq!(
            work, visited,
            "planner visits must consume the search budget"
        );
    }
}
