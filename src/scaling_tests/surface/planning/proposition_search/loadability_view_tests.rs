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

#[test]
fn witness_collection_stops_when_its_work_budget_is_exhausted() {
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = crate::kernel::CState::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: state.memory().clone(),
                base: Pointer::symbolic(Variable(680_000 + index)),
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            });
        }
        let body = Proposition::Predicate {
            name: "missing_witness".into(),
            arguments: Vec::new(),
        };
        let (found, work) = crate::instrumentation::with_run_work_limit(16, || {
            crate::instrumentation::measure_deterministic_work(|| {
                context.derive_exists_from_witness(Variable(690_000), &Sort::CInt32, &body)
            })
        });
        assert!(found.is_none());
        assert!(work <= 20, "the exhausted planner kept walking: {work}");
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn ambiguous_address_enumeration_requires_search_and_charges_candidates() {
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::CState::new().memory().clone();
        let base = Pointer::symbolic(Variable(795_000));
        let mut context = PureFactContext::new();
        for extent in 1..=size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: base.clone(),
                bytes: extent.into(),
                wide: false,
            });
        }
        assert!(
            context
                .memory_loadable_candidates_for_base(&base)
                .next()
                .is_none()
        );
        let (visited, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .search_memory_loadable_candidates_for_base(SearchPermission::new(), &base)
                .count()
        });
        assert_eq!(visited, size as usize);
        assert!(
            work >= visited,
            "unaccounted search candidates: {work} < {visited}"
        );
    }
}
