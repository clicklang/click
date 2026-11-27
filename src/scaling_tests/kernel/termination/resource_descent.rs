#[test]
fn witness_publication_and_calls_ignore_the_ambient_resource_frame() {
    for size in [1, 16, 64, 256, 1024] {
        let (descent, state, parent) = entry();
        let mut resources = state.resources().clone();
        for index in 0..size {
            resources = resources.unchecked_with_fact(fact("unrelated", index));
            resources = resources.unchecked_with_fact(fact("list", index + 100));
        }
        let state = state.with_resource_context(resources);
        let child = fact("list", 1);
        let (next, publication) =
            crate::instrumentation::measure_deterministic_work(|| unfold(&state, &parent, &child));
        let ((accepted, refused), checking) =
            crate::instrumentation::measure_deterministic_work(|| {
                (
                    descent.accepts(&next, &child, &PureFactContext::new()),
                    descent.accepts(&next, &fact("list", 50), &PureFactContext::new()),
                )
            });
        assert!(accepted && !refused);
        assert!(
            publication <= 64 * (size.ilog2() as usize + 1),
            "{size}: {publication} publication work"
        );
        assert!(
            checking <= 16 * (size.ilog2() as usize + 1),
            "{size}: {checking} checking work"
        );
    }
}

#[test]
fn witness_checks_do_not_walk_the_unfold_history() {
    for size in [1, 16, 64, 256, 1024] {
        let (descent, mut state, mut parent) = entry();
        for index in 1..=size {
            let child = fact("list", index);
            state = unfold(&state, &parent, &child);
            parent = child;
        }
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            descent.accepts(&state, &parent, &PureFactContext::new())
        });
        assert!(accepted);
        assert!(
            work <= 8 * (size.ilog2() as usize + 1),
            "{size}: {work} ancestry work"
        );
    }
}

#[test]
fn child_witness_aliases_use_the_published_point_index() {
    for size in [1u32, 16, 64, 256, 1024] {
        let assumptions = PureFactContext::new();
        let pointer_fact = |id| {
            ResourceFact::view_composite(
                "list".into(),
                vec![ProgramValue::typed_pointer(
                    Address::symbolic(Variable(id)),
                    ProgramType::Int32Pointer,
                )],
            )
        };
        let parent = pointer_fact(1);
        let child = pointer_fact(2);
        let resources =
            ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(parent.clone());
        let root = resources
            .structural_witness_occurrence(&parent, &assumptions)
            .unwrap();
        let descent = ResourceDescent {
            requirement: 0,
            authority: Arc::new(()),
            root,
            family: "list".into(),
            entry_resource: parent.resource().clone(),
            declaration: ResourceSpec::composite(
                ResourceAccessMode::View,
                "list".into(),
                vec![],
                vec![],
            ),
        };
        let state = descent.at_entry(&ExecutionState::new().with_resource_context(resources));
        let opening = state
            .resources()
            .open_structural_witness(&parent, &assumptions);
        let mut resources = state.resources().clone().unchecked_with_fact(child.clone());
        let owned_child = ResourceFact::own(child.resource().clone());
        resources =
            resources.with_opened_structural_witnesses(opening, &[owned_child], true, &assumptions);
        for index in 0..size {
            resources = resources.unchecked_with_fact(pointer_fact(u64::from(index) + 100));
        }
        resources.synchronize_memory_equalities(&assumptions);
        let state = state.with_resource_context(resources);
        let aliased = assumptions.assume_proposition(Proposition::condition_is(
            OldConditionTerm::PointerEqual(
                Box::new(Pointer::new(
                    Address::symbolic(Variable(2)),
                    ProgramType::Int32Pointer,
                )),
                Box::new(Pointer::new(
                    Address::symbolic(Variable(50)),
                    ProgramType::Int32Pointer,
                )),
            ),
            true,
        ));
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            descent.accepts(&state, &pointer_fact(50), &aliased)
        });
        assert!(
            accepted,
            "{size}: a selected child alias must retain its witness"
        );
        assert!(
            work <= 256 + 64 * (size.ilog2() as usize + 1),
            "{size}: {work} alias work"
        );
    }
}
