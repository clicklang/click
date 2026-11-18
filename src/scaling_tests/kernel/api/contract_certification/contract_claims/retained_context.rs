use super::*;

#[test]
fn retained_closing_work_tracks_outcomes_and_clauses_without_walking_ambient_facts() {
    for clauses in [1, 2, 4, 8] {
        let mut samples = Vec::new();
        for unrelated in [0, 64, 256] {
            let (function, entry, path, outcome) = fixture(clauses, unrelated);
            for paths in [1, 4, 16, 64] {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..paths {
                        let prepared = prepare_closing_path(
                            &function,
                            &path,
                            &entry.closing_entry,
                            &outcome,
                            vec![],
                            false,
                            false,
                            None,
                            false,
                            None,
                        )
                        .unwrap();
                        assert!(Arc::ptr_eq(
                            &prepared.checked_required_resources,
                            &entry.closing_entry.checked
                        ));
                    }
                });
                assert!(
                    work <= 512 * paths * (clauses + 1),
                    "{paths} paths, {clauses} clauses, {unrelated} unrelated facts: {work}"
                );
                samples.push((paths, unrelated, work));
            }
        }
        for paths in [1, 4, 16, 64] {
            let costs = samples
                .iter()
                .filter(|(count, _, _)| *count == paths)
                .map(|(_, _, work)| *work)
                .collect::<Vec<_>>();
            assert!(
                costs.windows(2).all(|pair| pair[0] == pair[1]),
                "{clauses} clauses, {paths} paths: {costs:?}"
            );
        }
    }
}

#[test]
fn prepared_exit_projection_uses_exact_checkpoints_without_revisiting_owners() {
    let mut samples = Vec::new();
    for size in [4_u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let (function, prepared, _, _) = fixture(0, 0);
        let function =
            function.with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
                "boxed",
                vec![],
                None,
                false,
                vec![ResourceSpec::token(
                    ResourceAccessMode::Own,
                    "child".to_string(),
                    vec![],
                    vec![],
                )],
                vec![],
            )]);
        let entry = &prepared.closing_entry;
        let head = ResourceFact::own_composite("boxed".into(), vec![]);
        let mut resources = ResourceContext::new().unchecked_with_fact(head.clone());
        let mut assumptions = PureFactContext::new();
        for n in 0..size {
            resources = resources
                .unchecked_with_fact(ResourceFact::own_token(format!("frame_{n}"), vec![]));
            assumptions = assumptions.assume_proposition(Proposition::Predicate {
                name: format!("premise_{n}"),
                arguments: vec![],
            });
        }
        let raw = ExecutionState::new().with_resource_context(resources);
        let cold = entry
            .prepare_exit_projection(&function, &raw, &mut raw.clone(), &assumptions)
            .unwrap();
        assert!(!cold.contains_exact_representation(&head));
        let (warm, work) = crate::instrumentation::measure_deterministic_work(|| {
            entry
                .prepare_exit_projection(&function, &raw, &mut raw.clone(), &assumptions)
                .unwrap()
        });
        assert!(warm.shares_storage_with(&cold));
        samples.push(work);

        let more = assumptions
            .clone()
            .assume_proposition(Proposition::Predicate {
                name: "new_fact".into(),
                arguments: vec![],
            });
        let new_facts = entry
            .prepare_exit_projection(&function, &raw, &mut raw.clone(), &more)
            .unwrap();
        assert!(!new_facts.shares_storage_with(&cold));

        let changed = raw.clone().with_resource_context(
            raw.resources()
                .clone()
                .unchecked_with_fact(ResourceFact::own_token("new_owner".into(), vec![])),
        );
        let new_owner = entry
            .prepare_exit_projection(&function, &changed, &mut changed.clone(), &more)
            .unwrap();
        assert!(!new_owner.shares_storage_with(&new_facts));
        assert!(
            new_owner.contains_exact_representation(&ResourceFact::own_token(
                "new_owner".into(),
                vec![]
            ))
        );
    }
    assert_eq!(samples, vec![1, 1, 1]);
}
