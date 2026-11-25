#[test]
fn known_domains_do_not_readmit_unrelated_path_facts() {
    for count in [0u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let opaque = OldPointer::new(
            Address::symbolic(Variable(1013300)),
            ProgramType::Int32Pointer,
        );
        let root = opaque.clone().with_root_bounds();
        let cached = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(opaque.clone(), root.clone()),
            true,
        );
        for (pointer, context) in [(root, PureFactContext::new()), (opaque, cached)] {
            let facts: ExecutionFacts = (0..count)
                .map(|i| {
                    ExecutionPureFact::new(Proposition::condition_is(
                        ConditionTerm::Variable(Variable(1013400 + i)),
                        true,
                    ))
                })
                .collect::<Vec<_>>()
                .into();
            let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    subobject_access_refusal(pointer.address(), &pointer, 4, &facts, &[], &context)
                        .is_none()
                );
                assert!(
                    subobject_formation_guards(
                        &pointer,
                        &pointer.address().offset_by_bytes(4),
                        &facts,
                        &[],
                        &context,
                        &ResourceContext::new()
                    )
                    .is_ok()
                );
                subobject_paths(
                    pointer,
                    4,
                    facts,
                    Vec::new(),
                    &context,
                    &ResourceContext::new(),
                )
            });
            assert_eq!(
                crate::kernel::reasoning::path_facts::context_rebuild_entries() - before,
                0,
                "readmitted unrelated path facts at count={count}"
            );
            assert!(work <= 32, "count={count}, work={work}");
            assert_eq!(paths.len(), 1);
            assert!(matches!(paths[0].outcome, ExpressionOutcome::Value(_)));
            assert_eq!(paths[0].facts.len(), count as usize);
        }
        // An unresolved domain is also a read-only miss. Access authority is
        // checked separately, using the context the caller already prepared.
        let unknown = OldPointer::new(
            Address::symbolic(Variable(1013700)),
            ProgramType::Int32Pointer,
        );
        let context = PureFactContext::new();
        let facts: ExecutionFacts = (0..count)
            .map(|i| {
                ExecutionPureFact::new(Proposition::condition_is(
                    ConditionTerm::Variable(Variable(1013800 + i)),
                    true,
                ))
            })
            .collect::<Vec<_>>()
            .into();
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (refusal, work) = crate::instrumentation::measure_deterministic_work(|| {
            subobject_access_refusal(unknown.address(), &unknown, 4, &facts, &[], &context)
        });
        assert!(refusal.is_none());
        assert_eq!(
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - before,
            0
        );
        assert!(work <= 32, "opaque miss: count={count}, work={work}");
    }
}
