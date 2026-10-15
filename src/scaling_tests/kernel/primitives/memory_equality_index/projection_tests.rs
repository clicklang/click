// Scaling tests of `src/kernel/primitives/memory_equality_index/projection_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn projection_context_attachment_does_not_scan_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (head, definition, memory, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(890_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(890_001 + i * 2)),
                ),
                true,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let context = projection_context(&head, &definition, &memory, &facts);
                let children = prior_child(context, &head);
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    children
                        .concrete_read_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(children.permits_memory_read(&alias, 4, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "projection scanned unrelated facts: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "projection rebuilt unrelated graph state: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn owned_frontier_attachment_ignores_unrelated_facts_and_caller_resources() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (viewed, definition, memory, mut facts, _) = fixture();
        let head = CResourceFact::own(viewed.resource().clone());
        let mut ambient = ResourceContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(891_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(891_001 + i * 2)),
                ),
                true,
            );
            ambient = ambient.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                Pointer::symbolic(Variable(895_000 + i)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )));
        }
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(ambient);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let context = owned_frontier_context(&head, &definition, &state, &facts);
                assert_eq!(
                    context.facts(),
                    std::slice::from_ref(&head),
                    "frontier expansion must not import ambient authority"
                );
                let children = prior_child(context, &head);
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    children
                        .concrete_read_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(children.permits_memory_read(&alias, 4, &facts));
                assert!(!children.permits_memory_read(
                    &Pointer::symbolic(Variable(895_000)),
                    4,
                    &facts
                ));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "owned frontier scanned unrelated state: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "owned frontier rebuilt unrelated state: {samples:?}"
    );
}

#[test]
fn frontier_coverage_does_not_scan_unrelated_equality_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (_, _, _, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
        }
        let available = vec![coverage_piece(881_000, 0, 1)];
        let wanted = coverage_piece(881_002, 0, 1);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (input, residual) =
                    coverage_context(available, std::slice::from_ref(&wanted), &facts);
                assert!(
                    input
                        .concrete_write_entries(&Pointer::symbolic(Variable(881_002)), 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(residual.unwrap().is_empty());
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "frontier coverage scanned unrelated facts: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "frontier coverage rebuilt unrelated graph state: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn resource_satisfaction_does_not_scan_unrelated_resources_or_equalities() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (_, _, _, mut facts, _) = fixture();
        let mut available = vec![coverage_piece(881_000, 1, 3)];
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
            available.push(coverage_piece(895_000 + i, 0, 1));
        }
        let context = ResourceContext::new()
            .try_compose_with_facts(available, &facts)
            .unwrap();
        let wanted = coverage_piece(881_002, 1, 3);
        let consumed = coverage_piece(881_002, 0, 1);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(context.satisfies_fact(&wanted, &facts));
                assert!(!context.satisfies_fact(&consumed, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "resource satisfaction scanned unrelated state: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "resource satisfaction rebuilt unrelated state: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn fresh_and_framing_publication_do_not_scan_ambient_inputs() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (head, definition, memory, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
        }
        let head = CResourceFact::own(head.resource().clone());
        let residual = ResourceContext::new()
            .try_compose_with_fact(head.clone(), &facts)
            .unwrap();
        let ambient = residual
            .clone()
            .try_compose_with_facts((0..size).map(|i| coverage_piece(895_000 + i, 0, 1)), &facts)
            .unwrap();
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(ambient);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let fresh = ResourceContext::new_with_equalities(&facts)
                    .unchecked_with_fact(coverage_piece(881_000, 0, 1));
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    fresh
                        .concrete_write_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                let kept = crate::kernel::functions::call_kept_ownership(
                    &residual,
                    std::slice::from_ref(&definition),
                    &state,
                    &facts,
                );
                let opened = kept.opened_resources_for_test();
                assert!(
                    opened
                        .concrete_write_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert_eq!(
                    opened.facts().len(),
                    2,
                    "ambient authority must not enter the frontier"
                );
                assert!(!opened.satisfies_fact(&coverage_piece(895_000, 0, 1), &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "publication scanned unrelated graph/resource input: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "publication rebuilt unrelated state: {samples:?}"
    );
}
