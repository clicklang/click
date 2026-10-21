// Scaling tests of `src/kernel/resource_tracker/cell_source.rs` (module `separated_range_frame_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn model_start_membership_ignores_unrelated_order_bounds() {
    let mut samples = Vec::new();
    for size in [0u64, 8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, _, _, _, mut context, facts) = model_start_frame();
        let (data, range) = match &facts[0] {
            Proposition::CResourceSeparate { left, .. } => match left.as_ref() {
                CResource::Memory(range) => (range.base().clone(), range.clone()),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        for extra in 0..size {
            let noise = Bitvector32Term::Variable(Variable(9_949_000 + extra));
            context = context
                .assume_condition(
                    ConditionTerm::signed_less_equal(range.start().clone(), noise.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(noise, range.end().clone()),
                    true,
                );
        }
        let index = Bitvector32Term::Add(
            Box::new(Bitvector32Term::Variable(Variable(9_941_002))),
            Box::new(Bitvector32Term::Variable(Variable(9_941_004))),
        );
        let access = data.offset_by_elements(index, 4);
        PureFactContext::reset_exact_order_evidence_visits();
        let (membership, work) = crate::instrumentation::measure_deterministic_work(|| {
            PointerInRangeEvidence::for_pointer(&access, &range, &context)
        });
        assert!(
            membership.is_some(),
            "the selected start alias and both bounds supply membership"
        );
        let visits = PureFactContext::exact_order_evidence_visits();
        samples.push((work, visits));
        assert_eq!(
            visits, 0,
            "size={size}: start-alias membership scanned order facts: {samples:?}"
        );
    }
    assert!(
        samples.iter().all(|(work, _)| *work < 1000),
        "selected membership work grew: {samples:?}"
    );
}

#[test]
fn separated_range_frame_retains_full_access_and_range_extents() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let data = Pointer::symbolic(Variable(9_901_001));
        let field = Pointer::symbolic(Variable(9_901_002));
        let backing = CMemoryRange::new(data.clone(), 0u32.into(), 2u32.into());
        let descriptor = CMemoryRange::new(field.clone(), 0u32.into(), 2u32.into());
        let separate = |left, right| Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(left)),
            right: Box::new(CResource::Memory(right)),
        };
        let authority = separate(backing.clone(), descriptor.clone());
        let mut context = PureFactContext::new().assume_proposition(authority.clone());
        for index in 0..size {
            context = context.assume_proposition(separate(
                CMemoryRange::new(
                    Pointer::symbolic(Variable(9_902_000 + index * 2)),
                    0u32.into(),
                    2u32.into(),
                ),
                CMemoryRange::new(
                    Pointer::symbolic(Variable(9_902_001 + index * 2)),
                    0u32.into(),
                    2u32.into(),
                ),
            ));
        }
        let child = CMemoryRange::new(data.clone(), 1u32.into(), 2u32.into());
        let read = field.offset_by_bytes(4);
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            typed_range_disjoint_from_pointer_evidence(&child, &read, 4, &context)
        });
        let proof = proof.expect("selected separation covers the complete subrange and read");
        assert!(matches!(
            &proof,
            RangeDisjointFromPointerEvidence::ExactSeparationFact(_)
        ));
        assert!(proof.checks(&child, &read, 4, &context));
        // The first element belongs to the descriptor, but the second does not.
        assert!(!proof.checks(&child, &read, 8, &context));
        assert!(typed_range_disjoint_from_pointer_evidence(&child, &read, 8, &context).is_none());
        let too_large = CMemoryRange::new(data, 0u32.into(), 3u32.into());
        assert!(!proof.checks(&too_large, &read, 4, &context));
        assert!(
            typed_range_disjoint_from_pointer_evidence(&too_large, &read, 4, &context).is_none()
        );
        let withdrawn = context.without_exact_fact(&authority);
        assert!(!proof.checks(&child, &read, 4, &withdrawn));
        assert!(typed_range_disjoint_from_pointer_evidence(&child, &read, 4, &withdrawn).is_none());
        assert!(work < 200, "size={size}, work={work}");
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated separations changed work: {samples:?}"
    );
}
