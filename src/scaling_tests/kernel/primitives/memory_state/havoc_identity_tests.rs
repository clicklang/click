// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `havoc_identity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn havoc_write_set_identity_scales_near_linearly_with_term_size() {
    let samples = [32, 64, 128, 256]
        .into_iter()
        .map(|depth| {
            let range = range(depth, 1);
            let (identity, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory_havoc_write_set_identity(std::slice::from_ref(&range))
            });
            assert!(!identity.is_empty());
            assert!(work > 0);
            (depth, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
        "havoc identity work grew faster than near-linearly: {samples:?}"
    );
}

#[test]
fn call_frame_retains_a_view_without_scanning_other_views() {
    let pointer = |index| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(index))),
            byte_width: 1,
        },
    };
    let target = pointer(900_000);
    crate::kernel::eval::declare_load_access_width(&target, 4);
    let before = CMemory::new();
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(target.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let mut residual = ResourceContext::new();
        for index in 0..count {
            residual = residual.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(
                    pointer(900_000 + index),
                    0u32.into(),
                    4u32.into(),
                    1,
                ),
            ));
        }
        let ((after, recorded, evidence), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let kept = CallKeptOwnership::new(
                    residual.clone(),
                    CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
                    &assumptions,
                );
                let after = before.clone().with_call_memory_havoc(
                    Variable(950_000 + count),
                    &[CMemoryRange::unnamed_footprint()],
                    &assumptions,
                    Some(&kept),
                );
                let recorded = CallKeptRanges::recorded_on(&after).unwrap();
                assert!(recorded.holds_access(&target, 4, &assumptions));
                assert!(!recorded.holds_access(&pointer(999_999), 4, &assumptions));
                let evidence = crate::kernel::memory_provenance::with_extended_dag_bridging(|| {
                    crate::kernel::memory_provenance::atomic_memory_load_equality_evidence(
                        &load(&after),
                        &load(&before),
                        &assumptions,
                    )
                })
                .expect("the recorded view keeps the uncached read unchanged");
                (after, recorded, evidence)
            });
        assert!(evidence.is_fully_typed());
        assert!(evidence.checks(
            &Proposition::ConditionIs(ConditionTerm::equal(load(&after), load(&before)), true),
            &assumptions,
        ));
        assert!(
            recorded.contains_range(&CMemoryRange::new_with_element_width(
                target.clone(),
                0u32.into(),
                4u32.into(),
                1,
            ))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 3 + 128),
        "call frame scanned views: {samples:?}"
    );
}
