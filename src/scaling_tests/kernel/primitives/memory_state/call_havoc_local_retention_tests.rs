// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `call_havoc_local_retention_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn local_initialization_havoc_checks_scale_with_changed_cells() {
    let target = Address::new("local:target".into(), AddressOffset::constant(0));
    let range = MemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1);
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut before = SymbolicMemory::new()
            .with_block(target.base.clone(), 8)
            .store(
                target.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(7)),
            );
        for index in 0..count {
            let pointer = Address::new(
                format!("local:ambient-{index}").into(),
                AddressOffset::constant(0),
            );
            std::sync::Arc::make_mut(&mut before.heap)
                .initialized
                .record(&pointer, 4);
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            let after = before.clone().with_call_memory_havoc(
                Variable(944_017),
                std::slice::from_ref(&range),
                &facts,
                None,
            );
            after.matches_call_memory_havoc_result(
                &before,
                std::slice::from_ref(&range),
                &facts,
                None,
            )
        });
        assert!(checked);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4 + 128),
        "ambient initialization scan: {samples:?}"
    );
}

#[test]
fn one_byte_call_havoc_ignores_disjoint_cells_in_its_block() {
    for retain_frame in [false, true] {
        let facts = PureFactContext::new();
        let kept = retain_frame.then(|| {
            CallKeptOwnership::new(
                ResourceContext::new(),
                CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
                &facts,
            )
        });
        let at = |offset| Address::new("local:byte-havoc".into(), AddressOffset::constant(offset));
        // The call writes byte 33. The cached word at byte 32 overlaps even
        // though its starting address lies before the write range.
        let range = MemoryRange::new_with_element_width(at(4), 29u32.into(), 30u32.into(), 1);
        let ranges = std::slice::from_ref(&range);
        let value = ProgramValue::Int32(OldMachineTerm::constant(7));
        let mut samples = Vec::new();

        for count in [4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut before = SymbolicMemory::new()
                .with_block(at(0).base.clone(), 2048)
                .store(at(0), value.clone())
                .store(at(32), value.clone())
                .store(at(36), value.clone());
            for i in 0..count {
                before = before.store(at(64 + 4 * i), value.clone());
            }

            let transition = || {
                let after = before.clone().with_call_memory_havoc(
                    Variable(944_019),
                    ranges,
                    &facts,
                    kept.as_ref(),
                );
                assert!(after.matches_call_memory_havoc_result(
                    &before,
                    ranges,
                    &facts,
                    kept.as_ref(),
                ));
                after
            };
            let (after, work) = crate::instrumentation::measure_deterministic_work(transition);
            assert_eq!(after.known_value(&at(32)), None);
            assert!(after.has_initialized_bytes_at(&at(32), 4));
            for offset in [0, 36, 64 + 4 * (count - 1)] {
                assert_eq!(after.known_value(&at(offset)), Some(value.clone()));
            }
            let (reference, reference_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(transition)
                });
            assert_eq!(after, reference);
            samples.push((work, reference_work));
        }
        assert!(
            samples.iter().all(|(work, _)| *work <= samples[0].0 + 8),
            "{samples:?}"
        );
        assert!(samples[3].1 > samples[0].1 + 128, "{samples:?}");
    }
}

#[test]
fn exact_call_havoc_ignores_disjoint_run_slots_and_holes() {
    let at = |offset: u32| {
        Address::new(
            "local:call-run-havoc".into(),
            AddressOffset::constant(i64::from(offset)),
        )
    };
    let value = ProgramValue::Int32(OldMachineTerm::constant(7));
    let facts = PureFactContext::new();
    for bytes in [1u32, 5] {
        // Write inside the word starting at byte 4. Five bytes also reach
        // the word starting at byte 8.
        let ranges = [MemoryRange::new_with_element_width(
            at(4),
            1u32.into(),
            (1 + bytes).into(),
            1,
        )];
        let samples = [16, 64, 256, 1024].map(|count| {
            let _session = crate::kernel::VerificationSession::enter();
            let start = at(0);
            let mut before = SymbolicMemory::new()
                .with_block(start.base.clone(), count * 4)
                .seed_fresh_declared_runs(
                    &start,
                    &[ConstantRun {
                        offset: 0,
                        stride: 4,
                        count,
                        value: value.clone(),
                    }],
                );
            for index in (4..count).step_by(2) {
                Arc::make_mut(&mut before.cells).remove(&at(index * 4));
            }
            let transition = || {
                let after =
                    before
                        .clone()
                        .with_call_memory_havoc(Variable(944_021), &ranges, &facts, None);
                assert!(after.matches_call_memory_havoc_result(&before, &ranges, &facts, None));
                after
            };
            let (after, work) = crate::instrumentation::measure_deterministic_work(transition);
            assert_eq!(after.known_value(&at(4)), None);
            assert!(after.has_initialized_bytes_at(&at(4), 4));
            if bytes == 5 {
                assert_eq!(after.known_value(&at(8)), None);
                assert!(after.has_initialized_bytes_at(&at(8), 4));
            } else {
                assert_eq!(after.known_value(&at(8)), Some(value.clone()));
            }
            for offset in [0, 12, (count - 1) * 4] {
                assert_eq!(after.known_value(&at(offset)), Some(value.clone()));
            }
            assert_eq!(after.known_value(&at(16)), None);
            let (reference, reference_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(transition)
                });
            assert_eq!(after, reference);
            (work, reference_work)
        });
        assert!(
            samples.iter().all(|(work, _)| *work <= samples[0].0 + 32),
            "{samples:?}"
        );
        assert!(samples[3].1 > samples[0].1 + 128, "{samples:?}");
    }
}
