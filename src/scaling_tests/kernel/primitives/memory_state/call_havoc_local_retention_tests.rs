// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `call_havoc_local_retention_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn local_initialization_havoc_checks_scale_with_changed_cells() {
    let target = Address {
        base: "local:target".into(),
        offset: AddressOffset::Constant(0),
    };
    let range = MemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1);
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut before = SymbolicMemory::new()
            .with_block(target.base.clone(), 8)
            .store(
                target.clone(),
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
        for index in 0..count {
            let pointer = Address {
                base: format!("local:ambient-{index}").into(),
                offset: AddressOffset::Constant(0),
            };
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
        let at = |offset| Address {
            base: "local:byte-havoc".into(),
            offset: AddressOffset::Constant(offset),
        };
        // The call writes byte 33. The cached word at byte 32 overlaps even
        // though its starting address lies before the write range.
        let range = MemoryRange::new_with_element_width(at(4), 29u32.into(), 30u32.into(), 1);
        let ranges = std::slice::from_ref(&range);
        let value = ProgramValue::Int32(MachineTerm::constant(7));
        let mut samples = Vec::new();

        for count in [4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut before = SymbolicMemory::new()
                .with_block(at(0).base, 2048)
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
            let (after, work) = crate::instrumentation::measure_deterministic_work(&transition);
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
