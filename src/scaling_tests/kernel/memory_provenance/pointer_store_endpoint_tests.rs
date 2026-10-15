// Scaling tests of `src/kernel/memory_provenance.rs` (module `pointer_store_endpoint_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// The endpoint rule checks a full typed pointer and its exact address;
/// it cannot answer from an older store, missing alias, or partial bytes.
#[test]
fn selected_pointer_store_endpoint_preserves_width_history_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = |id| {
        Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(id)),
            4,
        )
    };
    let written = base(160_001).offset_by_bytes(8);
    let address = base(160_002).offset_by_bytes(8);
    let alias = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(base(160_001), base(160_002)),
        true,
    );
    let endpoint = |memory: CMemory| MemoryDagCell::Unwritten {
        node: intern_c_memory(memory),
        path: Vec::new(),
    };
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new().assume_proposition(alias.clone());
        let mut memory = CMemory::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(170_000 + index * 2)),
                    Pointer::symbolic(Variable(170_001 + index * 2)),
                ),
                true,
            );
            memory = memory.store(
                written.offset_by_bytes(32 + index as u32 * 8),
                CValue::UInt64(Bitvector32Term::UInt64Constant(index)),
            );
        }
        let stored = Pointer::symbolic(Variable(180_000 + count));
        memory = memory.store(
            written.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        let cell = endpoint(memory.clone());
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_value_at_stopping_store(&cell, &address, LoadKind::Bits32, 8, &context)
        });
        assert_eq!(value, Some(CPointerValue::new(stored.clone(), CType::Int32Pointer)));
        samples.push(work);
        for (kind, bytes) in [
            (LoadKind::Bits32, 4),
            (LoadKind::Bits32, 16),
            (LoadKind::Bits64, 8),
        ] {
            assert!(
                pointer_value_at_stopping_store(&cell, &address, kind, bytes, &context).is_none()
            );
        }
        assert!(
            pointer_value_at_stopping_store(
                &cell,
                &address,
                LoadKind::Bits32,
                8,
                &context.without_exact_fact(&alias)
            )
            .is_none()
        );
        assert!(
            pointer_value_at_stopping_store(
                &cell,
                &address.offset_by_bytes(4),
                LoadKind::Bits32,
                8,
                &context
            )
            .is_none()
        );
        // Same offset in another object is not the stored address.
        assert!(
            pointer_value_at_stopping_store(
                &cell,
                &Pointer::symbolic(Variable(190_000 + count)).offset_by_bytes(8),
                LoadKind::Bits32,
                8,
                &context
            )
            .is_none()
        );
        let overwritten = endpoint(memory.clone().store(
            written.clone(),
            CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
        ));
        assert_eq!(
            pointer_value_at_stopping_store(&overwritten, &address, LoadKind::Bits32, 8, &context),
            Some(CPointerValue::new(Pointer::null(), CType::Int32Pointer))
        );
        assert_ne!(
            pointer_value_at_stopping_store(&overwritten, &address, LoadKind::Bits32, 8, &context),
            Some(CPointerValue::new(stored, CType::Int32Pointer))
        );
        for offset in [0, 4, 32] {
            let changed = endpoint(memory.clone().store(
                written.offset_by_bytes(offset),
                CValue::Int32(Bitvector32Term::Constant(1)),
            ));
            assert!(
                pointer_value_at_stopping_store(&changed, &address, LoadKind::Bits32, 8, &context)
                    .is_none()
            );
        }
    }
    assert!(samples[3] <= samples[0] * 4 + 64, "{samples:?}");
}
