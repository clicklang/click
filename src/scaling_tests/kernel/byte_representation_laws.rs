use super::*;

#[test]
fn representation_axiom_has_fixed_work_at_distant_word_addresses() {
    let work = [0, 16, 1024, 1_000_000].map(|offset| {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(8_390_002)).offset_by_bytes(offset);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            prove_uint32_from_le_bytes(CPointerValue::new(pointer, CType::UInt32Pointer))
        });
        result.expect("representation axiom");
        work
    });
    assert!(work[0] > 0);
    assert!(work.iter().all(|n| *n == work[0]), "{work:?}");
}

#[test]
fn target_fact_lowering_ignores_unrelated_state_and_store_history() {
    let costs = [4, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(8_390_003));
        let mut memory = CMemory::new();
        for index in 0..size {
            memory = memory.store(
                base.offset_by_bytes(index * 4),
                CValue::UInt32(index.into()),
            );
        }
        let state = CState::new().with_memory(memory);
        let proposition = SpecProposition::Predicate {
            resource_state_dependent: false,
            name: LITTLE_ENDIAN_PREDICATE_NAME.into(),
            arguments: vec![],
        };
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::c_lower_spec_proposition_at_state(
                &state,
                &proposition,
                Some(&state),
                &PureFactContext::new(),
            )
        });
        let (fact, _, _) = lowered.unwrap();
        assert_eq!(fact, CExecutionEnvironment::new().byte_order_fact());
        assert_ne!(
            fact,
            CExecutionEnvironment::new()
                .with_byte_order(ByteOrder::Big)
                .byte_order_fact()
        );
        work
    });
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
