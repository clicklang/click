use super::*;

#[test]
fn an_opaque_candidate_does_not_walk_its_unusable_memory_frame() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "opaque-frame".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base = CMemory::new();
        let raw = Pointer::symbolic(Variable(995_080));
        let previous = CPointerValue::new(
            Pointer::loaded_value(&intern_c_memory_ref(&base), &field),
            CType::Int32Pointer,
        )
        .with_address(raw.clone());
        let alias = CPointerValue::new(Pointer::symbolic(Variable(995_081)), CType::Int32Pointer);
        assert!(!alias.extent_is_known());
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_value_equal(previous, alias), true);
        let mut memory = base;
        for index in 0..size {
            memory = memory.store(
                field.clone().offset_by_bytes((8 + index * 8) as u32),
                CValue::UInt64(Bitvector32Term::UInt64Constant(index)),
            );
        }
        let current = CPointerValue::new(
            Pointer::loaded_value(&intern_c_memory_ref(&memory), &field),
            CType::Int32Pointer,
        )
        .with_address(raw);
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.known_value_of_framed_pointer_read(&current)
        });
        assert!(value.is_none());
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
        "{costs:?}"
    );
}
