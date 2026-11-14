use super::*;

#[test]
fn an_opaque_candidate_does_not_walk_its_unusable_memory_frame() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "opaque-frame".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base = Memory::new();
        let raw = Pointer::symbolic(Variable(995_080));
        let previous = PointerValue::new(
            Pointer::loaded_value(&intern_c_memory_ref(&base), &field),
            ProgramType::Int32Pointer,
        )
        .with_address(raw.clone());
        let alias = PointerValue::new(
            Pointer::symbolic(Variable(995_081)),
            ProgramType::Int32Pointer,
        );
        assert!(!alias.extent_is_known());
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_value_equal(previous, alias), true);
        let mut memory = base;
        for index in 0..size {
            memory = memory.store(
                field.clone().offset_by_bytes((8 + index * 8) as u32),
                ProgramValue::UInt64(MachineTerm::uint64_constant(index)),
            );
        }
        let current = PointerValue::new(
            Pointer::loaded_value(&intern_c_memory_ref(&memory), &field),
            ProgramType::Int32Pointer,
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

#[test]
fn provenance_misses_do_not_enumerate_direct_alias_stars() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| Pointer::symbolic(Variable(963_000 + id));
        let value = |id| PointerValue::new(pointer(id), ProgramType::Int32Pointer);
        let mut facts = PureFactContext::new();
        for index in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_value_equal(value(0), value(index)),
                true,
            );
        }
        assert!(facts.designations_equal(&pointer(0), &pointer(size)));
        assert!(facts.opaque_extents_equal(&pointer(0), &pointer(size)));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!facts.designations_equal(&pointer(0), &pointer(size + 1)));
                assert!(!facts.opaque_extents_equal(&pointer(0), &pointer(size + 1)));
            }
        });
        samples.push(work);
    }
    eprintln!("provenance alias-star misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn framed_pointer_refusals_do_not_scan_same_address_sources() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(964_000));
        let raw = Pointer::symbolic(Variable(964_001));
        let alias = PointerValue::new(
            Pointer::symbolic(Variable(964_002)),
            ProgramType::Int32Pointer,
        );
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let memory = Memory::new().store(
                field.offset_by_bytes(8),
                ProgramValue::UInt64(MachineTerm::uint64_constant(index)),
            );
            let source = PointerValue::new(
                Pointer::loaded_value(&intern_c_memory_ref(&memory), &field),
                ProgramType::Int32Pointer,
            )
            .with_address(raw.clone());
            facts = facts.assume_condition(
                ConditionTerm::pointer_value_equal(source, alias.clone()),
                true,
            );
        }
        let current = PointerValue::new(
            Pointer::loaded_value(&intern_c_memory_ref(&Memory::new()), &field),
            ProgramType::Int32Pointer,
        )
        .with_address(raw);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(facts.known_value_of_framed_pointer_read(&current).is_none());
            }
        });
        samples.push(work);
    }
    eprintln!("framed pointer source misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
