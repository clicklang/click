use super::*;
use crate::kernel::assumptions::PointerDomain;

#[test]
fn an_opaque_candidate_does_not_walk_its_unusable_memory_frame() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = OldAddress {
            base: "opaque-frame".into(),
            offset: OldAddressOffset::Constant(0).into(),
        };
        let base = SymbolicMemory::new();
        let raw = OldAddress::symbolic(Variable(995_080));
        let previous = OldPointer::new(
            OldAddress::loaded_value(&intern_memory_ref(&base), &field),
            ProgramType::Int32Pointer,
        )
        .with_address(raw.clone());
        let alias = OldPointer::new(
            OldAddress::symbolic(Variable(995_081)),
            ProgramType::Int32Pointer,
        );
        assert!(!alias.bounds_are_known());
        let context = PureFactContext::new()
            .assume_condition(OldConditionTerm::pointer_equal(previous, alias), true);
        let mut memory = base;
        for index in 0..size {
            memory = memory.store(
                field.clone().offset_by_bytes((8 + index * 8) as u32),
                ProgramValue::UInt64(OldMachineTerm::uint64_constant(index)),
            );
        }
        let current = OldPointer::new(
            OldAddress::loaded_value(&intern_memory_ref(&memory), &field),
            ProgramType::Int32Pointer,
        )
        .with_address(raw);
        let (value, work) =
            crate::instrumentation::measure_deterministic_work(|| context.pointer_domain(&current));
        assert_eq!(value, PointerDomain::Unknown);
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
        let pointer = |id| OldAddress::symbolic(Variable(963_000 + id));
        let value = |id| OldPointer::new(pointer(id), ProgramType::Int32Pointer);
        let mut facts = PureFactContext::new();
        for index in 1..=size {
            facts = facts.assume_condition(
                OldConditionTerm::pointer_equal(value(0), value(index)),
                true,
            );
        }
        assert!(facts.provenance_equal(&pointer(0), &pointer(size)));
        assert!(facts.bounds_owners_equal(&pointer(0), &pointer(size)));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!facts.provenance_equal(&pointer(0), &pointer(size + 1)));
                assert!(!facts.bounds_owners_equal(&pointer(0), &pointer(size + 1)));
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
        let field = OldAddress::symbolic(Variable(964_000));
        let raw = OldAddress::symbolic(Variable(964_001));
        let alias = OldPointer::new(
            OldAddress::symbolic(Variable(964_002)),
            ProgramType::Int32Pointer,
        );
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let memory = SymbolicMemory::new().store(
                field.offset_by_bytes(8),
                ProgramValue::UInt64(OldMachineTerm::uint64_constant(index)),
            );
            let source = OldPointer::new(
                OldAddress::loaded_value(&intern_memory_ref(&memory), &field),
                ProgramType::Int32Pointer,
            )
            .with_address(raw.clone());
            facts = facts
                .assume_condition(OldConditionTerm::pointer_equal(source, alias.clone()), true);
        }
        let current = OldPointer::new(
            OldAddress::loaded_value(&intern_memory_ref(&SymbolicMemory::new()), &field),
            ProgramType::Int32Pointer,
        )
        .with_address(raw);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert_eq!(facts.pointer_domain(&current), PointerDomain::Unknown);
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
