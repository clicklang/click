// Scaling tests of `src/kernel/resource_tracker/cell_source.rs` (module
// `unsigned_index_membership_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Placing `src[k]` in `src[0..4]` by `k < 4`, and checking that evidence, is
/// a handful of keyed lookups: it costs the same beside 4, 8, 16 and 32
/// unrelated order facts, separations and recorded stores.
#[test]
fn unsigned_index_membership_ignores_unrelated_facts_and_stores() {
    let mut samples = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let src = Pointer::symbolic(Variable(9_903_000));
        let dst = Pointer::symbolic(Variable(9_903_001));
        let k = Variable(9_903_002);
        let read = byte_at(&src, k);
        let range = bytes(&src, 4);
        let mut context = PureFactContext::new()
            .assume_condition(below(k, 4), true)
            .assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(bytes(&dst, 5))),
                right: Box::new(CResource::Memory(range.clone())),
            });
        let mut memory = CMemory::new();
        for index in 0..size {
            // Another index under another bound, on the same base.
            let other = Variable(9_904_000 + index);
            context = context.assume_condition(below(other, 4 + index), true);
            // An unrelated separation of two other buffers.
            context = context.assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(bytes(
                    &Pointer::symbolic(Variable(9_905_000 + index * 2)),
                    4,
                ))),
                right: Box::new(CResource::Memory(bytes(
                    &Pointer::symbolic(Variable(9_905_001 + index * 2)),
                    4,
                ))),
            });
            // A store to another object, and the effect fact it records.
            let target = Pointer::symbolic(Variable(9_906_000 + index));
            let before = memory.clone();
            memory = memory.store(target.clone(), CValue::UInt8(0u32.into()));
            context = context.assume_proposition(Proposition::CMemoryMutatesOnly {
                before,
                after: memory.clone(),
                writes: vec![(target, 1)],
            });
        }
        let (membership, find_work) = crate::instrumentation::measure_deterministic_work(|| {
            PointerInRangeEvidence::for_pointer(&read, &range, &context)
        });
        let membership = membership.expect("k < 4 places src[k] in src[0..4]");
        assert!(matches!(
            membership,
            PointerInRangeEvidence::UnsignedIndexed { .. }
        ));
        let (checked, check_work) = crate::instrumentation::measure_deterministic_work(|| {
            membership.checks(&read, &range, &context)
        });
        assert!(checked);
        // One unit each, at every size (measured 2026-10-16).
        assert!(find_work <= 2 && check_work <= 2, "size={size}, find={find_work}, check={check_work}");
        samples.push((find_work, check_work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts and stores changed membership work: {samples:?}"
    );
}
