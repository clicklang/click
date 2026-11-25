// Scaling tests of `src/kernel/equality_graph/storage_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn automatic_storage_lookup_does_not_walk_alias_history() {
    let root = Address::symbolic(Variable(896_100));
    let storage = Address {
        base: AddressBase::AutomaticLocal {
            binding: crate::kernel::LocalBindingId::new(
                crate::kernel::LocalFunctionId::new(Some("indexed.c".into()), "f".into()),
                false,
                0,
                Some("indexed".into()),
            ),
            instance: crate::kernel::LocalStorageInstance::Implicit,
        },
        offset: OldAddressOffset::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new().assume_condition(
            OldConditionTerm::address_equal(root.clone(), storage.clone()),
            true,
        );
        for id in 1..=size {
            facts = facts.assume_condition(
                OldConditionTerm::address_equal(
                    root.clone(),
                    Address::symbolic(Variable(897_000 + id)),
                ),
                true,
            );
        }
        let query = Address::symbolic(Variable(897_000 + size)).offset_by_bytes(8);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.equality_graph.storage_address(&query),
                storage.offset_by_bytes(8)
            );
            assert_eq!(
                facts.equality_graph.local_slot_alias_blocks(&query),
                vec![storage.base.clone()]
            );
        });
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 40,
        "storage query walked the equality history: {samples:?}"
    );
}

#[test]
fn declared_alignment_lookup_does_not_walk_alias_history() {
    let root = Address::symbolic(Variable(899_100));
    let mut work = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for id in 1..=size {
            facts = facts.assume_condition(
                OldConditionTerm::address_equal(
                    root.clone(),
                    Address::symbolic(Variable(900_000 + id)),
                ),
                true,
            );
        }
        // Register after all equality merges as well as before them above.
        facts = facts.assume_condition(OldConditionTerm::pointer_aligned(root.clone(), 16), true);
        let query = Address::symbolic(Variable(900_000 + size)).offset_by_bytes(8);
        let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.decide(&OldConditionTerm::pointer_aligned(query.clone(), 8)),
                Some(true)
            );
            assert_eq!(
                facts.decide(&OldConditionTerm::pointer_aligned(query, 16)),
                Some(false)
            );
        });
        work.push(units);
    }
    assert!(
        work[3] <= work[0] + 80,
        "alignment walked aliases: {work:?}"
    );
}
