// Scaling tests of `src/kernel/equality_graph/storage_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn concrete_storage_lookup_does_not_walk_alias_history() {
    let root = Pointer::symbolic(Variable(896_100));
    let storage = Pointer {
        block: "local:indexed".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(root.clone(), storage.clone()),
            true,
        );
        for id in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    root.clone(),
                    Pointer::symbolic(Variable(897_000 + id)),
                ),
                true,
            );
        }
        let query = Pointer::symbolic(Variable(897_000 + size)).offset_by_bytes(8);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.equality_graph.storage_address(&query),
                storage.offset_by_bytes(8)
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
    let root = Pointer::symbolic(Variable(899_100));
    let mut work = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for id in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    root.clone(),
                    Pointer::symbolic(Variable(900_000 + id)),
                ),
                true,
            );
        }
        // Register after all equality merges as well as before them above.
        facts = facts.assume_condition(ConditionTerm::pointer_aligned(root.clone(), 16), true);
        let query = Pointer::symbolic(Variable(900_000 + size)).offset_by_bytes(8);
        let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.decide(&ConditionTerm::pointer_aligned(query.clone(), 8)),
                Some(true)
            );
            assert_eq!(
                facts.decide(&ConditionTerm::pointer_aligned(query, 16)),
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
