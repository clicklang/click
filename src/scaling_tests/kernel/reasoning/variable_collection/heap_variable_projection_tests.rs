// Scaling tests of `src/kernel/reasoning/variable_collection.rs` (module `heap_variable_projection_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn heap_variable_counts_follow_local_edits_and_keep_siblings_isolated() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| Pointer {
            block: PointerBlock::Symbolic(Variable(id)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut heap = crate::kernel::primitives::CHeapMemory::default();
        for id in 1..=size {
            heap.uninitialized_objects.insert(pointer(id), 4);
        }
        let heap = std::sync::Arc::new(heap);
        let original = heap_variable_counts(&heap, WholeCount::Charged);
        let selected = CMemory {
            heap: heap.clone(),
            ..CMemory::new().with_block("selected:read", 4)
        };
        let (projected, work) = crate::instrumentation::measure_deterministic_work(|| {
            counts_whole(&selected, WholeCount::Charged)
        });
        assert_eq!(projected, original);
        assert_eq!(work, 1, "a selected read enumerated {size} heap entries");
        let mut changed = (*heap).clone();
        changed.uninitialized_objects.remove(&pointer(1));
        changed.uninitialized_objects.insert(pointer(10_000), 4);
        let changed = std::sync::Arc::new(changed);
        let (counts, work) = crate::instrumentation::measure_deterministic_work(|| {
            heap_variable_counts(&changed, WholeCount::Charged)
        });
        assert!(!counts.contains_key(&Variable(1)));
        assert!(counts.contains_key(&Variable(10_000)));
        assert_eq!(counts.len(), size as usize);
        assert!(work <= 4, "local heap edit walked {size} objects: {work}");
        assert_eq!(heap_variable_counts(&heap, WholeCount::Charged), original);
        let empty = std::sync::Arc::new(crate::kernel::primitives::CHeapMemory::default());
        assert!(heap_variable_counts(&empty, WholeCount::Charged).is_empty());
        assert_eq!(heap_variable_counts(&changed, WholeCount::Charged), counts);
    }
}
