// Scaling tests of `src/kernel/functions.rs` (module `population_creation_frame_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn automatic_lifetime_reuse_tracks_exact_memory_and_retired_blocks() {
    for size in [16usize, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let blocks = (0..size)
            .map(|i| PointerBlock::from(format!("local:lifetime:memo_{i}")))
            .collect::<Vec<_>>();
        let before = blocks.iter().fold(CMemory::new(), |memory, block| {
            memory.with_block(block.clone(), 4)
        });
        let after = retire_automatic_lifetime_blocks(&before, &blocks);
        let (repeated, work) = crate::instrumentation::measure_deterministic_work(|| {
            retire_automatic_lifetime_blocks(&before, &blocks)
        });
        assert_eq!(after, repeated);
        assert!(
            work <= size + 1,
            "retiring {size} exact blocks again rebuilt memory: {work}"
        );
        for block in &blocks {
            assert!(!after.has_block(block));
            assert!(after.is_ended_local_block(block));
        }
        // A sibling input must not evict the result needed when checking
        // this branch again after execution has visited other outcomes.
        let sibling = before.clone().with_block("caller:sibling", 4);
        retire_automatic_lifetime_blocks(&sibling, &blocks);
        let (interleaved, work) = crate::instrumentation::measure_deterministic_work(|| {
            retire_automatic_lifetime_blocks(&before, &blocks)
        });
        assert_eq!(interleaved, after);
        assert!(
            work <= size + 1,
            "interleaved retirement rebuilt {size} blocks: {work}"
        );
        let partial = retire_automatic_lifetime_blocks(&before, &blocks[..size - 1]);
        assert!(partial.has_block(&blocks[size - 1]));
        let changed = before.clone().with_block("caller:preserved", 8);
        let changed_after = retire_automatic_lifetime_blocks(&changed, &blocks);
        assert!(changed_after.has_block(&PointerBlock::from("caller:preserved")));
        assert!(!after.has_block(&PointerBlock::from("caller:preserved")));
    }
}
