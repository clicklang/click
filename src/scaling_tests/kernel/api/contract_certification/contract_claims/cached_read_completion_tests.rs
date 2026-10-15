// Scaling tests of `src/kernel/api/contract_certification/contract_claims.rs` (module `cached_read_completion_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn cached_read_completion_work_ignores_ambient_cells_and_range_length() {
    for size in [32, 128, 512, 2048] {
        let memory = (0..size).fold(CMemory::new(), |memory, index| {
            memory.store(
                pointer("ambient", index * 4),
                int32(u32::try_from(index).unwrap()),
            )
        });
        let first = cache(&memory, &memory, 2, 4);
        let second = cache(&first, &first, 10_000_000, 4);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            memories_match_up_to_cached_reads(&second, &memory)
        });
        assert!(matches);
        assert!(work <= 4, "size={size}, work={work}");
    }
}
