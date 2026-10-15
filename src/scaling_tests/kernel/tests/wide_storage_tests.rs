// Scaling tests of `src/kernel/tests/wide_storage_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_storage_exact_load_and_validation_work_ignore_unrelated_memory() {
    let value = literal(c_uint128_literal(u128::MAX));
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut memory = CMemory::new()
            .with_block("local:wide-storage", 16)
            .store(address(0), value.clone());
        for index in 0..size {
            let pointer = Pointer {
                block: format!("wide-unrelated-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer, literal(c_int32_literal(index)));
        }
        let raw = Bitvector32Term::MemoryLoad(
            intern_c_memory(memory.clone()),
            Box::new(address(0)),
            LoadKind::UInt128,
        );
        let state = CState::new().with_memory(memory);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(MachineIntegerType::UInt128.accepts_wide_term(&raw));
            paths(&state, &load(address(0), CType::UInt128))
        });
        assert_eq!(result[0].outcome, CExpressionOutcome::Value(value.clone()));
        assert!(work < 4096, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
        "{samples:?}"
    );
}
