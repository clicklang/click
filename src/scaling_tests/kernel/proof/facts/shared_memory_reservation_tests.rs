// Scaling tests of `src/kernel/proof/facts.rs` (module `shared_memory_reservation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A function's entry states one loadability fact per object, each over the
/// one entry memory that holds every object. Building the proof's fact set
/// reserves that memory's variables once, not once per fact, so its work
/// grows with the objects and not with their square (issues/scaling.md,
/// cause 8).
#[test]
fn facts_over_one_memory_reserve_its_variables_once() {
    let samples = [16u64, 64, 256].map(|size| {
        let pointer = |index: u64| Pointer {
            block: PointerBlock::ExternalObject(Variable(7_100_000 + index)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = (0..size).fold(CMemory::new(), |memory, index| {
            memory.store(
                pointer(index),
                CValue::Int32(Bitvector32Term::Variable(Variable(7_200_000 + index))),
            )
        });
        crate::kernel::intern_c_memory(memory.clone());
        let facts = (0..size)
            .map(|index| Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: pointer(index),
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            })
            .collect::<Vec<_>>();
        let (built, work) =
            crate::persistent::measure_persistent_work(|| ProofFacts::from_ordered(&facts));
        assert!((0..size).all(|index| {
            built.reserves_variable(Variable(7_100_000 + index))
                && built.reserves_variable(Variable(7_200_000 + index))
        }));
        (size, work)
    });
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 6, "{samples:?}");
    }
}
