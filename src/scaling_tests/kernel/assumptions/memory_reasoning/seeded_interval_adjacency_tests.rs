// Scaling tests of `src/kernel/assumptions/memory_reasoning.rs` (module `seeded_interval_adjacency_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn materialized_run_adjacency_preserves_holes_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: "run-adjacency".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source = crate::kernel::intern_c_memory(CMemory::new());
    let context = PureFactContext::new();
    let mut costs = Vec::new();
    for size in [16, 64, 4096, 22208, 1048576] {
        for missing in [None, Some(3), Some(size - 1)] {
            let mut holes = IndexIntervals::default();
            if let Some(index) = missing {
                holes.insert(index);
            }
            let run = CellRun::new(base.clone(), 1, CType::UInt8, size, source.clone(), holes);
            let mut memory = CMemory::new();
            std::sync::Arc::make_mut(&mut memory.cells).add_run(run);
            let memory = memory.store(
                base.offset_by_bytes(size),
                CValue::UInt8(Bitvector32Term::Constant(7)),
            );
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.adjacent_loadable_region_facts(
                    &memory,
                    &base,
                    &Bitvector32Term::Constant(size + 1),
                )
            });
            assert_eq!(facts.is_some(), missing.is_none());
            if missing.is_none() {
                let goal = Proposition::CMemoryLoadable {
                    memory,
                    base: base.clone(),
                    bytes: Bitvector32Term::Constant(size + 1),
                    wide: false,
                };
                let derivation = context.derive_atomic_proposition(&goal).unwrap();
                assert!(derivation.check(&context));
                assert!(derivation.context_premises().is_empty());
            }
            costs.push((size, work));
        }
    }
    assert!(
        costs.iter().all(|(_, work)| *work <= costs[0].1 + 256),
        "{costs:?}"
    );
}
