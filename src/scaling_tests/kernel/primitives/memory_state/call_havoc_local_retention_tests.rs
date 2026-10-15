// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `call_havoc_local_retention_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn local_initialization_havoc_checks_scale_with_changed_cells() {
    let target = Pointer {
        block: "local:target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = CMemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1);
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut before = CMemory::new()
            .with_block(target.block.clone(), 8)
            .store(target.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
        for index in 0..count {
            let pointer = Pointer {
                block: format!("local:ambient-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            std::sync::Arc::make_mut(&mut before.heap)
                .initialized
                .record(&pointer, 4);
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            let after = before.clone().with_call_memory_havoc(
                Variable(944_017),
                std::slice::from_ref(&range),
                &facts,
                None,
            );
            after.matches_call_memory_havoc_result(
                &before,
                std::slice::from_ref(&range),
                &facts,
                None,
            )
        });
        assert!(checked);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4 + 128),
        "ambient initialization scan: {samples:?}"
    );
}
