// Scaling tests of `src/kernel/loops.rs` (module `contract_exit_join_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn contract_exit_marker_join_work_is_linear_in_exits_and_skips_ambient_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for count in [4usize, 64, 1024] {
        let exits = marker_exits(count, 4);
        let (successor, work) = measured_join(&exits);
        samples.push((count, work));
        assert!(work > 0 && work <= count * 30 + 32, "{samples:?}");
        assert_eq!(successor.memory.cells, exits[0].memory.cells);
        assert_eq!(
            crate::kernel::reasoning::memory_resolution::havoc_marker_blocks(
                &successor.memory.blocks
            )
            .count(),
            2
        );
    }
    eprintln!("(exits, marker join work): {samples:?}");
    let mut ambient_work = Vec::new();
    for ambient in [4usize, 64, 1024] {
        let (_, work) = measured_join(&marker_exits(4, ambient));
        ambient_work.push(work);
    }
    assert!(
        ambient_work.iter().all(|work| *work <= ambient_work[0] * 2),
        "{ambient_work:?}"
    );
}

#[test]
fn optional_exit_cache_reconciliation_does_not_walk_unrelated_store_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "shared".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: "other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for count in [4usize, 64, 1024] {
        let mut memory = CMemory::new()
            .with_block("shared", 4)
            .with_block("other", 4);
        for index in 0..count {
            memory = memory.store(other.clone(), int32(index as u32));
        }
        let mut exits = [
            CState::new().with_memory(memory.clone().store(pointer.clone(), int32(0))),
            CState::new().with_memory(memory),
        ];
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            retain_proven_loop_exit_cells(
                &mut exits,
                &[&ExecutionFacts::new(), &ExecutionFacts::new()],
                &PureFactContext::new(),
                true,
            )
        });
        result.unwrap();
        assert!(exits[1].memory().known_value(&pointer).is_none());
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] * 2),
        "{samples:?}"
    );
    eprintln!("optional cache lookup work at 4/64/1024 old stores: {samples:?}");
}
