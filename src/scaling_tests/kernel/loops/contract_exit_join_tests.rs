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
                &[],
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

/// The exit join indexes each exit's facts once. Cache reconciliation reads
/// the contexts the join already built for its binders instead of assuming
/// the same exit facts a second time, so with them it rebuilds no context
/// entries however many facts an exit carries. Rebuilding them cost the
/// `flips_red_all` loop's exit join about 134,000 control units.
#[test]
fn exit_cache_reconciliation_reuses_the_joins_exit_contexts() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::Concrete("shared".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("shared", 4);
    // Name the cell's load, as the exit's own read did.
    let load = symbolic_storage_cell_value(&memory, &pointer, CType::Int32, true).unwrap();
    let zero = int32(0);
    let exits = || {
        [
            CState::new().with_memory(memory.clone().store(pointer.clone(), zero.clone())),
            CState::new().with_memory(memory.clone()),
        ]
    };
    let mut rebuilt = Vec::new();
    let mut reused = Vec::new();
    for count in [4usize, 16, 64, 256] {
        let mut facts = (0..count)
            .map(|k| {
                ExecutionPureFact::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(926_000 + k as u64)),
                        Bitvector32Term::Constant(k as u32),
                    ),
                    true,
                ))
            })
            .collect::<Vec<_>>();
        facts.push(ExecutionPureFact::new(
            c_value_comparison_proposition(&load, CComparisonOperator::Equal, &zero).unwrap(),
        ));
        let exit_facts = ExecutionFacts::from(facts);
        let empty = ExecutionFacts::new();
        let all = [&empty, &exit_facts];

        let mut states = exits();
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        retain_proven_loop_exit_cells(&mut states, &all, &[], &PureFactContext::new(), true)
            .unwrap();
        rebuilt.push(crate::kernel::reasoning::path_facts::context_rebuild_entries() - before);
        assert_eq!(states[1].memory().known_value(&pointer), Some(zero.clone()));

        let built = loop_exit_argument_contexts(&all, &PureFactContext::new(), true);
        let mut states = exits();
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        retain_proven_loop_exit_cells(&mut states, &all, &built, &PureFactContext::new(), true)
            .unwrap();
        reused.push(crate::kernel::reasoning::path_facts::context_rebuild_entries() - before);
        assert_eq!(states[1].memory().known_value(&pointer), Some(zero.clone()));
    }
    assert!(
        rebuilt
            .iter()
            .zip([4usize, 16, 64, 256])
            .all(|(entries, count)| *entries > count),
        "without the join's contexts an exit's facts are assumed here: {rebuilt:?}"
    );
    assert!(
        reused.iter().all(|entries| *entries == 0),
        "reconciliation assumed exit facts the join already indexed: {reused:?}"
    );
}
