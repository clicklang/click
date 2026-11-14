// Scaling tests of `src/kernel/proof/execution.rs` (module `loan_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn interface_binding_inheritance_is_near_linear_in_the_binding_count() {
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64] {
        let (arm, successor) = interface_join_states(count);
        let (inherited, work) = crate::instrumentation::measure_deterministic_work(|| {
            interface_successor_loans_are_inherited(&successor, [&arm, &arm])
        });
        assert!(
            inherited,
            "every successor binding is one the arm held, so the join is admitted"
        );
        samples.push((count, work));
    }
    // 36, 136, 528, 2080 before the membership index; 24, 48, 96, 192
    // after it (both arms folded in, then one lookup per successor
    // binding). The second assertion pins the linear shape itself, so a
    // reintroduced pairwise scan fails here and not only at eight times
    // the size.
    assert_near_linear("interface join binding count", &samples);
    for (count, work) in &samples {
        assert!(
            *work <= 6 * count + 16,
            "interface join binding inheritance stopped being one pass per binding: {samples:?}"
        );
    }
}

#[test]
fn loop_head_havoc_work_over_cells_and_symbolic_loans() {
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64] {
        let ledger = symbolic_contract_input_ledger(count);
        let memory = cells_in_the_symbolic_block(count);
        let (havoced, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_loop_memory_havoc_preserving_loans(
                Variable(7),
                &BTreeSet::new(),
                None,
                Some(&ledger),
            )
        });
        // None of the symbolic loans protects these concrete addresses.
        // Before the removal, every cell searched the whole loan bucket.
        for index in 0..count {
            assert!(
                !havoced.has_known_cell_at(&Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(4 * index as i64),
                }),
                "a cell no loan protects must not survive the havoc"
            );
        }
        samples.push((count, work));
    }
    // Before: 86, 287, 1071, 4175. Indexed retention: 30, 47, 79, 143.
    assert_near_linear("loop-head havoc cells and symbolic loans", &samples);
    for (count, work) in &samples {
        assert!(
            *work <= 4 * count + 16,
            "loop-head havoc must not query every symbolic loan per cell: {samples:?}"
        );
    }
}

#[test]
fn loop_head_havoc_symbolic_read_ignores_other_loans() {
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64] {
        let ledger = symbolic_contract_input_ledger(count);
        let pointer = parameter_view(0).memory_range().unwrap().base().clone();
        let memory = Memory::new().store(pointer.clone(), int32(7));
        let (havoced, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_loop_memory_havoc_preserving_loans(
                Variable(7),
                &BTreeSet::new(),
                None,
                Some(&ledger),
            )
        });
        assert!(havoced.has_known_cell_at(&pointer));
        samples.push((count, work));
    }
    assert!(samples[0].1 > 0);
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 8),
        "one symbolic read must select its origin, not search other loans: {samples:?}"
    );
}
