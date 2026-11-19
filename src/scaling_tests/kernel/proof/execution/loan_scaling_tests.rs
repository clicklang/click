// Scaling tests of `src/kernel/proof/execution.rs` (module `loan_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn interface_binding_inheritance_visits_only_claimed_bindings() {
    for count in [16, 64, 256] {
        for claimed in [0, 1, count] {
            let (arm, successor) = interface_join_states(count, claimed);
            let empty = ExecutionState::new();
            let (inherited, work) = crate::instrumentation::measure_deterministic_work(|| {
                interface_successor_loans_are_inherited(&successor, [&empty, &arm])
            });
            assert!(inherited);
            assert_eq!(work, 2 * claimed, "{count} held, {claimed} claimed");

            // A miss also costs only a lookup in each arm, even when the
            // missing binding describes a resource at a fresh occurrence.
            let (other, _) = interface_join_states(count, 0);
            let (inherited, work) = crate::instrumentation::measure_deterministic_work(|| {
                interface_successor_loans_are_inherited(&successor, [&other, &other])
            });
            assert_eq!(inherited, claimed == 0);
            assert_eq!(work, if claimed == 0 { 0 } else { 2 });
        }
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
                !havoced.has_known_cell_at(&Address {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::Constant(4 * index as i64),
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
        let memory = SymbolicMemory::new().store(pointer.clone(), int32(7));
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
