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
        // Validity: no cell was proven protected, so the havoc paid the
        // complete query for each one. An early refusal would short the
        // scan and make the curve look better than the checker is.
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
    // Measured, not aspirational: 65, 257, 1025, 4097 -- one query per
    // cell, each walking every symbolic protected range in the block, so
    // the curve is cells x symbolic loans and doubling costs four times
    // as much. Nothing local fixes it: a symbolic base offset cannot
    // enter the dyadic index, the block bucket already holds only the
    // genuinely symbolic entries, and a cell's answer depends on the
    // cell, so per-block hoisting cannot share it. This bound is recorded
    // as a known violation in `docs/internals/verification-efficiency.md`;
    // the assertion pins it from above so no further factor creeps in and
    // so a later indexing change that makes it linear still passes.
    for (count, work) in &samples {
        assert!(
            *work <= count * count + 4 * count + 16,
            "loop-head havoc cells x symbolic loans exceeded its known quadratic bound: {samples:?}"
        );
    }
}
