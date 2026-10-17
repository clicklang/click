// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `local_variable_spelling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// The held-term index answers from the locals that hold the variable, so
// declaring more unrelated locals adds no work.
#[test]
fn local_variable_spelling_work_does_not_grow_with_declared_slots() {
    for size in [4usize, 16, 64, 256, 1024] {
        let state = (0..size).fold(CState::new(), |state, index| {
            scalar(
                state,
                &format!("noise_{index:04}"),
                CValue::Int32(Bitvector32Term::Constant(0)),
            )
        });
        let (name, work) = crate::instrumentation::measure_deterministic_work(|| {
            state.local_name_holding_bitvector_variable(Variable(971_011))
        });
        assert_eq!(name, None);
        assert!(
            work <= 2,
            "size {size}: {work} work must not scale with unrelated slots"
        );
    }
}

#[test]
fn local_variable_spelling_does_not_traverse_unrelated_symbolic_values_or_heap_runs() {
    let variable = Variable(971_012);
    for depth in [4usize, 16, 64, 256, 1024] {
        let nested = (0..depth).fold(Bitvector32Term::Variable(variable), |term, _| {
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(0)), Box::new(term))
        });
        let state = scalar(CState::new(), "noise", CValue::Int32(nested));
        let base = Pointer {
            block: "unrelated-heap".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = state.memory().clone().with_seeded_cells(
            base,
            4,
            CType::Int32,
            0,
            1_000_000,
            CMemory::new().into(),
        );
        let state = state.with_memory(memory);
        let (name, work) = crate::instrumentation::measure_deterministic_work(|| {
            state.local_name_holding_bitvector_variable(variable)
        });
        assert_eq!(
            name, None,
            "a variable inside an expression is not the held scalar atom"
        );
        assert!(
            work <= 2,
            "depth {depth}: {work} work; only the index lookup participates"
        );
    }
}
