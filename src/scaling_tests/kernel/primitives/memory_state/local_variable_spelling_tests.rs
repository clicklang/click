// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `local_variable_spelling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;

// The held-term index answers from the locals that hold the variable, so
// declaring more unrelated locals adds no work.
#[test]
fn local_variable_spelling_work_does_not_grow_with_declared_slots() {
    for size in [4usize, 16, 64, 256, 1024] {
        let state = (0..size).fold(ExecutionState::new(), |state, index| {
            scalar(
                state,
                &format!("noise_{index:04}"),
                ProgramValue::Int32(MachineTerm::constant(0)),
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
        let nested = (0..depth).fold(MachineTerm::Variable(variable), |term, _| {
            binary_node!(
                Int32,
                Add,
                Box::new(MachineTerm::constant(0)),
                Box::new(term)
            )
        });
        let state = scalar(ExecutionState::new(), "noise", ProgramValue::Int32(nested));
        let base = Pointer {
            block: "unrelated-heap".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = state.memory().clone().with_seeded_cells(
            base,
            4,
            ProgramType::Int32,
            0,
            1_000_000,
            Memory::new().into(),
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

#[test]
fn declaration_reference_and_shadow_lookup_are_indexed() {
    for size in [1u32, 16, 256] {
        let owner = LocalFunctionId::new(None, "indexed".into());
        let mut locals = LocalEnvironment::new();
        let mut shadowed = Vec::new();
        for ordinal in 0..size {
            let noise = LocalBindingId::new(
                owner.clone(),
                false,
                ordinal * 2,
                Some(format!("noise_{ordinal}")),
            );
            locals.set(noise, int32(0));
            let selected = LocalBindingId::new(
                owner.clone(),
                false,
                ordinal * 2 + 1,
                Some("selected".into()),
            )
            .with_scope_depth(ordinal);
            locals.set(selected.clone(), int32(ordinal));
            shadowed.push(selected);
        }
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            assert_eq!(
                locals.get("selected").unwrap().native().as_ref(),
                &int32(size - 1)
            );
            assert_eq!(
                locals.get(shadowed[0].clone()).unwrap().native().as_ref(),
                &int32(0)
            );
        });
        assert!(
            work <= 6 * (size.ilog2() as usize + 1) + 12,
            "{size}: {work}"
        );
        if size > 1 {
            locals.remove(shadowed.pop().unwrap());
            assert_eq!(
                locals.get("selected").unwrap().native().as_ref(),
                &int32(size - 2)
            );
        }
    }
}
