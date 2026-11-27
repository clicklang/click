// Scaling tests of `src/kernel/spec/slice_operation_tests.rs`: deterministic
// work measured at several input sizes. Included into its `scaling_tests`
// module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// The work of `slice::from_raw_parts(p, n).len()` evaluated under `size`
/// unrelated slices and facts about their counts.
fn component_read_under_unrelated_facts(size: u64) -> usize {
    let mut assumptions = PureFactContext::new();
    for index in 0..size {
        let ProgramValue::Pointer(unrelated) = named_slice(969_000 + index) else {
            panic!("a slice is a pointer value");
        };
        assumptions = assumptions.assume_condition(
            OldConditionTerm::uint64_equal(
                unrelated.len().expect("a wide pointer").clone(),
                OldMachineTerm::uint64_constant(index),
            ),
            true,
        );
    }
    let read = SpecExpression::SliceLength(Box::new(from_raw_parts(
        thin(969_900),
        ProgramValue::UInt64(count(969_901)),
    )));
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    let state = ExecutionState::new();
    let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
        evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&state, None),
            &read,
            &assumptions,
            &mut budget,
        )
        .unwrap()
    });
    assert_eq!(paths.len(), 1);
    assert_eq!(
        paths[0].value.clone().into_native(),
        ProgramValue::UInt64(count(969_901))
    );
    work
}

/// A component read takes the value from its operand: its work does not grow
/// with unrelated slices and facts about their counts
/// (`design/rust-slice-values.md`, step 2b-iii-c-i).
#[test]
fn slice_component_reads_ignore_unrelated_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(component_read_under_unrelated_facts);
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] + 8, "{costs:?}");
    }
}

/// `depth` nested rebuilds (spec evaluation recurses through each, so the
/// sizes stay within the test stack), `from_raw_parts(from_raw_parts(...).as_ptr(),
/// n_k)`, each with its own count, cost a constant amount each: the work
/// grows linearly with the expression, never with what was built before.
#[test]
fn nested_slice_rebuilds_grow_linearly() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [4u64, 8, 16].map(|depth| {
        let mut expression = from_raw_parts(thin(969_950), ProgramValue::UInt64(count(969_951)));
        for level in 0..depth {
            expression = SpecExpression::SliceFromRawParts {
                data: Box::new(SpecExpression::SliceData(Box::new(expression))),
                count: value(ProgramValue::UInt64(count(970_000 + level))),
            };
        }
        let expression = SpecExpression::SliceLength(Box::new(expression));
        let (value, work) =
            crate::instrumentation::measure_deterministic_work(|| evaluated(&expression));
        assert_eq!(value, Ok(ProgramValue::UInt64(count(970_000 + depth - 1))));
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{costs:?}");
    }
}
