// Scaling tests of `src/kernel/tests/program_slice_operation_tests.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// The work of reading `s.len()` and `s.as_ptr()` of a slice local beside
/// `size` unrelated slice locals and `size` facts about their counts.
fn component_reads_beside_unrelated_slices(size: u64) -> usize {
    let mut state = ExecutionState::new();
    let mut assumptions = PureFactContext::new();
    for index in 0..size {
        let unrelated = named_slice(976_000 + index);
        let ProgramValue::Pointer(slice) = &unrelated else {
            panic!("a slice is a pointer value");
        };
        assumptions = assumptions.assume_condition(
            OldConditionTerm::uint64_equal(
                slice.len().expect("a wide pointer").clone(),
                OldMachineTerm::uint64_constant(index),
            ),
            true,
        );
        state = state.with_local(format!("unrelated_{index}"), unrelated);
    }
    let target = named_slice(976_900);
    let ProgramValue::Pointer(slice) = &target else {
        panic!("a slice is a pointer value");
    };
    let expected_length = ProgramValue::UInt64(slice.len().expect("a wide pointer").clone());
    let expected_data = ProgramValue::Pointer(slice.as_ptr());
    let state = state.with_local("target", target);
    let target = || Box::new(ProgramExpression::Variable(BindingName::from("target")));
    let reads = [
        (ProgramExpression::SliceLength(target()), expected_length),
        (ProgramExpression::SliceData(target()), expected_data),
    ];
    let mut total = 0;
    for (read, expected) in reads {
        let mut budget = ExecutionBudget::for_program_expression(&read);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_program_expression_paths(&state, &read, &assumptions, &mut budget).unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].outcome, ExpressionOutcome::Value(expected));
        total += work;
    }
    total
}

/// A component read takes the value from its operand: its work does not
/// grow with unrelated slice locals and facts about their counts
/// (`design/rust-slice-values.md`, step 3a).
#[test]
fn program_slice_component_reads_ignore_unrelated_slices_and_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(component_reads_beside_unrelated_slices);
    assert!(costs[0] > 0, "{costs:?}");
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] + 8, "{costs:?}");
    }
}

/// `depth` nested rebuilds, `from_raw_parts(from_raw_parts(...).as_ptr(),
/// n_k)`, each with its own count, cost a constant amount each: the work
/// grows linearly with the expression, never with what was built before.
#[test]
fn nested_program_slice_constructions_grow_linearly() {
    let _session = crate::kernel::VerificationSession::enter();
    let sizes = [8u64, 16, 32];
    let costs = sizes.map(|depth| {
        let mut expression = from_raw_parts(
            pointer(&thin(976_950)),
            value(ProgramValue::UInt64(count(976_951))),
        );
        for level in 0..depth {
            expression = from_raw_parts(
                Box::new(ProgramExpression::SliceData(Box::new(expression))),
                value(ProgramValue::UInt64(count(977_000 + level))),
            );
        }
        let expression = ProgramExpression::SliceLength(Box::new(expression));
        let (outcome, work) =
            crate::instrumentation::measure_deterministic_work(|| evaluated(&expression));
        assert_eq!(
            outcome,
            ExpressionOutcome::Value(ProgramValue::UInt64(count(977_000 + depth - 1)))
        );
        work
    });
    // Doubling the depth at most doubles the work, beside a constant.
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 2 + 64, "{costs:?}");
    }
}
