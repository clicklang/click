use super::*;

fn error_path(error: RuntimeError) -> ExpressionPath {
    ExpressionPath {
        outcome: ExpressionOutcome::RuntimeError(error),
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }
}

fn value_path() -> ExpressionPath {
    ExpressionPath {
        outcome: ExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::constant(1))),
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }
}

fn width_mismatch() -> RuntimeError {
    RuntimeError::LoadTypeMismatch {
        pointer: Pointer::null(),
        value_type: ProgramType::Int32,
        stored: Some(Box::new(ProgramValue::UInt64(
            MachineTerm::uint64_constant(6),
        ))),
    }
}

#[test]
fn an_all_error_evaluation_records_its_first_error_on_the_budget() {
    let mut execution_budget = ExecutionBudget::default();
    let mut budget = SpecEvaluation::logical(&mut execution_budget);
    let paths = spec_value_paths_in(
        vec![
            error_path(width_mismatch()),
            error_path(RuntimeError::TypeMismatch),
        ],
        &mut budget,
    );
    assert!(paths.is_empty());
    assert_eq!(budget.dropped_runtime_error(), Some(&width_mismatch()));
    // A later all-error evaluation does not displace the first record.
    spec_value_paths_in(vec![error_path(RuntimeError::TypeMismatch)], &mut budget);
    assert_eq!(budget.dropped_runtime_error(), Some(&width_mismatch()));
}

#[test]
fn a_value_path_beside_an_error_path_records_nothing() {
    let mut execution_budget = ExecutionBudget::default();
    let mut budget = SpecEvaluation::logical(&mut execution_budget);
    let paths = spec_value_paths_in(
        vec![error_path(width_mismatch()), value_path()],
        &mut budget,
    );
    assert_eq!(paths.len(), 1);
    assert_eq!(budget.dropped_runtime_error(), None);
    assert!(spec_value_paths_in(Vec::new(), &mut budget).is_empty());
    assert_eq!(budget.dropped_runtime_error(), None);
}

#[test]
fn a_load_width_mismatch_names_the_load_and_the_cell() {
    let summary = width_mismatch().kernel_summary();
    assert_eq!(
        summary,
        "a 4-byte load found a value of 8 bytes in the cell"
    );
}
