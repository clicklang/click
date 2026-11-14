//! Scalar-array initialization and region writes. Storage and retained derivations
//! are compact; authority, source initialization, and coercion remain checked.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn execute(
    state: &ExecutionState,
    target: &ProgramExpression,
    source: &ProgramExpression,
    element_type: ProgramType,
    count: u32,
    copy: bool,
    fresh: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    if !matches!(
        element_type,
        ProgramType::Int32 | ProgramType::UInt8 | ProgramType::UInt32
    ) {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    }
    let Some(bytes) = count
        .checked_mul(element_type.byte_width())
        .filter(|n| *n <= i32::MAX as u32)
    else {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    };
    for target in evaluate_c_expression_paths(state, target, assumptions, budget)? {
        let target_pointer = match target.outcome {
            ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => pointer,
            outcome => {
                paths.push(path(
                    expression_error(outcome),
                    target.facts,
                    target.obligations,
                ));
                continue;
            }
        };
        let selected =
            assumptions_with_path_context(assumptions, &target.facts, &target.obligations);
        for source in evaluate_c_expression_paths(state, source, &selected, budget)? {
            let Some((facts, mut obligations)) = merge_execution_pure_facts_and_obligations(
                &target.facts,
                &target.obligations,
                &source.facts,
                &source.obligations,
                assumptions,
            ) else {
                continue;
            };
            let value = match source.outcome {
                ExpressionOutcome::Value(value) => value,
                outcome => {
                    paths.push(path(expression_error(outcome), facts, obligations));
                    continue;
                }
            };
            let selected = assumptions_with_path_context(assumptions, &facts, &obligations);
            let value = if copy {
                Some(value)
            } else {
                crate::kernel::functions::coerce_c_value_with_pointee_constant(
                    value,
                    element_type,
                    false,
                    &mut obligations,
                    &selected,
                )
            };
            let Some(value) = value else {
                paths.push(path(
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    facts,
                    obligations,
                ));
                continue;
            };
            let target = target_pointer.pointer();
            if bytes != 0
                && let Some(refusal) = subobject_access_refusal(
                    target,
                    target_pointer.extent(),
                    bytes,
                    &facts,
                    &obligations,
                    assumptions,
                )
            {
                paths.push(path(
                    StatementOutcome::UndefinedBehavior(refusal),
                    facts,
                    obligations,
                ));
                continue;
            }
            if bytes != 0
                && (target_pointer.pointee_constant()
                    || state.memory.is_read_only_block(&target.block))
            {
                paths.push(path(
                    StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                ));
                continue;
            }
            let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                target.clone(),
                0u32.into(),
                count.into(),
                element_type.byte_width(),
            ));
            if bytes != 0
                && !state.resources().owns_designated_storage_access(
                    target,
                    target_pointer.access_designation(),
                    bytes,
                    &selected,
                )
            {
                paths.push(path(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(required),
                    }),
                    facts,
                    obligations,
                ));
                continue;
            }
            if bytes != 0
                && let Some(outcome) =
                    memory_write_permission_outcome(state, target, bytes, &selected)
            {
                paths.push(path(outcome, facts, obligations));
                continue;
            }
            if copy && bytes != 0 {
                let ProgramValue::Pointer(source) = &value else {
                    paths.push(path(
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts,
                        obligations,
                    ));
                    continue;
                };
                if let Some(refusal) = subobject_access_refusal(
                    source.pointer(),
                    source.extent(),
                    bytes,
                    &facts,
                    &obligations,
                    assumptions,
                ) {
                    paths.push(path(
                        StatementOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    ));
                    continue;
                }
                if !crate::kernel::api::with_extended_dag_bridging(|| {
                    state.resources().permits_designated_storage_read(
                        source.pointer(),
                        Some(source.access_designation()),
                        bytes,
                        &selected,
                    )
                }) {
                    let resource = ResourceFact::view_memory(MemoryRange::new_with_element_width(
                        source.pointer().clone(),
                        0u32.into(),
                        count.into(),
                        element_type.byte_width(),
                    ));
                    paths.push(path(
                        StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                            resource: Box::new(resource),
                        }),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
            let memory = if fresh {
                state.memory.clone().initialize_scalar_array(
                    target,
                    element_type,
                    count,
                    value,
                    copy,
                )
            } else {
                state.memory.clone().write_scalar_array_region(
                    target,
                    element_type,
                    count,
                    value,
                    copy,
                    false,
                    &selected,
                )
            };
            let outcome = match memory {
                Ok(memory) => {
                    let mut next = state.clone();
                    next.set_memory(memory);
                    if bytes != 0
                        && let ExpressionOutcome::Value(value) = next.memory.load(target)
                    {
                        refresh_scalar_local_after_memory_store(
                            &mut next, target, &value, &selected,
                        );
                    }
                    StatementOutcome::Normal(Box::new(next))
                }
                Err(error) => StatementOutcome::RuntimeError(error),
            };
            paths.push(path(outcome, facts, obligations));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn path(
    outcome: StatementOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> StatementExecutionPath {
    StatementExecutionPath::new(outcome, facts, obligations)
}
fn expression_error(outcome: ExpressionOutcome) -> StatementOutcome {
    match outcome {
        ExpressionOutcome::UndefinedBehavior(error) => StatementOutcome::UndefinedBehavior(error),
        ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
        ExpressionOutcome::Value(_) => StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
    }
}
