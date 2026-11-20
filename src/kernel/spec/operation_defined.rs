//! The `defined(...)` special form: the domain of an expression's root
//! operation, with its operands taken as values.
//!
//! Each operand is evaluated once, as an ordinary term. Its obligations stay
//! obligations of the lowered proposition, exactly as `ensures r == a + b`
//! owes `a + b`'s domain without claiming it. Its value is bound to a fresh
//! generated name, and the root is evaluated over those names, from no facts
//! and with C's evaluation rules. What that evaluation owes or selects is the
//! claim. A bound name reads its value and owes nothing, so the claim is the
//! root operation's own domain, the same kernel conditions the whole
//! expression's evaluation owes for that operation.
//!
//! `let` and loop entry are transparent. A conversion to its operand's own
//! type is transparent; any other conversion is the operation. `if` claims
//! its selected branch's domain under its condition, as `and`, `or` and
//! `implies` read their right sides. A form with no operand expressions is
//! evaluated whole.

use super::*;

struct DefinedPath {
    claim: Proposition,
    /// The value the root evaluation produced, when it produced one value.
    value: Option<SpecValue>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

pub(super) fn lower(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    Ok(paths(scope, expression, assumptions, budget)?
        .into_iter()
        .map(|path| SpecPropositionPath {
            introductions: Vec::new(),
            proposition: path.claim,
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect())
}

fn paths(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        SpecExpression::Cast(operand, target)
        | SpecExpression::PointerCoercion(operand, target) => {
            conversion(scope, expression, operand, *target, assumptions, budget)
        }
        SpecExpression::LoopEntryState(inner) => {
            let Some(entry) = scope.loop_entry_state else {
                return Ok(Vec::new());
            };
            paths(
                SpecScope {
                    state: entry,
                    loop_entry_state: Some(entry),
                    values: None,
                    ..scope
                },
                inner,
                assumptions,
                budget,
            )
        }
        SpecExpression::Let { name, value, body } => {
            let mut result = Vec::new();
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                value,
                assumptions,
                budget,
            )? {
                let mut state = scope.state.clone();
                let mut values = scope.values.cloned().unwrap_or_default();
                bindings::bind_value(name, value_path.value, &mut state, &mut values);
                let context = assumptions_with_path_context(
                    assumptions,
                    &value_path.facts,
                    &value_path.obligations,
                );
                let body_scope = SpecScope {
                    state: &state,
                    values: Some(&values),
                    ..scope
                };
                for body_path in paths(body_scope, body, &context, budget)? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &value_path.facts,
                            &value_path.obligations,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            &context,
                        )
                    else {
                        continue;
                    };
                    result.push(DefinedPath {
                        facts,
                        obligations,
                        ..body_path
                    });
                }
            }
            Ok(result)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => conditional(
            scope,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        ),
        _ => operation(scope, expression, assumptions, budget),
    }
}

/// The operand expressions of a root operation, in evaluation order. A form
/// without operand expressions has none and is evaluated whole.
fn operands(expression: &SpecExpression) -> Vec<&SpecExpression> {
    use SpecExpression as E;
    match expression {
        E::Add(left, right)
        | E::Subtract(left, right)
        | E::Multiply(left, right)
        | E::Divide(left, right)
        | E::Remainder(left, right)
        | E::ShiftLeft(left, right)
        | E::RustShiftLeft(left, right)
        | E::RustShiftRight(left, right)
        | E::ShiftRight(left, right)
        | E::BitwiseAnd(left, right)
        | E::BitwiseOr(left, right)
        | E::BitwiseXor(left, right) => vec![left, right],
        E::Negate(operand) | E::BitwiseNot(operand) => vec![operand],
        // The format annotates the root operator itself.
        E::NarrowArithmetic(operator, _) => operands(operator),
        E::MemoryLoad { pointer, .. } | E::Subobject { pointer, .. } => vec![pointer],
        E::PointerOffset {
            pointer, elements, ..
        } => vec![pointer, elements],
        E::Requires { value, .. } => vec![value],
        E::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .filter_map(|argument| match argument {
                SpecPureFunctionArgument::Value(value) => Some(value),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// `expression` with each operand, in [`operands`] order, replaced by the
/// next of `replacements`.
fn replace_operands(
    expression: &SpecExpression,
    replacements: &mut impl Iterator<Item = SpecExpression>,
) -> SpecExpression {
    use SpecExpression as E;
    let mut next = || Box::new(replacements.next().expect("one replacement per operand"));
    match expression {
        E::Add(..) => E::Add(next(), next()),
        E::Subtract(..) => E::Subtract(next(), next()),
        E::Multiply(..) => E::Multiply(next(), next()),
        E::Divide(..) => E::Divide(next(), next()),
        E::Remainder(..) => E::Remainder(next(), next()),
        E::ShiftLeft(..) => E::ShiftLeft(next(), next()),
        E::RustShiftLeft(..) => E::RustShiftLeft(next(), next()),
        E::RustShiftRight(..) => E::RustShiftRight(next(), next()),
        E::ShiftRight(..) => E::ShiftRight(next(), next()),
        E::BitwiseAnd(..) => E::BitwiseAnd(next(), next()),
        E::BitwiseOr(..) => E::BitwiseOr(next(), next()),
        E::BitwiseXor(..) => E::BitwiseXor(next(), next()),
        E::Negate(_) => E::Negate(next()),
        E::BitwiseNot(_) => E::BitwiseNot(next()),
        E::NarrowArithmetic(operator, format) => {
            E::NarrowArithmetic(Box::new(replace_operands(operator, replacements)), *format)
        }
        E::MemoryLoad {
            point,
            value_type,
            exact,
            ..
        } => E::MemoryLoad {
            point: point.clone(),
            pointer: next(),
            value_type: *value_type,
            exact: *exact,
        },
        E::Subobject { width, .. } => E::Subobject {
            pointer: next(),
            width: *width,
        },
        E::PointerOffset { byte_width, .. } => {
            let pointer = next();
            E::PointerOffset {
                pointer,
                elements: next(),
                byte_width: *byte_width,
            }
        }
        E::Requires { requirement, .. } => E::Requires {
            requirement: requirement.clone(),
            value: next(),
        },
        E::PureFunctionApplication {
            name,
            arguments,
            result_type,
            pointer_result,
            result_object_class,
        } => E::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    SpecPureFunctionArgument::Value(_) => SpecPureFunctionArgument::Value(*next()),
                    argument => argument.clone(),
                })
                .collect(),
            result_type: *result_type,
            pointer_result: pointer_result.clone(),
            result_object_class: result_object_class.clone(),
        },
        expression => expression.clone(),
    }
}

/// A prefix of evaluated operands: their values bound to fresh names, and
/// the facts and obligations their evaluation produced.
#[derive(Clone)]
struct Operands {
    state: ExecutionState,
    values: crate::persistent::PersistentMap<BindingName, KernelTerm>,
    references: Vec<SpecExpression>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    context: PureFactContext,
}

fn operation(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let operand_expressions = operands(expression);
    let mut prefixes = vec![Operands {
        state: scope.state.clone(),
        values: scope.values.cloned().unwrap_or_default(),
        references: Vec::new(),
        facts: ExecutionFacts::new(),
        obligations: Vec::new(),
        context: assumptions.clone(),
    }];
    for operand in operand_expressions {
        let mut extended = Vec::new();
        for prefix in prefixes {
            let operand_paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                operand,
                &prefix.context,
                budget,
            )?;
            for operand_path in operand_paths {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &prefix.facts,
                    &prefix.obligations,
                    &operand_path.facts,
                    &operand_path.obligations,
                    assumptions,
                    &prefix.context,
                ) else {
                    continue;
                };
                let mut next = prefix.clone();
                let reference =
                    operand_reference(operand_path.value, &mut next.state, &mut next.values);
                next.context = assumptions_with_path_context(assumptions, &facts, &obligations);
                next.facts = facts;
                next.obligations = obligations;
                next.references.push(reference);
                extended.push(next);
            }
        }
        prefixes = extended;
    }
    let mut result = Vec::new();
    for prefix in prefixes {
        let root_expression = replace_operands(expression, &mut prefix.references.into_iter());
        let root_scope = SpecScope {
            state: &prefix.state,
            values: Some(&prefix.values),
            ..scope
        };
        result.push(root(
            root_scope,
            &root_expression,
            prefix.facts,
            prefix.obligations,
            assumptions,
            budget,
        )?);
    }
    Ok(result)
}

/// An expression that reads an evaluated operand's value and owes nothing. A
/// native value, and a shared pointer through its retained native pointer, is
/// that value itself, which keeps its C type, including a pointer's provenance
/// and element width. Any other shared root is bound to a fresh generated
/// name, which reads that same root.
fn operand_reference(
    value: SpecValue,
    state: &mut ExecutionState,
    values: &mut crate::persistent::PersistentMap<BindingName, KernelTerm>,
) -> SpecExpression {
    match value {
        SpecValue::Native(value) => SpecExpression::Value(value),
        // A pointer's arithmetic reads its element width from its type, which
        // its retained native pointer keeps and a generated name does not.
        SpecValue::Shared(root) if root.pointer_native().is_some() => {
            SpecExpression::Value(SpecValue::Shared(root).into_native())
        }
        value => {
            let name = crate::kernel::GeneratedBinderId::fresh().binding_name();
            bindings::bind_value(&name, value, state, values);
            SpecExpression::ProgramExpression(ProgramExpression::Variable(name))
        }
    }
}

/// Evaluate a root over already-evaluated operands, from no facts and with
/// C's evaluation rules. Its conditions are the claim; the operands' facts
/// and obligations are carried unchanged.
fn root(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<DefinedPath> {
    let mut checked = SpecEvaluation::checked(budget);
    checked.program_definedness = true;
    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        expression,
        &definedness_context(assumptions),
        &mut checked,
    )?;
    let value = match paths.as_slice() {
        [path] => Some(path.value.clone()),
        _ => None,
    };
    Ok(DefinedPath {
        claim: definedness_claim(paths),
        value,
        facts,
        obligations,
    })
}

/// A conversion to its operand's own type is no operation: the claim is the
/// operand's. Any other conversion is the root operation, and the operand's
/// claim is owed like any operand's domain.
fn conversion(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    operand: &SpecExpression,
    target: ProgramType,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let mut result = Vec::new();
    for inner in paths(scope, operand, assumptions, budget)? {
        let Some(value) = inner.value.clone() else {
            // Several root values: evaluate the conversion as an operation.
            result.extend(operation(scope, expression, assumptions, budget)?);
            continue;
        };
        if value.program_type() == target {
            result.push(inner);
            continue;
        }
        let mut obligations = inner.obligations;
        if !is_true(&inner.claim) {
            obligations.push(ProofObligation::evaluation_domain(inner.claim));
        }
        let mut state = scope.state.clone();
        let mut values = scope.values.cloned().unwrap_or_default();
        let reference = operand_reference(value, &mut state, &mut values);
        let root_expression = replace_conversion_operand(expression, reference);
        result.push(root(
            SpecScope {
                state: &state,
                values: Some(&values),
                ..scope
            },
            &root_expression,
            inner.facts,
            obligations,
            assumptions,
            budget,
        )?);
    }
    Ok(result)
}

fn replace_conversion_operand(
    expression: &SpecExpression,
    operand: SpecExpression,
) -> SpecExpression {
    match expression {
        SpecExpression::Cast(_, target) => SpecExpression::Cast(Box::new(operand), *target),
        SpecExpression::PointerCoercion(_, target) => {
            SpecExpression::PointerCoercion(Box::new(operand), *target)
        }
        _ => unreachable!("a conversion"),
    }
}

fn is_true(proposition: &Proposition) -> bool {
    matches!(
        proposition.condition_native(),
        Some((ConditionTerm::Constant(true), true))
    )
}

fn negation(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// `if c { x } else { y }` reads only its selected branch: the claim is
/// `(c implies defined(x)) and (not c implies defined(y))`, and each branch's
/// obligations are owed only under its own side of the condition.
fn conditional(
    scope: SpecScope<'_>,
    condition: &SpecProposition,
    then_branch: &SpecExpression,
    else_branch: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let mut result = Vec::new();
    for condition_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        condition,
        assumptions,
        budget,
    )? {
        let context = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        let holds = condition_path.proposition.clone();
        let fails = negation(&holds);
        let then_paths = paths(
            scope,
            then_branch,
            &context.clone().assume_proposition(holds.clone()),
            budget,
        )?;
        let else_paths = paths(
            scope,
            else_branch,
            &context.clone().assume_proposition(fails.clone()),
            budget,
        )?;
        for then_path in &then_paths {
            for else_path in &else_paths {
                let guarded = guard_right_obligations(&holds, then_path.obligations.clone())
                    .into_iter()
                    .chain(guard_right_obligations(
                        &fails,
                        else_path.obligations.clone(),
                    ))
                    .collect::<Vec<_>>();
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &condition_path.facts,
                    &condition_path.obligations,
                    &ExecutionFacts::new(),
                    &guarded,
                    assumptions,
                    &context,
                ) else {
                    continue;
                };
                result.push(DefinedPath {
                    claim: Proposition::And(
                        Box::new(Proposition::Implies(
                            Box::new(holds.clone()),
                            Box::new(then_path.claim.clone()),
                        )),
                        Box::new(Proposition::Implies(
                            Box::new(fails.clone()),
                            Box::new(else_path.claim.clone()),
                        )),
                    ),
                    value: None,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(result)
}
