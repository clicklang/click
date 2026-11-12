//! Iterative lexical binding chains with retained machine values.
use super::*;

type Values = crate::persistent::PersistentMap<String, KernelTerm>;

#[derive(Clone)]
struct Path {
    state: CState,
    values: Values,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    context: PureFactContext,
    mandatory_only: bool,
}

#[derive(Clone)]
struct ReturnBinding<'a> {
    name: &'a String,
    body: &'a SpecExpression,
    state: CState,
    values: Values,
}

impl Path {
    fn bind(&mut self, name: &String, value: SpecValue) {
        match value {
            SpecValue::Shared(value) => self.values.insert(name.clone(), value),
            SpecValue::Native(value) => {
                self.values.remove(name);
                self.state.locals.set(name.clone(), value);
            }
        }
    }
    fn append(&mut self, path: &mut SpecExpressionPath, base: &PureFactContext) -> bool {
        let next_context =
            assumptions_with_path_context(&self.context, &path.facts, &path.obligations);
        let mandatory = !path.obligations.iter().any(ProofObligation::is_assumable);
        if self.facts.is_empty() && path.facts.is_empty() && self.mandatory_only && mandatory {
            // Arithmetic debts are mandatory output, not assumptions or path
            // selection. Move each new debt once instead of cloning the whole
            // growing prefix at every binding.
            self.obligations.append(&mut path.obligations);
        } else {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &self.facts,
                &self.obligations,
                &path.facts,
                &path.obligations,
                base,
                &self.context,
            ) else {
                return false;
            };
            self.facts = facts;
            self.obligations = obligations;
        }
        self.mandatory_only &= mandatory;
        self.context = next_context;
        true
    }
}

pub(super) fn evaluate(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut pending = vec![(
        expression,
        Path {
            state: scope.state.clone(),
            values: scope.values.cloned().unwrap_or_default(),
            facts: ExecutionFacts::new(),
            obligations: Vec::new(),
            context: assumptions.clone(),
            mandatory_only: true,
        },
        false,
        Vec::<ReturnBinding<'_>>::new(),
    )];
    let mut result = Vec::new();
    while let Some((expression, path, charge, mut continuation)) = pending.pop() {
        let local_scope = SpecScope {
            state: &path.state,
            values: Some(&path.values),
            ..scope
        };
        if let SpecExpression::Let { name, value, body } = expression {
            // The outer expression dispatcher charged the first let already.
            if charge {
                budget.consume_expression_step()?;
            }
            if matches!(value.as_ref(), SpecExpression::Let { .. }) {
                continuation.push(ReturnBinding {
                    name,
                    body,
                    state: path.state.clone(),
                    values: path.values.clone(),
                });
                pending.push((value, path, true, continuation));
                continue;
            }
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                local_scope,
                value,
                &path.context,
                budget,
            )?;
            let mut paths = paths.into_iter().peekable();
            let mut prefix = Some((path, continuation));
            let start = pending.len();
            while let Some(mut value_path) = paths.next() {
                let (mut next, continuation) = if paths.peek().is_some() {
                    prefix.as_ref().unwrap().clone()
                } else {
                    prefix.take().unwrap()
                };
                if !next.append(&mut value_path, assumptions) {
                    continue;
                }
                next.bind(name, value_path.value);
                pending.push((body, next, true, continuation));
            }
            // The explicit work stack retains source path order.
            pending[start..].reverse();
        } else {
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                local_scope,
                expression,
                &path.context,
                budget,
            )?;
            let mut paths = paths.into_iter().peekable();
            let mut prefix = Some((path, continuation));
            let start = pending.len();
            while let Some(mut body) = paths.next() {
                let (mut completed, mut continuation) = if paths.peek().is_some() {
                    prefix.as_ref().unwrap().clone()
                } else {
                    prefix.take().unwrap()
                };
                if completed.append(&mut body, assumptions) {
                    if let Some(binding) = continuation.pop() {
                        completed.state = binding.state;
                        completed.values = binding.values;
                        completed.bind(binding.name, body.value);
                        pending.push((binding.body, completed, true, continuation));
                        continue;
                    }
                    result.push(SpecExpressionPath {
                        value: body.value,
                        facts: completed.facts,
                        obligations: completed.obligations,
                    });
                }
            }
            pending[start..].reverse();
        }
    }
    Ok(result)
}
