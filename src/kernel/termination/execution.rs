//! Execute generated local-descent and call-dependency obligations.

use super::obligations::{TerminationCallObligation, TerminationObligations};
use super::*;

impl TerminationObligations {
    pub(super) fn prove_local_descent(
        &self,
        name: &String,
    ) -> Result<Option<TerminationRefusal>, TerminationError> {
        match &self.function_goals[name].input {
            super::inputs::LocalTerminationInput::Completed(completed) => {
                // Ordinary completion owns descent; its loop producers own
                // ranking eligibility and concrete-exit coverage. No legacy
                // plan or source analyzer is an alternative on this route.
                let (ranked, _) = verified_loop_ranking_measures(
                    self.loop_rules.get(name).map_or(&[], Vec::as_slice),
                );
                let refusal = (0..completed.exits.count)
                    .find(|index| !completed.exits.contains(index) && !ranked.contains_key(index))
                    .map(|index| TerminationRefusal::UnrankedLoop { index });
                Ok(refusal.or_else(|| self.function_goals[name].recursion.refusal.clone()))
            }
            super::inputs::LocalTerminationInput::Independent => {
                self.prove_independent_local_descent(name)
            }
        }
    }

    fn prove_independent_local_descent(
        &self,
        name: &String,
    ) -> Result<Option<TerminationRefusal>, TerminationError> {
        let functions = &self.functions;
        let function = &functions[name];
        let plans = &self.plans;
        let verified_loop_rules = &self.loop_rules;
        let recursive_callees = &self.function_goals[name].recursive_callees;
        let mut refusal = self.function_goals[name].recursion.refusal.clone();
        let plan = plans.get(name);
        let requirements = &self.function_goals[name];
        let recursion = &requirements.recursion;
        let addressed = std::cell::OnceCell::new();
        if let Some(expression) = &recursion.expression
            && !self
                .ruled
                .get(name.as_str())
                .is_some_and(|index| self.partial_rules[*index].descent_completion.is_some())
        {
            check_expression_measure_recursion(
                name,
                &expression.source,
                &expression.declaration,
                function,
                recursive_callees,
                verified_loop_rules.get(name).map_or(&[], Vec::as_slice),
            )?;
        }

        let empty = BTreeMap::new();
        let loop_measures = plan.map_or(&empty, |plan| &plan.loop_measures);
        let (certified, uncertified_paths) = verified_loop_rules
            .get(name)
            .map(|rules| verified_loop_ranking_measures(rules))
            .unwrap_or_default();
        // A presentation clause may come from a ranked proof branch,
        // while a sibling honestly declares only partial correctness.
        // Preserve that as an unranked-loop refusal (and allow an
        // explicit `diverges` contract), not a plan for its sibling.
        let complete_path_measures;
        let loop_measures = if uncertified_paths.is_empty() {
            loop_measures
        } else {
            complete_path_measures = loop_measures
                .iter()
                .filter(|(index, _)| !uncertified_paths.contains(index))
                .map(|(index, measure)| (*index, measure.clone()))
                .collect::<BTreeMap<_, _>>();
            &complete_path_measures
        };
        let mut unranked = Vec::new();
        for &index in &requirements.loop_indices {
            prove_loop_obligation(index, loop_measures, &certified, name, &mut unranked)?;
        }
        let next_loop = requirements.loop_indices.len();
        if loop_measures.keys().any(|index| *index >= next_loop) {
            return Err(error(format!(
                "termination plan for `{name}` refers to a nonexistent loop"
            )));
        }
        // Only a function certified on its own is known to have had
        // this body executed; a linked body with no rule is not.
        if let Some(rule) = self
            .ruled
            .get(name.as_str())
            .map(|index| &self.partial_rules[*index])
            && let Some(exits) = &rule.concrete_loop_exits
        {
            unranked.retain(|index| !exits.contains(index));
        }
        if let Some(index) = unranked.first() {
            // An unranked loop is the function's own defect, so it is
            // reported ahead of anything a callee lacks.
            refusal = Some(TerminationRefusal::UnrankedLoop { index: *index });
        }

        if let Some(requirement_index) = recursion.structural_requirement {
            let measure = structural_resource_children(function, requirement_index)?;
            let mut callees = BTreeMap::new();
            for (member, index) in &recursion.structural_callees {
                charge_termination_work(1);
                callees.insert(
                    member.clone(),
                    structural_callee(&functions[member], *index)?,
                );
            }
            // An arm the function's own requirements already select is
            // active on every path; the check reads that from the arm
            // rather than seeding a synthetic path condition.
            structural_recursion_paths(
                &function.source_body,
                function,
                &measure,
                &callees,
                vec![StructuralRecursionPath {
                    aliases: BTreeMap::new(),
                    conditions: Vec::new(),
                }],
            )?;
        } else if let Some(measure) = &recursion.parameter {
            reject_address_escaped_measure(
                name,
                measure,
                addressed.get_or_init(|| address_taken_locals(&function.source_body)),
            )?;
            recursion_paths(
                &function.source_body,
                measure,
                recursive_callees,
                &recursion.parameter_indices,
                vec![i64::MIN / 2],
            )?;
        }
        Ok(refusal)
    }

    pub(super) fn prove_implicitly(self) -> Result<TerminationVerdicts, TerminationError> {
        // Local source checks are proofs of the already generated local
        // obligations. Strict and pointer-enabled dependency proofs share them.
        let mut local = BTreeMap::new();
        for level in self.levels.values() {
            for name in level {
                charge_termination_work(1);
                let result = self.prove_local_descent(name).map_err(|mut error| {
                    error.function = Some(name.clone());
                    error
                })?;
                local.insert(name.clone(), result);
            }
        }
        type Settled = (
            BTreeSet<String>,
            BTreeMap<String, TerminationRefusal>,
            Vec<String>,
        );
        let settle = |allow_pointer_calls: bool| -> Settled {
            let mut terminating = BTreeSet::<String>::new();
            let mut refusals = BTreeMap::<String, TerminationRefusal>::new();
            let mut unjustified_diverging = Vec::new();
            for level in self.levels.values() {
                let mut level_callers = BTreeMap::<&str, Vec<&String>>::new();
                let mut settled = Vec::<&String>::new();
                for name in level {
                    charge_termination_work(1);
                    let mut refusal = None;
                    for requirement in &self.function_goals[name].calls {
                        charge_termination_work(1);
                        match requirement {
                            TerminationCallObligation::Indirect {
                                object,
                                diverging_contract,
                            } => {
                                if let Some(contract) = diverging_contract {
                                    if refusal.is_none()
                                        || matches!(
                                            refusal,
                                            Some(TerminationRefusal::IndirectCall { .. })
                                        )
                                    {
                                        refusal = Some(TerminationRefusal::DivergingContract {
                                            object: object.clone(),
                                            contract: contract.clone(),
                                        });
                                    }
                                } else if !allow_pointer_calls && refusal.is_none() {
                                    refusal = Some(TerminationRefusal::IndirectCall {
                                        object: object.clone(),
                                    });
                                }
                            }
                            TerminationCallObligation::External { callee, assumed } => {
                                if !assumed && refusal.is_none() {
                                    refusal = Some(TerminationRefusal::Callee {
                                        callee: callee.clone(),
                                    });
                                }
                            }
                            TerminationCallObligation::Callee { callee, recursive } => {
                                if *recursive {
                                    level_callers.entry(callee.as_str()).or_default().push(name);
                                } else if !terminating.contains(callee) && refusal.is_none() {
                                    refusal = Some(TerminationRefusal::Callee {
                                        callee: callee.clone(),
                                    });
                                }
                            }
                        }
                    }
                    // A loop is an own-body defect; a missing recursion
                    // measure is reported only if no call already refused.
                    if matches!(local[name], Some(TerminationRefusal::UnrankedLoop { .. }))
                        || refusal.is_none()
                    {
                        refusal = local[name].clone();
                    }
                    match refusal {
                        Some(refusal) => {
                            refusals.insert(name.clone(), refusal);
                            settled.push(name);
                        }
                        None => {
                            terminating.insert(name.clone());
                        }
                    }
                }
                while let Some(refused) = settled.pop() {
                    charge_termination_work(1);
                    for caller in level_callers.remove(refused.as_str()).unwrap_or_default() {
                        charge_termination_work(1);
                        if terminating.remove(caller) {
                            refusals.insert(
                                caller.clone(),
                                TerminationRefusal::Callee {
                                    callee: refused.clone(),
                                },
                            );
                            settled.push(caller);
                        }
                    }
                }
                for name in level {
                    charge_termination_work(1);
                    if self.declared_diverging.contains(name) && terminating.remove(name) {
                        refusals.insert(name.clone(), TerminationRefusal::DeclaredDiverging);
                        unjustified_diverging.push(name.clone());
                    }
                }
            }
            (terminating, refusals, unjustified_diverging)
        };
        let strict = settle(false);
        let mut unsuitable_callbacks = Vec::new();
        for callback in &self.callbacks {
            charge_termination_work(1);
            if !strict.0.contains(&callback.callback)
                && !self.assumed_terminating.contains(&callback.callback)
            {
                unsuitable_callbacks.push(UnsuitableCallback {
                    taker: callback.taker.clone(),
                    callback: callback.callback.clone(),
                });
            }
        }
        let (terminating, refusals, unjustified_diverging) =
            if self.makes_pointer_calls && unsuitable_callbacks.is_empty() {
                settle(true)
            } else {
                strict
            };
        Ok(TerminationVerdicts {
            rules: self
                .partial_rules
                .into_iter()
                .inspect(|_| charge_termination_work(1))
                .filter(|rule| terminating.contains(rule.function.name()))
                .map(|rule| VerifiedFunctionTerminationRule {
                    function: rule.function,
                })
                .collect(),
            refusals,
            unjustified_diverging,
            unsuitable_callbacks,
        })
    }
}
