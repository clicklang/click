//! Execute generated local-descent and call-dependency obligations.

use super::obligations::{TerminationCallObligation, TerminationObligations};
use super::*;

impl TerminationObligations {
    pub(super) fn prove_local_descent(
        &self,
        name: &String,
    ) -> Result<Option<TerminationRefusal>, TerminationError> {
        let functions = &self.functions;
        let function = &functions[name];
        let plans = &self.plans;
        let verified_loop_rules = &self.loop_rules;
        let recursive_callees = &self.function_goals[name].recursive_callees;
        let mut refusal = None;
        let plan = plans.get(name);
        let requirements = &self.function_goals[name];
        let recursive_measure = requirements.recursive_measure.clone();
        // A recursion carried by a tactic application has no C call
        // for a structural or parameter measure to read: the
        // recursive edge lives in the certified proof, not the body.
        // Only an expression measure answers for it, because its
        // descent was owed, under the recursion anchor, at the very
        // application that recursed.
        if let Some(rule) = self
            .ruled
            .get(name.as_str())
            .map(|index| &self.partial_rules[*index])
            && rule
                .applied_tactics
                .iter()
                .any(|tactic| recursive_callees.contains(tactic))
            && !matches!(
                recursive_measure,
                None | Some(FunctionTerminationMeasure::Expression(_))
            )
        {
            return Err(error(format!(
                "`{name}` recurses through a tactic application, which only an expression \
             `decreases` measure can rank: its descent is owed at each application. \
             Rank `{name}` by an expression over its parameters or its binders' models"
            )));
        }
        let mut parameter_indices = BTreeMap::new();
        let mut structural_requirement = None;
        // The function's address-taken locals, walked once for every
        // measure checked below.
        let addressed = std::cell::OnceCell::new();
        if recursive_callees.is_empty() {
            if recursive_measure.is_some() {
                let mut refused = error(format!(
                    "function-level `decreases` on nonrecursive function `{name}` has no recursive edge to rank"
                ));
                refused.superfluous_recursive_measure = true;
                return Err(refused);
            }
        } else if let Some(unmeasured) = std::iter::once(name)
            .chain(recursive_callees.iter())
            .inspect(|_| charge_termination_work(1))
            .find(|member| {
                plans
                    .get(*member)
                    .and_then(|plan| plan.recursive_measure.as_ref())
                    .is_none()
            })
        {
            if refusal.is_none() {
                refusal = Some(TerminationRefusal::UnmeasuredRecursion {
                    callee: if unmeasured == name {
                        recursive_callees
                            .first()
                            .expect("a recursive function has a recursive callee")
                            .clone()
                    } else {
                        unmeasured.clone()
                    },
                });
            }
        } else if let Some(FunctionTerminationMeasure::ResourceRequirement(index)) =
            recursive_measure
        {
            // Every member of the component is ranked structurally,
            // so each one's walk checks its own edges.
            for member in recursive_callees {
                charge_termination_work(1);
                if !matches!(
                    plans[member].recursive_measure,
                    Some(FunctionTerminationMeasure::ResourceRequirement(_))
                ) {
                    return Err(error(
                        "a recursive component cannot mix structural and other measures",
                    ));
                }
            }
            structural_requirement = Some(index);
        } else if let Some(FunctionTerminationMeasure::Expression(source)) = &recursive_measure {
            check_expression_measure_recursion(
                name,
                source,
                function,
                recursive_callees,
                plans,
                verified_loop_rules.get(name).map_or(&[], Vec::as_slice),
            )?;
        } else {
            for member in std::iter::once(name).chain(recursive_callees.iter()) {
                charge_termination_work(1);
                let Some(FunctionTerminationMeasure::NumericParameter(index)) =
                    plans[member].recursive_measure
                else {
                    return Err(error(
                        "a recursive component cannot mix numeric and structural measures",
                    ));
                };
                let parameter = functions[member].parameters().get(index).ok_or_else(|| {
                    error(format!(
                        "termination parameter index is invalid for `{member}`"
                    ))
                })?;
                if parameter.program_type != ProgramType::Int32 {
                    return Err(error(format!(
                        "termination parameter `{}` in `{member}` must have type int32",
                        parameter.name
                    )));
                }
                parameter_indices.insert(member.clone(), index);
            }
        }

        let empty = BTreeMap::new();
        let loop_measures = plan.map_or(&empty, |plan| &plan.loop_measures);
        for measures in loop_measures.values() {
            let LoopTerminationMeasure::Ranking(measures) = measures else {
                continue;
            };
            for measure in measures {
                // A pure component reaches this pass only as the
                // spelling the plan names it by; the lowered
                // expression, and so its escape check, lives on the
                // certified loop head that
                // `verified_loop_ranking_measures` reads below.
                let RankingMeasureKey::ProgramExpression(measure) = measure else {
                    continue;
                };
                reject_address_escaped_expression_measure(
                    name,
                    measure,
                    addressed.get_or_init(|| address_taken_locals(&function.source_body)),
                )?;
            }
        }
        let loop_source_body = if requirements.lowered_loop_body {
            function.body()
        } else {
            &function.source_body
        };
        let (certified, uncertified_paths) = match verified_loop_rules.get(name) {
            Some(rules) => verified_loop_ranking_measures(name, loop_source_body, rules)?,
            None => (BTreeMap::new(), BTreeSet::new()),
        };
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
        {
            let ruled_loops = verified_loop_rules
                .get(name)
                .map(|rules| {
                    rules
                        .iter()
                        .filter_map(|rule| rule.loop_index)
                        .collect::<BTreeSet<_>>()
                })
                .unwrap_or_default();
            let executed = loops_executed_to_exit(function, rule.loop_semantics(), &ruled_loops);
            unranked.retain(|index| !executed.contains(index));
        }
        if let Some(index) = unranked.first() {
            // An unranked loop is the function's own defect, so it is
            // reported ahead of anything a callee lacks.
            refusal = Some(TerminationRefusal::UnrankedLoop { index: *index });
        }

        if let Some(requirement_index) = structural_requirement {
            let measure = structural_resource_children(function, requirement_index)?;
            let mut callees = BTreeMap::new();
            for member in recursive_callees {
                charge_termination_work(1);
                let Some(FunctionTerminationMeasure::ResourceRequirement(index)) =
                    plans[member].recursive_measure
                else {
                    continue;
                };
                callees.insert(
                    member.clone(),
                    structural_callee(&functions[member], index)?,
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
        } else if let Some(index) = parameter_indices.get(name) {
            let measure = &function.parameters()[*index].name;
            reject_address_escaped_measure(
                name,
                measure,
                addressed.get_or_init(|| address_taken_locals(&function.source_body)),
            )?;
            recursion_paths(
                &function.source_body,
                measure,
                recursive_callees,
                &parameter_indices,
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
