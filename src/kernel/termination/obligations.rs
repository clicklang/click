//! Generate immutable termination requirements without executing their proofs.

use super::*;

#[derive(Clone, Debug)]
pub(super) enum TerminationCallObligation {
    Indirect {
        object: String,
        diverging_contract: Option<String>,
    },
    External {
        callee: String,
        assumed: bool,
    },
    Callee {
        callee: String,
        recursive: bool,
    },
}

#[derive(Debug)]
pub(super) struct FunctionTerminationObligations {
    pub recursive_callees: BTreeSet<String>,
    pub recursive_measure: Option<FunctionTerminationMeasure>,
    pub loop_indices: Vec<usize>,
    pub calls: Vec<TerminationCallObligation>,
}

pub(super) struct CallbackTerminationObligation {
    pub taker: String,
    pub callback: String,
}

/// Every function has a local loop/recursion-descent obligation and the
/// enumerated call dependencies. Construction classifies the graph; it does
/// not run a loop, recursion, or callback proof and cannot issue a rule.
pub(super) struct TerminationObligations {
    pub functions: BTreeMap<String, ProgramFunction>,
    pub partial_rules: Vec<VerifiedFunctionRule>,
    pub ruled: BTreeMap<String, usize>,
    pub plans: BTreeMap<String, FunctionTerminationPlan>,
    pub loop_rules: BTreeMap<String, Vec<VerifiedLoopRule>>,
    pub levels: BTreeMap<usize, Vec<String>>,
    pub function_goals: BTreeMap<String, FunctionTerminationObligations>,
    pub callbacks: Vec<CallbackTerminationObligation>,
    pub makes_pointer_calls: bool,
    pub assumed_terminating: BTreeSet<String>,
    pub declared_diverging: BTreeSet<String>,
}

impl TerminationObligations {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn generate(
        partial_rules: &[VerifiedFunctionRule],
        plan_entries: &[FunctionTerminationPlan],
        loop_rules: &BTreeMap<String, Vec<VerifiedLoopRule>>,
        inline_bodies: &[&ProgramFunction],
        heights: &BTreeMap<String, usize>,
        assumed_terminating: &BTreeSet<String>,
        declared_diverging: &BTreeSet<String>,
        diverging_contracts: &BTreeSet<String>,
        allow_unused_recursive_measure: bool,
    ) -> Result<Self, TerminationError> {
        let (functions, calls) = termination_call_graph(partial_rules, inline_bodies);
        charge_termination_work(plan_entries.len());
        let mut plans = plan_entries
            .iter()
            .map(|plan| (plan.function_name.clone(), plan.clone()))
            .collect::<BTreeMap<_, _>>();
        if plans.len() != plan_entries.len() {
            return Err(error("termination plans contain a duplicate function"));
        }
        let height_of = |name: &str| {
            heights.get(name).copied().ok_or_else(|| {
                error(format!(
                    "the termination height plan assigns no height to `{name}`"
                ))
            })
        };
        let mut levels = BTreeMap::<usize, Vec<String>>::new();
        let retained_exits = partial_rules
            .iter()
            .filter_map(|rule| {
                charge_termination_work(1);
                rule.concrete_loop_exits
                    .as_ref()
                    .map(|exits| (rule.function.name(), exits))
            })
            .collect::<BTreeMap<_, _>>();
        let mut function_goals = BTreeMap::new();
        let mut callbacks = Vec::new();
        let mut makes_pointer_calls = false;
        for (name, function) in &functions {
            charge_termination_work(1);
            let height = height_of(name)?;
            levels.entry(height).or_default().push(name.clone());
            let diverging_objects = diverging_contract_objects(function, diverging_contracts);
            let mut requirements = Vec::new();
            let mut recursive_callees = BTreeSet::new();
            for callee in &calls[name] {
                charge_termination_work(1);
                if callee == MODELED_REALLOC {
                    continue;
                }
                if let Some(object) = callee.strip_suffix("#indirect") {
                    makes_pointer_calls = true;
                    requirements.push(TerminationCallObligation::Indirect {
                        object: object.to_string(),
                        diverging_contract: diverging_objects
                            .get(object)
                            .or_else(|| diverging_objects.values().next())
                            .cloned(),
                    });
                } else if functions.contains_key(callee) {
                    let callee_height = height_of(callee)?;
                    if callee_height > height {
                        let mut failure = error(format!(
                            "the termination height plan places callee `{callee}` at height {callee_height}, above its caller `{name}` at height {height}"
                        ));
                        failure.function = Some(name.clone());
                        return Err(failure);
                    }
                    let recursive = callee_height == height;
                    if recursive {
                        recursive_callees.insert(callee.clone());
                    }
                    requirements.push(TerminationCallObligation::Callee {
                        callee: callee.clone(),
                        recursive,
                    });
                } else {
                    requirements.push(TerminationCallObligation::External {
                        callee: callee.clone(),
                        assumed: assumed_terminating.contains(callee),
                    });
                }
            }
            // Selection can break a recursive component. Whether a declaration
            // has an edge to rank is known now, before any proof executes.
            if allow_unused_recursive_measure
                && recursive_callees.is_empty()
                && let Some(plan) = plans.get_mut(name)
            {
                plan.clear_recursive_measure();
            }
            let lowered_loop_body = contains_natural_control_loop(function.body());
            let loop_body = if lowered_loop_body {
                function.body()
            } else {
                &function.source_body
            };
            let mut loop_indices = Vec::new();
            if let Some(exits) = retained_exits.get(name.as_str()) {
                loop_indices.extend(0..exits.count);
            } else {
                visit_loop_obligations(loop_body, &mut 0, &mut |index| {
                    loop_indices.push(index);
                    Ok(())
                })?;
            }
            if let Some(plan) = plans.get(name) {
                let addressed = std::cell::OnceCell::new();
                let owned = loop_rules
                    .get(name)
                    .into_iter()
                    .flatten()
                    .filter_map(|rule| {
                        charge_termination_work(1);
                        rule.loop_evidence.as_ref().map(|evidence| evidence.index)
                    })
                    .collect::<BTreeSet<_>>();
                for (&index, measure) in &plan.loop_measures {
                    if owned.contains(&index) {
                        continue;
                    }
                    if let LoopTerminationMeasure::Ranking(components) = measure {
                        for component in components {
                            if let RankingMeasureKey::ProgramExpression(expression) = component {
                                reject_address_escaped_expression_measure(
                                    name,
                                    expression,
                                    addressed.get_or_init(|| address_taken_locals(loop_body)),
                                )?;
                            }
                        }
                    }
                }
            }
            let recursive_measure = plans
                .get(name)
                .and_then(|plan| plan.recursive_measure.clone());
            function_goals.insert(
                name.clone(),
                FunctionTerminationObligations {
                    recursive_callees,
                    recursive_measure,
                    loop_indices,
                    calls: requirements,
                },
            );
            let mut taken = BTreeSet::new();
            function_address_taken(function, &mut taken);
            for callback in taken {
                charge_termination_work(1);
                callbacks.push(CallbackTerminationObligation {
                    taker: name.clone(),
                    callback,
                });
            }
        }
        Ok(Self {
            functions: functions
                .into_iter()
                .map(|(name, function)| (name, function.clone()))
                .collect(),
            partial_rules: partial_rules.to_vec(),
            ruled: partial_rules
                .iter()
                .enumerate()
                .map(|(index, rule)| (rule.function.name().to_string(), index))
                .collect(),
            plans,
            loop_rules: loop_rules.clone(),
            levels,
            function_goals,
            callbacks,
            makes_pointer_calls,
            assumed_terminating: assumed_terminating.clone(),
            declared_diverging: declared_diverging.clone(),
        })
    }
}
