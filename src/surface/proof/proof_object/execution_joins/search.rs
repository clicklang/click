//! Discovery adapters over the existing persistent proof.
use super::*;
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Splits the proof on `split`, the variants of the enum a Rust `match`
    /// selects among, and runs each arm to function exit: the proof `match`
    /// a sidecar would write, each arm running to function exit. Arms the facts
    /// rule out are not run. Expansion prints the `match`.
    pub(in crate::surface::proof) fn execute_enum_match_to_exit(
        search_input: &Proof<'a>,
        split: &Arc<ProofMatch>,
        enclosing: &[&ExecutionSplit<'a>],
        retried_requirements: &mut BTreeSet<PropositionIdentityKey>,
        steps: &mut usize,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("execute_enum_match_to_exit");
        let tactic_index = match search_input.context.as_ref() {
            ProofContext::Execution(context) => context.tactic_index,
            _ => {
                return Err(
                    search_input.step_error("a Rust `match` split requires an execution proof")
                );
            }
        };
        let prepared = search_input.prepare_execution_match(false, tactic_index)?;
        let marker = prepared.checkpoint();
        let plan = prepared.plan_execution_match(split, |_| usize::MAX)?;
        let live = plan.live_cases();
        let mut certificates = vec![None; split.arms.len()];
        let Some(proof) = Self::execute_enum_match_group(
            &prepared,
            &plan,
            &live,
            &mut certificates,
            enclosing,
            retried_requirements,
            steps,
        )?
        else {
            return Ok(None);
        };
        let Some(certificates) = certificates.into_iter().collect::<Option<Vec<_>>>() else {
            return Err(
                proof.step_error("a Rust `match` split left a variant without a checked arm")
            );
        };
        Ok(Some(proof.finish_execution_match(
            &marker,
            split,
            certificates,
            plan.take_trace(),
        )?))
    }
    /// Runs one group of live variant arms to function exit, halving the
    /// group at a frontier split until one arm remains, as a written proof
    /// `match` does.
    pub(in crate::surface::proof) fn execute_enum_match_group(
        search_input: &Proof<'a>,
        plan: &ExecutionMatchPlan,
        live: &[usize],
        certificates: &mut [Option<ProofCertificate>],
        enclosing: &[&ExecutionSplit<'a>],
        retried_requirements: &mut BTreeSet<PropositionIdentityKey>,
        steps: &mut usize,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("execute_enum_match_group");
        let [index] = live else {
            let (left, right) = live.split_at(live.len() / 2);
            if left.is_empty() {
                return Err(search_input.step_error("a Rust `match` split has no live variant"));
            }
            let (mut proof, record) =
                search_input.split_execution_match_group(plan.condition(left))?;
            for (take_left, group) in [(true, left), (false, right)] {
                let focused = proof.focus_execution_if_arm(&record, take_left)?;
                let Some(next) = Self::execute_enum_match_group(
                    &focused,
                    plan,
                    group,
                    certificates,
                    enclosing,
                    retried_requirements,
                    steps,
                )?
                else {
                    return Ok(None);
                };
                proof = next;
            }
            return Ok(Some(proof.join_focused_execution_if_terminal(&record)?));
        };
        let index = *index;
        let entered = search_input.enter_execution_match_arm(plan, index)?;
        let marker = entered.checkpoint();
        let Some(proof) = crate::kernel::search::ProofSearch::try_focused_execute_to_exit_within(
            &(entered),
            enclosing.to_vec(),
            retried_requirements,
            steps,
            None,
            None,
        )?
        else {
            return Ok(None);
        };
        if !proof.is_at_function_exit() {
            return Ok(None);
        }
        certificates[index] = Some(proof.execution_match_arm_certificate(&marker)?);
        proof.record_execution_match_arm_trace(plan, index, &marker);
        Ok(Some(proof.leave_terminal_execution_match_arm(plan)?))
    }

    /// Runs nested execution arms with an explicit continuation stack. Each
    /// frame retains the checked split and its parent region chain; completing
    /// an arm either focuses its sibling or joins the checked descendants.
    /// Statement steps share one budget across all frames. Only top-level
    /// advances contribute to `introduced`, as in straight-line execution.
    pub(in crate::surface::proof) fn try_focused_execute_to_exit_within(
        search_input: &Proof<'a>,
        enclosing: Vec<&ExecutionSplit<'a>>,
        retried_requirements: &mut BTreeSet<PropositionIdentityKey>,
        steps: &mut usize,
        mut introduced: Option<&mut Vec<Proposition>>,
        until: Option<StepUntilTarget>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_focused_execute_to_exit_within");
        enum Pending<'a> {
            Branch {
                record: ExecutionSplit<'a>,
                call_outcomes: bool,
                next_else: bool,
                enclosing: imbl::Vector<ExecutionSplit<'a>>,
            },
            Cases {
                record: ExecutionProofCaseSplit<'a>,
                next_else: bool,
                enclosing: imbl::Vector<ExecutionSplit<'a>>,
            },
        }
        let mut pending = Vec::new();
        let mut splits = 0usize;
        let mut enclosing: imbl::Vector<_> = enclosing.into_iter().cloned().collect();
        let mut record_added = |proof: &Proof<'a>| {
            if let Some(introduced) = introduced.as_deref_mut() {
                for fact in proof.added_facts() {
                    if !introduced.contains(fact) {
                        introduced.push(fact.clone());
                    }
                }
            }
        };
        let mut proof = search_input.clone();
        loop {
            while proof.is_at_region_boundary() {
                if proof
                    .execution()
                    .is_some_and(|execution| execution.core.evidence_completed)
                {
                    return Ok(None);
                }
                let Some(record) = enclosing.pop_back() else {
                    return Ok(None);
                };
                proof = proof.continue_arm_into_parent_frontier(&record)?;
            }
            if let Some(StepUntilTarget::FunctionExit) = until {
                if proof.is_at_function_exit() {
                    return Ok(Some(proof));
                }
            } else if let Some(StepUntilTarget::Region(target)) = until {
                match proof.current_statement_index()? {
                    Some(current) if current == target => return Ok(Some(proof)),
                    Some(current) if current < target => {}
                    Some(current) => return Err(proof.step_error(format!(
                        "`step_until(region({target}))` target is not reachable from the current execution path; execution moved the frontier to region({current})"
                    ))),
                    None => return Err(proof.step_error(format!(
                        "`step_until(region({target}))` reached function exit before its target"
                    ))),
                }
            } else if proof.is_at_function_exit() {
                let Some(frame) = pending.pop() else {
                    return Ok(Some(proof));
                };
                match frame {
                    Pending::Branch {
                        record,
                        call_outcomes,
                        next_else,
                        enclosing: parent,
                    } => {
                        if next_else && record.arm_id(false).is_some() {
                            proof = proof.focus_split_arm(&record, false)?;
                            enclosing = parent.clone();
                            enclosing.push_back(record.clone());
                            pending.push(Pending::Branch {
                                record,
                                call_outcomes,
                                next_else: false,
                                enclosing: parent,
                            });
                            continue;
                        }
                        proof = if call_outcomes {
                            proof.join_focused_call_outcomes_terminal(&record)?
                        } else if record.sole_feasible_arm().is_some() {
                            proof.finish_focused_execution_decided(&record)?
                        } else {
                            proof.join_focused_execution_terminal(&record)?
                        };
                        enclosing = parent;
                    }
                    Pending::Cases {
                        record,
                        next_else,
                        enclosing: parent,
                    } => {
                        if next_else {
                            proof = proof.focus_execution_if_arm(&record, false)?;
                            enclosing = parent.clone();
                            pending.push(Pending::Cases {
                                record,
                                next_else: false,
                                enclosing: parent,
                            });
                            continue;
                        }
                        proof = proof.join_focused_execution_if_terminal(&record)?;
                        enclosing = parent;
                    }
                }
                if pending.is_empty() {
                    record_added(&proof);
                }
                retried_requirements.clear();
                continue;
            }
            proof.charge_execute_step(steps, splits)?;
            let stepped = crate::kernel::search::ProofSearch::try_smart_statement_step(
                &(proof),
                ProofStep::Step,
                retried_requirements,
            );
            let stepped = match (stepped, until) {
                (Err(error), Some(target)) => {
                    return Err(step_until_refusal(&proof, target, error)?);
                }
                (stepped, _) => stepped?,
            };
            if let Some(next) = stepped {
                if pending.is_empty() {
                    record_added(&next);
                }
                proof = next;
                retried_requirements.clear();
                continue;
            }
            if let Some(target) = until {
                return match proof.driver().apply_step(ProofStep::Step) {
                    Err(error) => Err(step_until_refusal(&proof, target, error)?),
                    Ok(_) => Err(proof.step_error(format!(
                        "`step_until({})` could not advance this statement",
                        target.describe()
                    ))),
                };
            }
            let split = if proof.is_at_call_outcomes_frontier()? {
                proof
                    .split_focused_call_outcomes()
                    .map(|split| split.map(|(proof, record)| (proof, record, true)))
            } else if proof.is_at_execution_branch()? && !proof.is_at_enum_match_test()? {
                proof
                    .split_focused_execution_branch()
                    .map(|(proof, record)| Some((proof, record, false)))
            } else {
                match proof.driver().apply_step(ProofStep::Step) {
                    Err(error) => Err(error),
                    Ok(_) => return Ok(None),
                }
            };
            match split {
                Ok(Some((split, record, call_outcomes))) => {
                    let take_then = record.arm_id(true).is_some();
                    proof = split.focus_split_arm(&record, take_then)?;
                    let parent = enclosing.clone();
                    enclosing.push_back(record.clone());
                    splits += 1;
                    pending.push(Pending::Branch {
                        record,
                        call_outcomes,
                        next_else: take_then,
                        enclosing: parent,
                    });
                }
                Err(error) if error.path_case_match().is_some() => {
                    let split = Arc::new(error.path_case_match().expect("checked").clone());
                    let parents = enclosing.iter().collect::<Vec<_>>();
                    let Some(next) = Self::execute_enum_match_to_exit(
                        &proof,
                        &split,
                        &parents,
                        retried_requirements,
                        steps,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = next;
                }
                Err(error) if error.is_path_case_split() => {
                    let Some(condition) = error.path_case_condition() else {
                        return Err(error.with_context(
                            "the implicit tail could not split the cases of this C operation",
                        ));
                    };
                    let (split, record) = proof.prepare_focused_execute_cases(condition.clone())?;
                    proof = split.focus_execution_if_arm(&record, true)?;
                    splits += 1;
                    pending.push(Pending::Cases {
                        record,
                        next_else: true,
                        enclosing: enclosing.clone(),
                    });
                }
                Err(error) => return Err(error),
                Ok(None) => return Ok(None),
            }
        }
    }
}
