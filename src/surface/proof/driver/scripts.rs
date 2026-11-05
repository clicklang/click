//! Proof script orchestration; explicit operations remain on Proof.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Applies a planner's flat explicit candidate directly to persistent
    /// `Proof` descendants. Planning may select surface operations, but only
    /// their checked implementations can advance the proof.
    ///
    /// Generated candidates historically retain a final `assumption()` even
    /// when the preceding operation already discharged the goal. Ignore only
    /// that final no-op; any other operation after closure rejects the
    /// candidate. No certificate is materialized or interpreted here.
    pub(in crate::surface::proof) fn try_planned_explicit_steps(
        &self,
        tactics: &[ProofTactic],
    ) -> Option<Proof<'a>> {
        let driver_proof = self.proof;
        if tactics.is_empty() {
            return None;
        }
        let mut proof = driver_proof.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Assumption) {
                    continue;
                }
                return None;
            }
            let step = SourceContext::PureGoal.leaf_step(tactic)?;
            proof = proof.driver().apply_step(step).ok()?;
        }
        proof.focused_discharged().then_some(proof)
    }

    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .try_authoritative_linear_script_reporting(tactics, &mut None, None)
    }

    /// [`Self::try_authoritative_linear_script`], also reporting why the body
    /// declined. A caller that turns the decline into a user-facing error
    /// needs the written step to name, not only that some route said no.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_reporting(
        &self,
        tactics: &[ProofTactic],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Proof<'a>>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        // Address each tactic's diagnostics by its position in the block the
        // user wrote, so a failure inside one `have` body is distinguishable
        // from the same failure inside another.
        let sites = (0..tactics.len())
            .map(|index| driver_proof.site().at_block_position(index))
            .collect::<Vec<_>>();
        driver_proof
            .driver()
            .try_addressed_linear_script(tactics, &sites, declined, unfinished)
    }

    /// Checks an explicit planner candidate without attributing its block
    /// positions to a written source body, then restores the caller's site.
    pub(in crate::surface::proof) fn try_generated_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .at_source_tactic(usize::MAX)
            .driver()
            .try_authoritative_linear_script(tactics)
            .map(|proof| proof.map(|proof| proof.at_site(driver_proof.site())))
    }

    /// The linear script runner. `sites[index]` is where `tactics[index]`
    /// was written. A proof `if` or `cases` arm is checked together with the
    /// tactics after it, so its script joins the arm's own tactics, addressed
    /// inside that arm, to the continuation, which keeps the addresses it has
    /// in the enclosing block: every written tactic reports its own source
    /// position however many arms check it.
    pub(in crate::surface::proof) fn try_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Proof<'a>>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .run_addressed_linear_script(tactics, sites, declined, unfinished)
    }

    /// [`Self::try_authoritative_linear_script`], also keeping the proof a
    /// body left with its focused goal still open, so a caller refusing the
    /// body can name the goal it stopped at. Only a script that ran every
    /// written step (in its own block or in a proof `if`, `cases` or `both`
    /// arm) leaves one; a declined step leaves none.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_leaving_open(
        &self,
        tactics: &[ProofTactic],
        unfinished: &mut Option<Proof<'a>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .try_authoritative_linear_script_reporting(tactics, &mut None, Some(unfinished))
    }

    /// Runs the arms of one `cases` to completion. The kernel splits a
    /// disjunction in two, so more than two arms split the leading arms'
    /// disjunction against the last arm and recurse into the leading branch;
    /// each arm still runs at the sites of its own source block.
    fn run_case_arms(
        &self,
        arms: &[CaseArmScript<'_>],
        mut unfinished: Option<&mut Option<Proof<'a>>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        let (last, leading) = arms.split_last().expect("`cases` has arms");
        let disjunction = leading.iter().skip(1).fold(
            leading
                .first()
                .expect("`cases` has at least two arms")
                .assumption
                .clone(),
            |disjunction, arm| {
                ClickProposition::Or(Box::new(disjunction), Box::new(arm.assumption.clone()))
            },
        );
        let disjunction =
            ClickProposition::Or(Box::new(disjunction), Box::new(last.assumption.clone()));
        let (split_proof, split, ids) = driver_proof.split_focused_cases(disjunction.clone())?;
        let marker = split_proof.checkpoint();
        let leading_branch = split_proof.focus_branch(ids[0])?;
        let leading_done = match leading {
            [only] => leading_branch.driver().run_addressed_linear_script(
                &only.tactics,
                &only.sites,
                &mut None,
                unfinished.as_deref_mut(),
            )?,
            _ => leading_branch
                .driver()
                .run_case_arms(leading, unfinished.as_deref_mut())?,
        };
        let Some(leading_done) = leading_done else {
            return Ok(None);
        };
        let Some(all_done) = leading_done
            .focus_branch(ids[1])?
            .driver()
            .run_addressed_linear_script(&last.tactics, &last.sites, &mut None, unfinished)?
        else {
            return Ok(None);
        };
        all_done
            .join_focused_cases(&marker, split, ids, disjunction)
            .map(Some)
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn run_pure_match_group(
        &self,
        plan: &super::proof_object::PureMatchPlan,
        source: &ProofMatch,
        indices: &[usize],
        arm_tactics: &[Vec<ProofTactic>],
        arm_sites: &[Vec<ProofStepSite>],
        certificates: &mut Vec<ProofCertificate>,
        trace: &mut Option<crate::surface::proof_trace::TraceMatch>,
        mut unfinished: Option<&mut Option<Proof<'a>>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        if let [index] = indices {
            let arm = driver_proof.enter_pure_match_case(plan, *index)?;
            let marker = arm.checkpoint();
            let written = source.arms[*index].tactics.len();
            let mut pending = Some(arm.clone());
            let closed = if written == 0 {
                None
            } else {
                arm.driver().run_addressed_linear_script(
                    &arm_tactics[*index][..written],
                    &arm_sites[*index][..written],
                    &mut None,
                    Some(&mut pending),
                )?
            };
            let Some(body_done) = closed.or(pending) else {
                return Ok(None);
            };
            let body_done = body_done.leave_pure_match_case(plan);
            let done = if written < arm_tactics[*index].len() {
                let Some(done) = body_done.driver().run_addressed_linear_script(
                    &arm_tactics[*index][written..],
                    &arm_sites[*index][written..],
                    &mut None,
                    unfinished,
                )?
                else {
                    return Ok(None);
                };
                done
            } else if body_done.focused_discharged() {
                body_done
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(body_done);
                }
                return Ok(None);
            };
            certificates.push(done.certificate_since(&marker)?);
            if let Some(trace) = trace {
                trace.arms[*index] = Some(done.pure_match_arm_trace(&arm, &marker, source, *index));
            }
            return Ok(Some(done.leave_pure_match_case(plan)));
        }
        let middle = indices.len() / 2;
        let (split_proof, split, ids) = driver_proof.split_pure_match_group()?;
        let marker = split_proof.checkpoint();
        let Some(left_done) = split_proof
            .focus_branch(ids[0])?
            .driver()
            .run_pure_match_group(
                plan,
                source,
                &indices[..middle],
                arm_tactics,
                arm_sites,
                certificates,
                trace,
                unfinished.as_deref_mut(),
            )?
        else {
            return Ok(None);
        };
        let Some(done) = left_done
            .focus_branch(ids[1])?
            .driver()
            .run_pure_match_group(
                plan,
                source,
                &indices[middle..],
                arm_tactics,
                arm_sites,
                certificates,
                trace,
                unfinished,
            )?
        else {
            return Ok(None);
        };
        done.join_focused_both(&marker, split, ids).map(Some)
    }

    pub(in crate::surface::proof) fn run_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        mut unfinished: Option<&mut Option<Proof<'a>>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        debug_assert_eq!(tactics.len(), sites.len());
        let finish = |proof: Proof<'a>, unfinished: Option<&mut Option<Proof<'a>>>| {
            if proof.focused_discharged() {
                Some(proof)
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(proof);
                }
                None
            }
        };
        let pure_source = matches!(driver_proof.context.as_ref(), ProofContext::Pure(_));
        if tactics.is_empty() {
            *declined = Some(LinearScriptDecline::Shape);
            return Ok(None);
        }
        let arm_sites = |index: usize, arm: usize, name: &'static str, written: usize| {
            (0..written)
                .map(|position| sites[index].in_arm(arm, name, position))
                .chain(sites[index + 1..].iter().cloned())
                .collect::<Vec<_>>()
        };

        let mut proof = driver_proof.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            proof = proof.at_site(&sites[index]);
            let _timing = if pure_source {
                proof
                    .site()
                    .written_source_tactic_path()
                    .and_then(|path| TacticTiming::pure_source(proof.claim_label(), path, tactic))
            } else {
                None
            };
            let _origin = super::timing::trace_origin(tactic);
            let nested_capture = proof.begin_nested_tactic_capture();
            if proof.focused_discharged() {
                // A closer after a step that already discharged the goal (a
                // `transport` whose target is the goal, an exact theorem
                // conclusion, an `unfold` whose refreshed goal was already
                // an available fact) asserts a closed judgment: a harmless
                // no-op that emits no redundant certificate step. That is
                // `assumption`, a bare `solve`, and the context-free `normalize`,
                // in any position, so `unfold(f(x)); normalize();` means the
                // same whether or not the unfold alone closed the goal. Any
                // other suffix after closure is a declined shape, named with
                // the tactic that closed the goal.
                if matches!(
                    tactic,
                    ProofTactic::Assumption
                        | ProofTactic::Solve
                        | ProofTactic::Normalize
                        | ProofTactic::NormalizeUsing(_)
                ) {
                    // The harmless closer checks nothing: its expansion is
                    // empty.
                    if let Some(capture) = nested_capture {
                        capture.finish(&proof);
                    }
                    continue;
                }
                let closer = index
                    .checked_sub(1)
                    .and_then(|previous| tactics.get(previous))
                    .map_or("an earlier tactic".to_string(), |closer| {
                        format!("`{}`", tactic_name(closer))
                    });
                // `solve() using` is refused here where a bare `solve()`
                // is not, so it is named by its whole spelling.
                let name = match tactic {
                    ProofTactic::SolveUsing(_) => "solve() using",
                    tactic => tactic_name(tactic),
                };
                return Err(proof.step_error(format!(
                    "`{name}` follows a goal-closing tactic: {closer} already closed this goal, so only `assumption()`, a bare `solve()`, or `normalize()` may follow it",
                )));
            }
            // A step that adds a fact can close the goal before a written
            // suffix. Retain that completed step as a checked have, keeping
            // the outer goal open so every remaining explicit step is
            // checked; only a final step, or one followed by a harmless
            // closer, leaves the goal closed.
            let retain_application = matches!(
                tactic,
                ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInductionUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::InstantiateUsing { .. }
                    | ProofTactic::Transport { .. }
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::LetSatisfy(_)
            ) && tactics
                .get(index + 1)
                .is_some_and(|next| !matches!(next, ProofTactic::Assumption | ProofTactic::Solve));
            let retain_application = retain_application
                || (matches!(
                    tactic,
                    ProofTactic::Extract(_) | ProofTactic::ApplyTheorem(_)
                ) && tactics.get(index + 1).is_some_and(|next| {
                    !matches!(next, ProofTactic::Assumption | ProofTactic::Solve)
                }));
            let before_application = retain_application.then(|| proof.clone());
            match tactic {
                ProofTactic::ApplyInduction {
                    hypothesis,
                    arguments,
                } => {
                    proof = crate::kernel::search::ProofSearch::apply_smart_induction(
                        &(proof),
                        hypothesis,
                        arguments,
                    )?;
                }
                ProofTactic::ApplyTheorem(application) => {
                    proof = proof.driver().apply_theorem_application(application)?;
                }
                ProofTactic::Solve => {
                    let mut search = attempt::search_scope("written solve");
                    let (selected, checks) =
                        crate::surface::proof_diagnostics::capture_check_observations(|| {
                            crate::kernel::search::ProofSearch::try_solve_closure(&(proof))
                        });
                    let selected = match selected {
                        Ok(selected) => selected,
                        Err(error) => {
                            return Err(error
                                .with_check_observations(checks)
                                .with_search_failures(search.finish()));
                        }
                    };
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `solve` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ).with_search_failures(search.finish()));
                        }
                        return Err(proof
                            .solve_failure()
                            .with_check_observations(checks)
                            .with_search_failures(search.finish()));
                    };
                    search.succeed();
                    proof = closed;
                }
                ProofTactic::SolveUsing(solve) => {
                    let (selected, checks) =
                        crate::surface::proof_diagnostics::capture_check_observations(|| {
                            crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                                &(proof),
                                &solve.premises,
                            )
                        });
                    check_verification_deadline()?;
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `solve` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ));
                        }
                        // Arithmetic is the last closer `solve() using`
                        // tries; its own refusal says why the listed
                        // premises fall short, as `arithmetic() using`
                        // reported it.
                        let arithmetic = match proof
                            .driver()
                            .apply_step(ProofStep::ArithmeticUsing(solve.premises.clone()))
                        {
                            Err(error) => {
                                // The reason without its location prefix,
                                // which the report already gives.
                                let summary = error.raw_summary();
                                let reason = summary
                                    .find("` proof step tactic")
                                    .and_then(|at| summary[at..].find(": ").map(|end| at + end + 2))
                                    .map_or(summary, |start| &summary[start..]);
                                // A goal outside arithmetic's fragment has
                                // nothing to add about the premises.
                                if reason.starts_with("arithmetic requires a supported") {
                                    String::new()
                                } else {
                                    format!("; {reason}")
                                }
                            }
                            Ok(_) => String::new(),
                        };
                        check_verification_deadline()?;
                        return Err(proof.step_error(format!("`solve() using` could not prove the current goal from only its listed premises{arithmetic}")).with_check_observations(checks));
                    };
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let source_proof = have.checking_proof();
                    let selected = match source_proof.as_ref() {
                        SourceProof::Tactic(SmartTactic::ImplicitTail) => {
                            let Some(selected) = scope.driver().try_solve_closure()? else {
                                // The omitted body runs `solve`: its
                                // miss is refused there, with the `have`'s
                                // goal, not declined to the enclosing claim.
                                let body = scope.body();
                                let solve = body.at_site(&body.site().at_block_position(0));
                                return Err(solve.step_error(format!(
                                    "`solve` could not prove `{}`",
                                    describe_click_proposition(&have.proposition)
                                )));
                            };
                            Some(selected)
                        }
                        SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
                            (scope).driver().try_solve_closure()?
                        }
                        SourceProof::Script(body) => {
                            scope.driver().try_authoritative_linear_script(body)?
                        }
                    };
                    let Some(selected) = selected else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let then_tactics =
                        script_arm_with_continuation(&proof_if.then_tactics, &tactics[index + 1..]);
                    let else_tactics =
                        script_arm_with_continuation(&proof_if.else_tactics, &tactics[index + 1..]);
                    let then_sites = arm_sites(index, 0, "then", proof_if.then_tactics.len());
                    let else_sites = arm_sites(index, 1, "else", proof_if.else_tactics.len());
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof
                        .focus_branch(ids[0])?
                        .driver()
                        .run_addressed_linear_script(
                            &then_tactics,
                            &then_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = then_done
                        .focus_branch(ids[1])?
                        .driver()
                        .run_addressed_linear_script(
                            &else_tactics,
                            &else_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_if(&marker, split, ids, proof_if.condition.clone())?
                        .at_site(&sites[index]);
                    // Both arms checked the tactics after the `if`; a trace
                    // to one of those follows the first arm.
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Both(both) => {
                    // A `both` arm proves one conjunct and continues nothing.
                    let own_arm_sites = |arm: usize, name: &'static str, written: usize| {
                        (0..written)
                            .map(|position| sites[index].in_arm(arm, name, position))
                            .collect::<Vec<_>>()
                    };
                    let left_sites = own_arm_sites(0, "left", both.left_tactics.len());
                    let right_sites = own_arm_sites(1, "right", both.right_tactics.len());
                    let (split_proof, split, ids) = proof.split_focused_both()?;
                    let marker = split_proof.checkpoint();
                    let Some(left_done) = split_proof
                        .focus_branch(ids[0])?
                        .driver()
                        .run_addressed_linear_script(
                            &both.left_tactics,
                            &left_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = left_done
                        .focus_branch(ids[1])?
                        .driver()
                        .run_addressed_linear_script(
                            &both.right_tactics,
                            &right_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_both(&marker, split, ids)?
                        .at_site(&sites[index]);
                }
                ProofTactic::Match(source) if pure_source => {
                    let (prepared, plan) = proof.prepare_pure_match(source)?;
                    let marker = prepared.checkpoint();
                    let bodies = source
                        .arms
                        .iter()
                        .map(|arm| {
                            script_arm_with_continuation(&arm.tactics, &tactics[index + 1..])
                                .into_owned()
                        })
                        .collect::<Vec<_>>();
                    let addressed = source
                        .arms
                        .iter()
                        .enumerate()
                        .map(|(arm, body)| arm_sites(index, arm, "case", body.tactics.len()))
                        .collect::<Vec<_>>();
                    let mut certificates = Vec::new();
                    let mut trace = proof.new_pure_match_trace(source);
                    let Some(done) = prepared.driver().run_pure_match_group(
                        &plan,
                        source,
                        &(0..source.arms.len()).collect::<Vec<_>>(),
                        &bodies,
                        &addressed,
                        &mut certificates,
                        &mut trace,
                        unfinished.as_deref_mut(),
                    )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done
                        .finish_execution_match(&marker, source, certificates, trace)?
                        .at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Cases(proof_cases) => {
                    // Each arm runs its own tactics and then the rest of the
                    // script, at the source sites of its own block.
                    let arm_names = if proof_cases.arms().len() == 2 {
                        ["left", "right"].as_slice()
                    } else {
                        ["case"].as_slice()
                    };
                    let arms = proof_cases
                        .arms()
                        .iter()
                        .enumerate()
                        .map(|(arm_index, arm)| CaseArmScript {
                            assumption: arm.assumption(),
                            tactics: script_arm_with_continuation(
                                arm.tactics(),
                                &tactics[index + 1..],
                            ),
                            sites: arm_sites(
                                index,
                                arm_index,
                                arm_names[arm_index.min(arm_names.len() - 1)],
                                arm.tactics().len(),
                            ),
                        })
                        .collect::<Vec<_>>();
                    let Some(done) = proof
                        .driver()
                        .run_case_arms(&arms, unfinished.as_deref_mut())?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done.at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Transport { source, target } => {
                    // The bare form selects its frame evidence at the
                    // execution frontier this `have` was opened on, exactly
                    // as between top-level steps: the source-local candidates
                    // first, then the premise planner, whose refusal is the
                    // answer. A pure theorem has no frontier to select from.
                    if !matches!(proof.context.as_ref(), ProofContext::Execution(_)) {
                        return Err(proof.step_error(
                            "bare `transport` selects its premises at a C execution frontier, and this proof has none; write `transport(P, Q) using { ... }` with the premises it needs",
                        ));
                    }
                    proof = match crate::kernel::search::ProofSearch::try_execution_fact_transport_or_refusal(&(proof), source, target)? {
                        Ok(transported) => transported,
                        Err(source_refusal) => proof.apply_planned_fact_transport(
                            source,
                            target,
                            index,
                            source_refusal.as_ref(),
                        )?,
                    };
                }
                tactic => {
                    if matches!(tactic, ProofTactic::Sorry) {
                        // Admitted only as a complete body (a `have` body
                        // reaching this runner, or a direct engine call with
                        // a single tactic). A bare `sorry` among other
                        // tactics would cover an unbounded suffix, so it is
                        // rejected to keep holes minimal.
                        if tactics.len() != 1 {
                            return Err(proof.step_error(
                                "`sorry` is only allowed as a complete `have` body or a complete contract proof body; it cannot cover a suffix of other tactics",
                            ));
                        }
                        if !crate::surface::verification::sorry_is_allowed() {
                            return Err(proof.step_error(
                                "`sorry` requires `click verify --allow-sorry`; it is a dev-only proof hole and never verifies in the gate",
                            ));
                        }
                        let label = proof
                            .surface_goal()
                            .map(crate::surface::diagnostics::describe_click_proposition)
                            .map(|goal| format!("have {goal}"))
                            .unwrap_or_else(|| "have (goal unavailable)".to_string());
                        crate::surface::verification::record_sorry_admission(label, String::new());
                        proof = proof.admit_focused_goal_for_sorry()?;
                        continue;
                    }
                    let step = SourceContext::PureGoal
                        .leaf_step(tactic)
                        .ok_or_else(|| proof.unsupported_operation_error(tactic_name(tactic)))?;
                    proof = proof.driver().apply_step(step)?;
                }
            }
            // A written step that checks the goal under another spelling of
            // the same order claim (`0 <= e` for the goal `e >= 0`) has
            // proved the goal. Close it with a recorded `assumption`, which
            // accepts that spelling, so the certificate re-runs on its own;
            // a planned step sequence never reaches this runner and keeps
            // the goal open after such a step.
            if matches!(
                tactic,
                ProofTactic::ApplyTheorem(_)
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInductionUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::InstantiateUsing { .. }
                    | ProofTactic::Transport { .. }
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::LetSatisfy(_)
            ) && !proof.focused_discharged()
                && checked_fact_spells_the_goal(&proof)
            {
                proof = proof.driver().apply_step(ProofStep::Assumption)?;
            }
            if let Some(before) = before_application
                && proof.focused_discharged()
            {
                // An application guarantees every conclusion of its theorem,
                // and an `extract` the whole fact it extracted, not only the
                // part that happened to be the goal.
                let conclusions = match tactic {
                    ProofTactic::ApplyTheorem(application)
                    | ProofTactic::ApplyTheoremUsing { application, .. } => {
                        before.theorem_application_surface_conclusions(application)
                    }
                    ProofTactic::Extract(proposition) => vec![proposition.clone()],
                    _ => Vec::new(),
                };
                proof = before.retain_completed_goal(&proof, &conclusions)?;
            }
            if let Some(capture) = nested_capture {
                capture.finish(&proof);
            }
        }

        Ok(finish(proof, unfinished))
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Proves `conclusion` from exactly `premises` by Integer arithmetic,
    /// `arithmetic() using`, which expands to the explicit arithmetic
    /// certificate, and keeps it as a fact.
    pub(in crate::surface::proof) fn have_by_integer_arithmetic(
        &self,
        conclusion: ClickProposition,
        premises: Vec<ClickProposition>,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .apply_step(super::wide_arithmetic::have(
                conclusion,
                vec![ProofStep::ArithmeticUsing(premises)],
            ))
    }

    /// Applies one uint32 lemma and closes the goal with its conclusion.
    pub(in crate::surface::proof) fn close_with_unsigned_lemma(
        &self,
        name: &str,
        arguments: Vec<ContractExpression>,
        premise: ClickProposition,
    ) -> Option<Proof<'a>> {
        let driver_proof = self.proof;
        let applied = driver_proof
            .driver()
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: name.to_string(),
                    arguments,
                },
                premises: vec![premise],
            })
            .ok()?;
        // The lemma's conclusion is the goal, so applying it discharges the
        // goal where it is stated exactly; the focus then leaves it, though
        // sibling goals (other members of a loop bundle) may remain.
        if applied.is_complete() || applied.goal() != driver_proof.goal() {
            return Some(applied);
        }
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
            .ok()
            .flatten()
    }
}
