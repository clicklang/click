//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Runs `step_until` on checked descendants: the implicit tail's search
    /// with a target, which stops before that source statement and follows
    /// one path, refusing where it would have to split. The returned fact
    /// list is only the prefix's output delta; scope adapters use it to
    /// retain facts introduced inside their owned representation.
    pub(in crate::surface::proof) fn try_execute_until_descendant(
        search_input: &Proof<'a>,
        point: &ExecutionPoint,
    ) -> Result<Option<(Proof<'a>, Vec<Proposition>)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execute_until_descendant");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error("checked-only verification forbids step_until; write its execution steps explicitly"));
        }
        let target = match point {
            ExecutionPoint::BackEdge(loop_index) => {
                return crate::kernel::search::ProofSearch::try_execute_to_back_edge_descendant(
                    search_input,
                    *loop_index,
                );
            }
            ExecutionPoint::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Exit,
            }) => {
                if search_input.is_at_function_exit() {
                    return Ok(Some((search_input.clone(), Vec::new())));
                }
                StepUntilTarget::FunctionExit
            }
            ExecutionPoint::ProgramPoint(ProgramPointRef {
                region,
                kind: ProgramPointKind::Entry,
            }) => StepUntilTarget::Region(search_input.resolve_statement_target(region)?),
            ExecutionPoint::ProgramPoint(_) => {
                return Err(search_input.step_error("`step_until` cannot reach this program point"));
            }
        };
        if let StepUntilTarget::Region(target) = target {
            let Some(current) = search_input.current_statement_index()? else {
                return Err(search_input.step_error(format!(
                    "`step_until({})` cannot run after execution already reached function exit",
                    crate::surface::diagnostics::describe_execution_point(point)
                )));
            };
            if target < current {
                return Err(search_input.step_error(format!(
                    "`step_until({})` cannot move backward from region({current})",
                    crate::surface::diagnostics::describe_execution_point(point)
                )));
            }
            if target == current {
                // Reaching the requested frontier is success, including inside
                // a proof branch or resource scope. `None` means unsupported to
                // those drivers and incorrectly declines a valid no-op.
                return Ok(Some((search_input.clone(), Vec::new())));
            }
        }
        let mut introduced_facts = Vec::new();
        let Some(proof) = crate::kernel::search::ProofSearch::try_focused_execute_to_exit_within(
            search_input,
            Vec::new(),
            &mut BTreeSet::new(),
            &mut 0,
            Some(&mut introduced_facts),
            Some(target),
        )?
        else {
            return Ok(None);
        };
        Ok(Some((proof, introduced_facts)))
    }

    /// Finish only the current preservation region. Every advance is an
    /// ordinary checked step; reaching the boundary grants no invariant or
    /// termination authority. Refuse branch splits and non-back-edge exits.
    pub(in crate::surface::proof) fn try_execute_to_back_edge_descendant(
        search_input: &Proof<'a>,
        loop_index: Option<usize>,
    ) -> Result<Option<(Proof<'a>, Vec<Proposition>)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execute_to_back_edge_descendant");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error("checked-only verification forbids implicit back-edge execution; write its execution steps explicitly"));
        }
        let frontier = &search_input
            .execution()
            .ok_or_else(|| {
                search_input.step_error("`loop.back_edge` requires a loop preservation frontier")
            })?
            .core
            .frontier;
        if !frontier.in_loop_body
            || frontier.region != crate::kernel::proof::ExecutionRegionKind::LoopBody
        {
            return Err(search_input.step_error("`loop.back_edge` requires the current loop preservation region; it cannot select a branch arm boundary"));
        }
        if let Some(loop_index) = loop_index {
            let preserved = match search_input.context.as_ref() {
                ProofContext::Execution(context) => context
                    .constants
                    .invariant_body_context
                    .as_ref()
                    .map(|body| body.loop_index),
                _ => None,
            };
            if preserved != Some(loop_index) {
                let current = preserved
                    .map(|index| format!("; this preservation region is `loop({index})`'s"))
                    .unwrap_or_default();
                return Err(search_input.step_error(format!(
                    "`loop({loop_index}).back_edge` names the back edge of the `loop({loop_index})` preservation region{current}"
                )));
            }
        }
        if frontier.is_at_region_boundary() && !frontier.loop_control.is_exit() {
            return Ok(None);
        }
        let mut proof = search_input.clone();
        let mut facts = Vec::new();
        let mut retried = BTreeSet::new();
        let mut steps = 0;
        loop {
            let frontier = &proof
                .execution()
                .ok_or_else(|| proof.step_error("execution proof lost its semantic frontier"))?
                .core
                .frontier;
            if frontier.region != crate::kernel::proof::ExecutionRegionKind::LoopBody {
                return Err(proof.step_error("`loop.back_edge` cannot finish a nested branch or loop region; prove that region separately"));
            }
            if frontier.is_at_region_boundary() {
                if frontier.loop_control.is_exit() {
                    return Err(proof.step_error(
                        "`loop.back_edge` reached a loop exit instead of the back edge",
                    ));
                }
                return Ok(Some((proof, facts)));
            }
            if frontier.is_at_function_exit() {
                return Err(proof.step_error(
                    "`loop.back_edge` reached function exit instead of the back edge",
                ));
            }
            proof.charge_execute_step(&mut steps, 0)?;
            if let Some(next) = crate::kernel::search::ProofSearch::try_smart_statement_step(
                &(proof),
                ProofStep::Step,
                &mut retried,
            )? {
                facts.extend(next.added_facts().iter().cloned());
                proof = next;
                retried.clear();
            } else {
                return match proof.driver().apply_step(ProofStep::Step) {
                    Err(error) => Err(error),
                    Ok(_) => Err(proof.step_error(
                        "`loop.back_edge` found no checked advance from this frontier",
                    )),
                };
            }
        }
    }

    /// Runs `step_until` on this Proof and returns only the
    /// already-accepted descendant.
    pub(in crate::surface::proof) fn try_execute_until(
        search_input: &Proof<'a>,
        point: &ExecutionPoint,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execute_until");
        Ok(
            crate::kernel::search::ProofSearch::try_execute_until_descendant(search_input, point)?
                .map(|(proof, _)| proof),
        )
    }

    /// Runs the implicit tail to function exit on checked descendants: one
    /// statement step at a time, splitting at C branches, call outcomes, and
    /// path cases. A partial path is discarded unless it reaches function
    /// exit. The returned fact list is the top-level advances' output delta.
    pub(in crate::surface::proof) fn try_execute_to_exit_descendant(
        search_input: &Proof<'a>,
    ) -> Result<Option<(Proof<'a>, Vec<Proposition>)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execute_to_exit_descendant");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error("checked-only verification forbids implicit execution; write its execution steps explicitly"));
        }
        if search_input.is_at_function_exit() {
            return Ok(None);
        }
        // The statement steps below are the implicit tail's, and a refusal
        // names the step that refused; the returned descendant carries this
        // proof's own context again, so checkpoints taken before it still
        // apply.
        let proof = search_input.with_execution_step_tactic_name("step()");
        // Retrying a refused statement is bounded by the owning smart
        // operation: one retained-have attempt per distinct requirement
        // identity. The set follows this immutable search, rather than a
        // process-global cache, so unrelated proofs cannot affect it.
        let mut retried_requirements = BTreeSet::new();
        let mut introduced_facts = Vec::new();
        let Some(proof) = crate::kernel::search::ProofSearch::try_focused_execute_to_exit_within(
            &(proof),
            Vec::new(),
            &mut retried_requirements,
            &mut 0,
            Some(&mut introduced_facts),
            None,
        )?
        else {
            return Ok(None);
        };
        Ok(Some((
            proof.with_context_of(search_input),
            introduced_facts,
        )))
    }

    /// Returns the already-checked function-exit descendant selected by the
    /// implicit tail's search.
    pub(in crate::surface::proof) fn try_execute_to_exit(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execute_to_exit");
        Ok(
            crate::kernel::search::ProofSearch::try_execute_to_exit_descendant(search_input)?
                .map(|(proof, _)| proof),
        )
    }

    /// Searches explicit premise forms for one fixed-state fact transport.
    ///
    /// Every candidate is checked by applying the corresponding proof step
    /// to this immutable root. Failed descendants are discarded. Return
    /// the checked successor so callers reuse its ordinary proof.
    pub(in crate::surface::proof) fn try_fixed_state_fact_transport(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_fixed_state_fact_transport");
        let result_aware = matches!(search_input.context.as_ref(), ProofContext::FixedState(_))
            || search_input.focused_outcome_data().is_some()
            || search_input
                .execution_proposition_fixed_state_view()
                .is_some();
        if !result_aware {
            return Err(search_input.step_error(
                "fact-transport search requires a fixed-state proof, focused outcome goal, or execution proposition scope",
            ));
        }
        crate::kernel::search::ProofSearch::try_fact_transport_from_candidates(
            search_input,
            source,
            target,
            candidates,
        )
    }

    /// Close an explicitly selected historical equality inside an execution
    /// proposition scope by retaining the separation and preservation proof.
    pub(in crate::surface::proof) fn try_execution_proposition_read_preservation(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
        point_limit: usize,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_proposition_read_preservation");
        if search_input
            .execution_proposition_fixed_state_view()
            .is_none()
        {
            return Ok(None);
        }
        if let Some(proof) =
            Self::try_indexed_read_preservation(search_input, target, point_limit, true)?
        {
            return Ok(Some(proof));
        }
        Self::try_recorded_footprint_preservation(search_input, source, target)
    }

    /// Tries the bounded source-local form of mid-execution fact transport on
    /// this immutable execution Proof. The smart operation checks ordinary
    /// proof steps for the selected source and target.
    pub(in crate::surface::proof) fn try_execution_fact_transport(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_fact_transport");
        Ok(
            crate::kernel::search::ProofSearch::try_execution_fact_transport_or_refusal(
                search_input,
                source,
                target,
            )?
            .ok(),
        )
    }

    /// The bounded source-local form of mid-execution fact transport, as
    /// [`Self::try_execution_fact_transport`], keeping the refusal of its
    /// last candidate: the checked `transport using` with the source as its
    /// only premise. A bare `transport` whose premise planner then fails
    /// reports that refusal, which names what the frame could not carry
    /// (`fact_transport_planning_failure`). Keeping it costs nothing: the
    /// check already ran.
    pub(in crate::surface::proof) fn try_execution_fact_transport_or_refusal(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Result<Proof<'a>, Option<ClickError>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_fact_transport_or_refusal");
        if crate::instrumentation::replay_forbids_discovery("fact transport search") {
            return Err(search_input.step_error("fact transport discovery needs explicit premises"));
        }
        let ProofContext::Execution(_) = search_input.context.as_ref() else {
            return Err(search_input
                .step_error("execution fact-transport search requires an execution proof"));
        };
        let execution = search_input.execution().ok_or_else(|| {
            search_input.step_error("execution fact-transport search lost its semantic frontier")
        })?;
        if execution.core.frontier.is_at_function_entry() {
            return Err(search_input.step_error(
                "`transport` requires a current statement frontier after at least one execution step",
            ));
        }
        // A focused function outcome is planned against its returned state;
        // a bare exit frontier has no state to transport into.
        if execution.core.frontier.is_at_function_exit()
            && search_input.focused_outcome_data().is_none()
        {
            return Ok(Err(None));
        }
        match crate::kernel::search::ProofSearch::fact_transport_candidate_search(
            search_input,
            source,
            target,
            std::iter::once(source.clone()),
        ) {
            Ok(Ok(proof)) => Ok(Ok(proof)),
            Ok(Err(_)) if !crate::instrumentation::deadline_exceeded() => {
                // Keep the written bare tactic's source-only refusal for
                // diagnostics. Only the ordinary search above can admit a fact.
                let refusal = search_input.source_only_transport_refusal(source, target);
                Ok(Err(refusal))
            }
            Ok(Err(refusal)) => {
                // A budget stop is a failure of this written operation, not
                // an abandoned candidate. Retain the checked predecessor.
                search_input.record_certification_failure_trace(search_input.claim_label(), 0);
                Err(search_input.attach_step_diagnostic(search_input.step_error(format!(
                    "execution-frontier fact transport has no explicit surface-premise certificate: {}",
                    refusal
                        .as_ref()
                        .map(|error| error.raw_summary())
                        .unwrap_or("no candidate was checked")
                ))))
            }
            Err(error) if crate::instrumentation::deadline_exceeded() => {
                search_input.record_certification_failure_trace(search_input.claim_label(), 0);
                Err(search_input.attach_step_diagnostic(error))
            }
            Err(_) => Ok(Err(None)),
        }
    }

    /// Ordinary search misses carry no outer diagnostic: smart callers
    /// discard them. The checked candidate refusals remain available to
    /// the execution planner that needs to report a written operation.
    pub(in crate::surface::proof) fn try_fact_transport_from_candidates(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_fact_transport_from_candidates");
        Ok(
            crate::kernel::search::ProofSearch::fact_transport_candidate_search(
                search_input,
                source,
                target,
                candidates,
            )?
            .ok(),
        )
    }

    /// Try progressively more of the supplied premises with ordinary proof
    /// steps.
    pub(in crate::surface::proof) fn fact_transport_candidate_search(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Result<Proof<'a>, Option<ClickError>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("fact_transport_candidate_search");
        if crate::instrumentation::replay_forbids_discovery("fact transport search") {
            return Err(search_input.step_error("fact transport discovery needs explicit premises"));
        }
        if let Some(proof) =
            Self::try_recorded_footprint_preservation(search_input, source, target)?
        {
            return Ok(Ok(proof));
        }
        if let Some(proof) = Self::try_history_indexed_equalities(search_input, source, target)? {
            return Ok(Ok(proof));
        }
        let mut selected = Vec::new();
        if let Some(proof) =
            Self::try_ordinary_fact_transport(search_input, source, target, &selected)?
        {
            return Ok(Ok(proof));
        }
        for candidate in candidates {
            check_verification_deadline()?;
            if selected.contains(&candidate) {
                continue;
            }
            selected.push(candidate);
            if let Some(proof) =
                Self::try_ordinary_fact_transport(search_input, source, target, &selected)?
            {
                return Ok(Ok(proof));
            }
        }
        Ok(Err(None))
    }
}
