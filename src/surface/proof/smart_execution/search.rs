//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Runs `step_until` as ordinary steps on one checked path, refusing
    /// where it would have to split. The returned fact
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
            proof = proof.driver().apply_step(ProofStep::Step)?;
            facts.extend(proof.added_facts().iter().cloned());
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
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        candidates: impl IntoIterator<Item = SyntaxProposition>,
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
        source: &SyntaxProposition,
        target: &SyntaxProposition,
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
    /// this immutable execution Proof. The smart operation checks the empty
    /// candidate and the source's own explicit form; it never scans the
    /// ambient fact set. Richer premise discovery remains unavailable until
    /// it has a relevance index rather than an environment-wide scan.
    pub(in crate::surface::proof) fn try_execution_fact_transport(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_fact_transport");
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
            return Ok(None);
        }
        Ok(
            attempt::candidate_outcome(Self::fact_transport_candidate_search(
                search_input,
                source,
                target,
                [source.clone()],
            ))?
            .flatten(),
        )
    }

    /// Written transport uses the same source-local candidates as other
    /// search. Its remaining routes must also construct an ordinary proof.
    pub(in crate::surface::proof) fn apply_written_fact_transport(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        tactic_index: usize,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_written_fact_transport");
        let attempt = || {
            if let Some(proof) = Self::try_execution_fact_transport(search_input, source, target)? {
                return Ok(proof);
            }

            if search_input.focused_outcome_data().is_none()
                && search_input
                    .execution()
                    .is_some_and(|execution| execution.core.frontier.is_at_function_exit())
            {
                return Err(search_input.step_error("`transport` requires a current statement frontier after at least one execution step"));
            }
            let view = search_input
                .outcome_fixed_state_view()
                .or_else(|| search_input.execution_fixed_state_view())
                .ok_or_else(|| {
                    search_input.step_error("`transport` requires a recorded execution state")
                })?;
            let checked_source =
                search_input.lower_surface_proposition_direct(source, "`transport` source")?;
            if crate::kernel::search::ProofSearch::derive_proposition(
                search_input.facts().assumptions(),
                &checked_source,
            )
            .is_none()
            {
                return Err(search_input
                    .step_error("`transport` requires a source derivable from its ambient facts"));
            }
            let checked_target =
                search_input.lower_surface_proposition_direct(target, "`transport` target")?;
            if let Some(proof) = Self::try_ordinary_fact_transport(
                search_input,
                source,
                target,
                std::slice::from_ref(source),
            )? {
                return Ok(proof);
            }

            if let Some(name) = [source, target]
                .into_iter()
                .find_map(surface_predicate_call_name)
            {
                return Err(search_input.step_error(format!(
                    "`transport` cannot frame opaque predicate `{name}` across C execution because its memory footprint is hidden; unfold the selected application, such as `unfold({name}(args));`, before execution and transport its unfolded definition"
                )));
            }

            use crate::surface::proof_diagnostics::render;
            let _typed = render::TypedNotationScope::enter();
            let mut labels = render::MemoryStateLabels::with_state(
                view.parameter_binding,
                view.fixed_state.state,
            );
            let checked_source = render::render_proposition_labeled(&checked_source, &mut labels);
            let checked_target = render::render_proposition_labeled(&checked_target, &mut labels);
            let written_source = crate::surface::printing::source_click_proposition(source);
            let written_target = crate::surface::printing::source_click_proposition(target);
            Err(ClickError::new(format!(
                "`{}` tactic {tactic_index}: `transport` found no checked proof from its source\n  source (holds): {written_source}\n  target (wanted): {written_target}\n  checked source (holds): {checked_source}\n  checked target (wanted): {checked_target}{}\n  use `have` to state supporting facts, `preserve` across named footprints, and `rewrite` to relate the reads",
                search_input.claim_label(),
                labels.trace_legend(),
            ))
            .with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch)
            .with_report_labels(labels))
        };
        attempt().map_err(|error| {
            search_input.record_certification_failure_trace(search_input.claim_label(), 0);
            search_input.attach_step_diagnostic(error)
        })
    }

    /// Search for an ordinary proof from explicitly selected facts.
    /// Explicitly written transport reports its own refusal separately.
    pub(in crate::surface::proof) fn try_fact_transport_from_candidates(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        candidates: impl IntoIterator<Item = SyntaxProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_fact_transport_from_candidates");
        Self::fact_transport_candidate_search(search_input, source, target, candidates)
    }

    /// Construct a proof from the named candidates and the retained execution
    /// evidence. Every successful route records ordinary proof steps.
    pub(in crate::surface::proof) fn fact_transport_candidate_search(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        candidates: impl IntoIterator<Item = SyntaxProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("fact_transport_candidate_search");
        if crate::instrumentation::replay_forbids_discovery("fact transport search") {
            return Err(search_input.step_error("fact transport discovery needs explicit premises"));
        }
        check_verification_deadline()?;
        let source_fact =
            search_input.lower_surface_proposition_direct(source, "known transport source")?;
        if search_input.facts().pure_known_available(&source_fact)
            && let Some(proof) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_ordinary_transport_steps(target, vec![ProofStep::Known]),
            )?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            Self::try_recorded_footprint_preservation(search_input, source, target)?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_history_indexed_equalities(search_input, source, target)? {
            return Ok(Some(proof));
        }
        if search_input.surface_goal() == Some(target)
            && let Some(proof) = Self::try_struct_field_store_bridge(search_input, target, false)?
        {
            return Ok(Some(proof));
        }
        let mut selected = Vec::new();
        for candidate in candidates {
            check_verification_deadline()?;
            crate::instrumentation::record_deterministic_work(1);
            selected.push(candidate);
        }
        Self::try_direct_selected_fact_transport(
            search_input,
            source,
            target,
            &selected,
            &source_fact,
        )
    }
}

fn surface_predicate_call_name(proposition: &SyntaxProposition) -> Option<&str> {
    match proposition {
        SyntaxProposition::Value(_) => None,
        SyntaxProposition::PredicateCall { name, .. } => Some(name),
        SyntaxProposition::At { proposition, .. }
        | SyntaxProposition::Not(proposition)
        | SyntaxProposition::ForAll {
            body: proposition, ..
        }
        | SyntaxProposition::Exists {
            body: proposition, ..
        }
        | SyntaxProposition::RangeAll {
            body: proposition, ..
        }
        | SyntaxProposition::RangeAny {
            body: proposition, ..
        } => surface_predicate_call_name(proposition),
        SyntaxProposition::And(left, right)
        | SyntaxProposition::Or(left, right)
        | SyntaxProposition::Implies(left, right) => {
            surface_predicate_call_name(left).or_else(|| surface_predicate_call_name(right))
        }
        SyntaxProposition::Comparison { .. }
        | SyntaxProposition::FloatClassification { .. }
        | SyntaxProposition::Separate { .. }
        | SyntaxProposition::ResourceViewable { .. }
        | SyntaxProposition::Contains { .. }
        | SyntaxProposition::Loadable { .. }
        | SyntaxProposition::Defined { .. }
        | SyntaxProposition::IsA { .. } => None,
    }
}
