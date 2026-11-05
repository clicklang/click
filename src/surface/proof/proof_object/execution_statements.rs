//! Checked execution statement steps and loop-invariant bundles.

use super::*;

thread_local! {
    /// The source spelling of the bundle member the invariant-bundle planner
    /// last found open, so a refused closure names the invariant it did not
    /// prove. Diagnostic only: cleared before each closure attempt and read
    /// only on its refusal.
    static UNCLOSED_BUNDLE_MEMBER: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

fn record_unclosed_bundle_member(spelling: Option<String>) {
    if let Some(spelling) = spelling {
        UNCLOSED_BUNDLE_MEMBER.with(|member| *member.borrow_mut() = Some(spelling));
    }
}

pub(super) fn take_unclosed_bundle_member() -> Option<String> {
    UNCLOSED_BUNDLE_MEMBER.with(|member| member.borrow_mut().take())
}

pub(super) fn describe_invariant_closure_error(error: ClickError) -> ClickError {
    let member = take_unclosed_bundle_member().or_else(|| {
        // The direct structural strategy can stop before the member planner
        // runs. Its error retains the focused goal, not an enclosing bundle.
        let goal = error.diagnostic()?.kernel_goal()?;
        (!matches!(goal, Proposition::And(_, _))).then(|| {
            crate::surface::proof_diagnostics::render::render_proposition_labeled(
                goal,
                &mut crate::surface::proof_diagnostics::render::SnapshotLabels::ambient(),
            )
        })
    });
    let obligation = member
        .map(|member| format!("loop closure stopped with unresolved obligation: `{member}`"))
        .unwrap_or_else(|| "loop closure stopped without retaining an individual obligation; the failure applies to the bundle search".to_owned());
    // Concise reports read the diagnostic's reason, while legacy reports
    // read the summary. Restate both places, retaining the original goal,
    // checked state, budget attribution, and trace.
    error.with_rewritten_place(|reason| Some(format!("{obligation}: {reason}")))
}

/// Names the ranking members a ranked loop's bundle carries, so an explicit
/// `preserve by` body written before the `decreases` clause existed reports
/// what it now has to close instead of only that the bundle stayed open.
fn ranking_member_diagnostic(ranking_measures: &[crate::kernel::CRankingComponent]) -> String {
    if ranking_measures.is_empty() {
        return String::new();
    }
    let members = ranking_measures
        .iter()
        .map(|measure| {
            format!(
                "`0 <= {}` at the back edge",
                crate::kernel::c_ranking_measure_source(measure)
            )
        })
        .chain(std::iter::once(format!(
            "`{}` decreases at the back edge",
            crate::kernel::c_ranking_measures_source(ranking_measures)
        )))
        .collect::<Vec<_>>();
    format!(
        "; this loop declares `decreases`, so the bundle also has {}",
        members.join(", ")
    )
}

/// The C `if` condition standing at this frontier, spelled at that
/// statement's entry snapshot, when the case split about to happen is exactly
/// that C branch.
///
/// A proof-level case over anything else records nothing: only a decision the
/// C program itself makes is as written as the loop guard, and only a
/// condition that matches the statement at the frontier is one of those. The
/// check is one indexed source lookup and one comparison against the written
/// condition, so it reads no fact context.
fn c_branch_condition_at_frontier(
    execution: &ExecutionProofState,
    context: &ExecutionProofContext<'_>,
    condition: &ClickProposition,
) -> Result<Option<ClickProposition>, ClickError> {
    let statement_index = execution.core.frontier.next_statement_index;
    if !context
        .constants
        .source_layout
        .statement(statement_index)
        .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }))
    {
        return Ok(None);
    }
    let FrontierPosition::StatementEntry { remaining } = &execution.core.frontier.position else {
        return Ok(None);
    };
    let Ok((
        CStatement::If {
            condition: source, ..
        },
        _,
    )) = split_next_source_operation(remaining)
    else {
        return Ok(None);
    };
    if surface_c_condition(&source, &execution.core.state)? != *condition {
        return Ok(None);
    }
    Ok(Some(surface_at_snapshot(
        condition,
        &ProgramPointRef {
            region: CodeRegionRef::Region(statement_index),
            kind: ProgramPointKind::Entry,
        },
    )?))
}

impl<'a> Proof<'a> {
    /// Run the selected operation while retaining its unresolved obligations.
    /// The candidate is conditional until the driver proves those obligations
    /// at this original frontier and calls `finish_prepared_step`.
    pub(in crate::surface::proof) fn prepare_step(
        &self,
        step: &ProofStep,
    ) -> (
        Result<Self, ClickError>,
        crate::surface::proof::execution_planning::OpenObligationProbe,
    ) {
        probe_open_obligations(|| self.apply_fast_simple_step(step))
    }

    /// Refuses an exhausted script at its actual frontier. A disposable
    /// descendant checks at most six straight-line operations, enough for
    /// the next two callback statements, solely to name a concrete missing
    /// view or contract. It never completes or publishes the source proof.
    pub(in crate::surface::proof) fn unfinished_callback_diagnostic(
        &self,
    ) -> Result<Option<ClickError>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let sources = context.parsed_function.callback_statement_sources();
        if sources.is_empty() {
            return Ok(None);
        }
        let unfinished = "the proof stops before function exit; finish the remaining C operations with `step()` or `step_until(function.exit)`, or end the script so its implicit tail runs them";
        let mut pending = self.clone();
        for _ in 0..6 {
            check_verification_deadline()?;
            let Some(execution) = pending.execution() else {
                break;
            };
            let remaining = match &execution.core.frontier.position {
                FrontierPosition::FunctionEntry => context.function.body(),
                FrontierPosition::StatementEntry { remaining } => remaining.as_ref(),
                _ => break,
            };
            let Ok((statement, _)) = split_next_source_operation(remaining) else {
                break;
            };
            let carrier = match &statement {
                CStatement::Declare { name, .. } | CStatement::Assign { name, .. } => Some(name),
                CStatement::Call { function_name, .. }
                | CStatement::CallAssign { function_name, .. } => Some(function_name),
                _ => break,
            };
            let is_callback = carrier.is_some_and(|name| sources.contains_key(name));
            match pending.driver().apply_step(ProofStep::Step) {
                Ok(next) => pending = next,
                Err(error) => {
                    check_verification_deadline()?;
                    if error.kind() != ClickErrorKind::Proof {
                        return Err(error);
                    }
                    if is_callback {
                        let prefix = "the proof stops before this callback; continuing its checked operations would fail";
                        let mut error = error.with_context(prefix);
                        if let Some(diagnostic) = &mut error.diagnostic {
                            let diagnostic = std::sync::Arc::make_mut(diagnostic);
                            diagnostic.reason = diagnostics::bound_error_message(format!(
                                "{prefix}: {}",
                                diagnostic.reason
                            ));
                        }
                        return Ok(Some(error));
                    }
                    break;
                }
            }
        }
        Ok(Some(self.step_error(unfinished)))
    }

    /// Closes the back-edge bundle as `close_invariants() by { ... }` with
    /// `solve()` on each member. The bundle conjoins its members, balanced for
    /// wide bundles, and each member may open with a spine of guards from
    /// earlier declarations; that fixed structure is descended by checked
    /// `both` and `intro` steps, and every member below it is closed by
    /// `solve()` and nothing else. Every step advances this same `Proof`, so
    /// the retained certificate is the explicit proof `click expand` prints
    /// and re-verifies.
    pub(in crate::surface::proof) fn plan_invariant_bundle_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let result = self.driver().plan_invariant_bundle_member_closure();
        // A search refusal must retain the member it was checking, too. Keep
        // the innermost member: enclosing implication/quantifier scopes must
        // not replace it with the entire guarded bundle.
        if result.is_err() && !matches!(self.goal(), Some(Proposition::And(_, _))) {
            UNCLOSED_BUNDLE_MEMBER.with(|member| {
                if member.borrow().is_none() {
                    *member.borrow_mut() = self.bundle_member_spelling();
                }
            });
        }
        let result = result?;
        // A conjunction passes its open child's record up unchanged; any
        // other member that stays open is the one a refusal names, replacing
        // whatever leaf inside it was recorded first.
        if result.is_none() && !matches!(self.goal(), Some(Proposition::And(_, _))) {
            record_unclosed_bundle_member(self.bundle_member_spelling());
        }
        Ok(result)
    }

    /// One bundle member, closed by `solve()` as the member is spelled: a
    /// declared invariant as written, read at the back edge, and a ranking
    /// member as its `decreases` clause writes it
    /// ([`ranking_descent_surface`]), as a function's exit closes each
    /// `ensures` as written.
    fn close_bundle_member_by_solve(&self) -> Result<Option<Self>, ClickError> {
        crate::kernel::search::ProofSearch::try_solve_closure(
            &(self.with_synthesized_bundle_member_surface()),
        )
    }

    /// Restores presentation metadata for one generated bundle leaf from the
    /// two program points the loop rule itself owns. The candidate must lower
    /// alpha-equivalently to the focused kernel goal; attaching it changes no
    /// facts, proof topology, or checked proposition.
    /// The focused bundle member as a refusal names it: its source spelling,
    /// else the lowered member spelled over the back-edge locals.
    pub(super) fn bundle_member_spelling(&self) -> Option<String> {
        let presented = self.with_synthesized_bundle_member_surface();
        if let Some(surface) = presented.surface_goal() {
            let spelled = crate::surface::printing::source_click_proposition(surface);
            if !spelled.contains("__click_") {
                return Some(spelled);
            }
        }
        let goal = self.goal()?;
        let (parameters, arguments) = self.diagnostic_naming_tables();
        let mut labels = crate::surface::proof_diagnostics::render::SnapshotLabels::naming(
            ParameterBinding::new(&parameters, &arguments),
        );
        // A value the back-edge locals no longer hold, such as the
        // iteration's entry value of a counter, reads at the snapshot that
        // recorded it.
        if let Some(execution) = self.execution() {
            super::register_recorded_snapshot_names(
                &mut labels,
                &execution.presentation.recorded_snapshots,
            );
        }
        // The pass's own count, `iterations`.
        if let Some(crate::kernel::IntegerTerm::Variable(variable)) = self
            .execution_context()
            .and_then(|context| context.constants.invariant_body_context.as_deref())
            .and_then(|bundle| bundle.iterations.as_ref())
        {
            labels.integer_source_name(*variable, crate::surface::LOOP_ITERATIONS_NAME.to_string());
        }
        let mut lowered = crate::surface::proof_diagnostics::render::render_proposition_labeled(
            goal,
            &mut labels,
        );
        lowered.push_str(&labels.trace_legend());
        // The back-edge locals do not name a value read at an earlier
        // snapshot, which the lowered spelling elides. The synthesized form
        // names that snapshot even where it does not lower back exactly, as
        // an unsigned order does not.
        if lowered.contains('…')
            && let Some(surface) = self.bundle_member_surface(goal, false)
        {
            let spelled = crate::surface::printing::refusal_click_proposition(&surface);
            if !spelled.contains("__click_") && !spelled.contains('…') {
                return Some(spelled);
            }
        }
        Some(lowered)
    }

    fn with_synthesized_bundle_member_surface(&self) -> Self {
        if self.surface_goal().is_some() {
            return self.clone();
        }
        let Some(goal) = self.goal() else {
            return self.clone();
        };
        let surface = self.synthesized_bundle_member_surface(goal);
        let Some(surface) = surface else {
            return self.clone();
        };
        let Some(state) = self
            .state
            .with_focused_proposition_presentation(|presentation| PropositionPresentation {
                surface: Some(Arc::new(surface)),
                ..presentation.clone()
            })
        else {
            return self.clone();
        };
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }
    }

    /// The back-edge bundle's members as the loop head writes them, split
    /// at conjunctions as the bundle's leaves are: each declared invariant
    /// guarded by the invariants declared before it, and bare, as the member
    /// reads once the closer has introduced those guards; one `0 <= m` per
    /// `decreases` component, then the descent member
    /// ([`ranking_descent_surface`]). None outside a loop preservation proof.
    pub(in crate::surface::proof) fn written_bundle_member_surfaces(
        &self,
    ) -> Option<Vec<ClickProposition>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let bundle = context.constants.invariant_body_context.as_deref()?;
        let mut members = Vec::new();
        let declared = &bundle.declared_invariant_surfaces;
        for (index, invariant) in declared.iter().enumerate() {
            let guarded = declared[..index]
                .iter()
                .rev()
                .fold(invariant.clone(), |body, guard| {
                    ClickProposition::Implies(Box::new(guard.clone()), Box::new(body))
                });
            // A member whose guards the closer has already introduced is the
            // invariant itself.
            let mut pending = if index == 0 {
                vec![guarded]
            } else {
                vec![invariant.clone(), guarded]
            };
            while let Some(member) = pending.pop() {
                if let ClickProposition::And(left, right) = member {
                    pending.push(*right);
                    pending.push(*left);
                } else {
                    members.push(member);
                }
            }
        }
        if bundle.ranking_surfaces.len() == bundle.ranking_measures.len() {
            for component in &bundle.ranking_surfaces {
                members.push(ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral("0".to_string()),
                    operator: ComparisonOperator::LessEqual,
                    right: component.clone(),
                });
            }
            members.extend(ranking_descent_surface(bundle));
        }
        Some(members)
    }

    /// One bundle member's source form, synthesized at the current state
    /// with the iteration entry, and failing that the loop entry, as the one
    /// further snapshot, and kept only when it lowers alpha-equivalently to
    /// `goal`. A member at the loop entry has no source form in the whole
    /// bundle's synthesis, which names only the iteration entry, so a
    /// written `both` over a bundle reaches its members through this too.
    pub(in crate::surface::proof) fn synthesized_bundle_member_surface(
        &self,
        goal: &Proposition,
    ) -> Option<ClickProposition> {
        self.bundle_member_surface(goal, true)
    }

    /// [`Self::synthesized_bundle_member_surface`], or with `checked` false
    /// the synthesized form whether or not it lowers back to `goal`. Only a
    /// refusal reads the unchecked form, to name the snapshots a member
    /// compares; nothing proves or records it.
    fn bundle_member_surface(&self, goal: &Proposition, checked: bool) -> Option<ClickProposition> {
        let context = self.execution_context()?;
        let execution = self.execution()?;
        let bundle = context.constants.invariant_body_context.as_deref()?;
        let synthesize_at = |state: &CState, selector: &SnapshotSelector| {
            let synthesize = || {
                crate::surface::proof::surface_synthesis::synthesize_surface_proposition_at_entry_post_and_snapshot(
                    goal,
                    context.parameter_binding(),
                    context.old_reference_state(&execution.core.frontier, &execution.core.state),
                    &execution.core.state,
                    Some((state, selector)),
                )
            };
            let accepted = |surface: &ClickProposition| {
                !checked
                    || self
                        .lower_surface_goal(surface, "loop invariant bundle member")
                        .ok()
                        .is_some_and(|lowered| {
                            crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal)
                        })
            };
            if bundle.binder_names.is_empty() {
                return synthesize().filter(accepted);
            }
            // A binder takes the name its invariant wrote. The generated name
            // remains the fallback, tried only when the written spelling came
            // out different and does not lower back to this member.
            let written = crate::surface::proof::surface_synthesis::with_synthesis_binder_names(
                &bundle.binder_names,
                synthesize,
            )?;
            if accepted(&written) {
                return Some(written);
            }
            synthesize().filter(|generated| generated != &written && accepted(generated))
        };
        bundle
            .iteration_entry_selector
            .as_ref()
            .and_then(|selector| synthesize_at(&bundle.iteration_entry_state, selector))
            .or_else(|| {
                bundle
                    .loop_entry_selector
                    .as_ref()
                    .and_then(|selector| synthesize_at(&bundle.loop_entry_state, selector))
            })
            .or_else(|| {
                let written = ranking_descent_surface(bundle)?;
                (!checked
                    || self
                        .lower_surface_goal(&written, "loop invariant bundle member")
                        .ok()
                        .is_some_and(|lowered| {
                            crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal)
                        }))
                .then_some(written)
            })
    }

    /// The scalar local assigned by the statement at the current frontier.
    /// Plain `step()` bindings accept assignments; call bindings retain the
    /// explicit callee and binder-map path.
    ///
    /// A call whose result is used in a condition or a return expression is
    /// lowered as an assignment to one synthesized local, so naming that
    /// local's post-call value is what gives a proof a surface name for the
    /// result. A call in statement position discards its result and has no
    /// such local; naming it is an error rather than a silent no-op.
    fn frontier_result_local(&self, name: &String, assignment: bool) -> Result<String, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // The result hides an earlier proof-local value of its name, as any
        // proof binder does; a C variable of that name stays the program's.
        if execution.core.state.locals().contains_name(name)
            || context.constants.source_layout.has_parameter_name(name)
        {
            return Err(self.step_error(format!(
                "`{name}` names a C variable here; a proof binder cannot hide it, since execution keeps reading the program's `{name}`; choose another name"
            )));
        }
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "step",
        )?;
        match statement {
            CStatement::Assign { name, .. } if assignment => Ok(name),
            CStatement::CallAssign { target, .. } if !assignment => Ok(target),
            _ if assignment => Err(self.step_error(format!(
                "`let {{ result: {name} }} = step()` requires a scalar assignment at the frontier"
            ))),
            _ => Err(self.step_error(format!(
                "`let {{ result: {name} }} = step(...)` names a call result, but this call's result is unused"
            ))),
        }
    }

    /// `expression` evaluated at the frontier's state, as a call step's map
    /// value or the argument of the call it runs is: once, through the
    /// kernel.
    fn evaluate_at_frontier(
        &self,
        context: &ExecutionProofContext<'_>,
        expression: &ContractExpression,
        what: &str,
    ) -> Result<CValue, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error(format!("{what} needs an execution state")))?;
        let state = &*execution.core.state;
        let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
        let pre_state = context.old_reference_state(&execution.core.frontier, state);
        let values = parameter_values(context.parameter_binding())?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            state.memory(),
        );
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
        evaluate_fixed_state_expression_through_kernel(
            &expression,
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &array_refs),
            FixedStateFrame::new(
                pre_state,
                state,
                None,
                &execution.presentation.recorded_snapshots,
            ),
            context.spec_definitions,
            &BTreeSet::new(),
        )
        .map_err(|message| self.step_error(format!("{what}: {message}")))
    }

    pub(in crate::surface::proof) fn apply_execution_statement_step_with_policy(
        &self,
        step: ProofStep,
        prerequisite_policy: StatementPrerequisitePolicy,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        let addressed_context = self
            .site
            .tactic_index()
            // Loop phase drivers already attribute their own local script.
            // The enclosing proof site still names the outer loop tactic.
            .filter(|_| context.constants.invariant_body_context.is_none())
            .map(|index| context.with_tactic_index(index));
        let context = addressed_context.as_ref().unwrap_or(context);
        // `step(callee, { ... })` runs the call at the frontier, which must
        // call `callee`; its arguments are that call's.
        let frontier_call = match &step {
            ProofStep::StepCall(transport) if transport.is_frontier() => {
                Some(self.frontier_call_for_named_function(context, transport)?)
            }
            _ => None,
        };
        // Resolve this statement's result local before checking the step.
        // Only its checked successor value is bound below. The assignment
        // or call is exactly the current frontier; nothing is searched.
        let result_target = match &step {
            ProofStep::StepBind(name) => {
                Some((name.clone(), self.frontier_result_local(name, true)?))
            }
            ProofStep::StepCall(transport) => match transport.result() {
                Some(name) => {
                    let name = name.to_string();
                    let target = self.frontier_result_local(&name, false)?;
                    Some((name, target))
                }
                None => None,
            },
            _ => None,
        };
        let selected_environment;
        let selected_context;
        let context = if let ProofStep::StepContract(application) = &step {
            let name = &application.name;
            if context
                .function_environment
                .get_function_contract(name)
                .is_none()
            {
                return Err(self.step_error(format!("unknown call contract `{name}`")));
            }
            let definition = context
                .spec_definitions
                .predicates
                .contract_definition(name)
                .ok_or_else(|| self.step_error(format!("unknown call contract `{name}`")))?;
            let parameters = definition.proof_parameters.as_deref().unwrap_or(&[]);
            let handle_names = || {
                parameters
                    .iter()
                    .map(|parameter| match parameter {
                        ResourceClause::Named { binding, .. } => format!("`{}`", binding.name),
                        _ => unreachable!(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            // Entries name the contract's handles; each handle takes exactly
            // one entry, matched by name in one lookup per entry.
            let mut by_handle = BTreeMap::new();
            for argument in &application.arguments {
                crate::instrumentation::record_deterministic_work(1);
                if !parameters.iter().any(|parameter| {
                    matches!(parameter, ResourceClause::Named { binding, .. }
                        if binding.name == argument.handle)
                }) {
                    return Err(self.step_error(if parameters.is_empty() {
                        format!(
                            "contract `{name}` declares no resource handles; write `step({name})`"
                        )
                    } else {
                        format!(
                            "contract `{name}` has no resource handle `{}`; its handles are {}",
                            argument.handle,
                            handle_names()
                        )
                    }));
                }
                if by_handle
                    .insert(argument.handle.as_str(), argument)
                    .is_some()
                {
                    return Err(self.step_error(format!(
                        "contract `{name}` handle `{}` is bound twice",
                        argument.handle
                    )));
                }
            }
            let mut arguments = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let ResourceClause::Named { binding, .. } = parameter else {
                    unreachable!()
                };
                let Some(argument) = by_handle.get(binding.name.as_str()) else {
                    // A `produces` handle is introduced by the `let` pattern,
                    // not supplied in the map.
                    let produced = definition
                        .function_block()
                        .ensures()
                        .iter()
                        .filter(|ensure| !ensure.borrowed())
                        .filter_map(|ensure| match ensure.ensure() {
                            Ensure::Resource(ResourceClause::Named { binding, .. }) => {
                                Some(binding.name.clone())
                            }
                            _ => None,
                        })
                        .collect::<BTreeSet<_>>();
                    let entries = |produced_side: bool| {
                        parameters
                            .iter()
                            .filter_map(|parameter| match parameter {
                                ResourceClause::Named { binding, .. }
                                    if produced.contains(&binding.name) == produced_side =>
                                {
                                    Some(format!("{}: ...", binding.name))
                                }
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    let spelling = if produced.is_empty() {
                        format!("step({name}, {{ {} }})", entries(false))
                    } else {
                        format!(
                            "let {{ {} }} = step({name}, {{ {} }})",
                            entries(true),
                            entries(false)
                        )
                    };
                    return Err(self.step_error(format!(
                        "contract `{name}` declares resource handles; write `{spelling}` with one instance for each of {}",
                        handle_names()
                    )));
                };
                arguments.push(*argument);
            }
            let mut identities = BTreeSet::new();
            for (parameter, argument) in parameters.iter().zip(&arguments) {
                let ResourceClause::Named { binding, resource } = parameter else {
                    unreachable!()
                };
                let ResourceClause::Declared { name: expected, .. } = resource.as_ref() else {
                    unreachable!()
                };
                if argument.resource_name != *expected {
                    return Err(self.step_error(format!(
                        "contract `{name}` handle `{}` expects resource `{expected}`, got `{}`",
                        binding.name, argument.resource_name
                    )));
                }
                if !identities.insert(argument.identity) {
                    return Err(self.step_error(
                        "an exclusive instance cannot supply two contract resource handles",
                    ));
                }
            }
            selected_environment = context
                .function_environment
                .clone()
                .with_selected_call_contract(name)
                .with_selected_call_resource_arguments(
                    arguments.iter().map(|argument| argument.identity).collect(),
                );
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else if let ProofStep::StepCall(transport) = &step {
            let callee = transport.callee();
            // One lookup per written entry builds the whole binding; the
            // kernel consults nothing else at this call.
            let mut bindings = BTreeMap::new();
            for binding in transport.binders().iter().chain(transport.produced()) {
                crate::instrumentation::record_deterministic_work(1);
                if bindings
                    .insert(binding.binder_identity(), binding.identity())
                    .is_some()
                {
                    return Err(self.step_error(format!(
                        "duplicate binder `{}` in the call map",
                        binding.binder()
                    )));
                }
            }
            // A runtime type binder names the resource type as the call's
            // state reads it.
            let mut type_arguments = BTreeMap::new();
            for (_, identity, resource) in transport.type_arguments() {
                let ResourceClause::Declared { name, .. } = resource else {
                    return Err(self.step_error("a type binder names a declared resource type"));
                };
                let state = &*self
                    .execution()
                    .ok_or_else(|| self.step_error("a type binder needs an execution state"))?
                    .core
                    .state;
                let fact = crate::surface::lowering::lower_resource_clause_at_state(
                    resource,
                    context.parameter_binding(),
                    state,
                )?;
                let crate::kernel::CResource::Composite { arguments, .. } = fact.resource() else {
                    return Err(self.step_error(format!(
                        "type binder `{name}` must name a resource with a body"
                    )));
                };
                let schema = context
                    .resource_environment
                    .get(name)
                    .and_then(|definition| definition.field_schema().cloned())
                    .or_else(|| crate::kernel::ResourceFieldSchema::new(Vec::new()))
                    .ok_or_else(|| self.step_error("resource type has no field schema"))?;
                type_arguments.insert(
                    *identity,
                    crate::kernel::ResourceDescription::new(
                        name.clone(),
                        arguments.clone(),
                        schema,
                    ),
                );
            }
            // Each entry gives a callee's `let` value parameter its value,
            // evaluated at the call's state; the kernel still requires the
            // parameter's clauses at it.
            let mut selected_values = Vec::new();
            for (parameter, expression) in transport.value_arguments() {
                crate::instrumentation::record_deterministic_work(1);
                let value = self.evaluate_at_frontier(
                    context,
                    expression,
                    &format!("call map value `{parameter}`"),
                )?;
                selected_values.push((parameter.clone(), value));
            }
            let mut environment = context.function_environment.clone();
            if !selected_values.is_empty() {
                let function = frontier_call
                    .as_ref()
                    .map_or(callee, |call| call.callee.as_str());
                environment = environment.with_selected_call_values(function, selected_values);
            }
            let arity = if let Some(call) = &frontier_call {
                call.arguments.len()
            } else if transport.is_named_contract() {
                let definition = context
                    .spec_definitions
                    .predicates
                    .contract_definition(callee)
                    .ok_or_else(|| self.step_error(format!("unknown call contract `{callee}`")))?;
                environment = environment.with_selected_call_contract(callee);
                definition.function_block().signature().parameters().len()
            } else {
                transport.arguments().len()
            };
            let execution_callee = if let Some(call) = &frontier_call {
                call.callee.as_str()
            } else if transport.is_named_contract() {
                callee
            } else {
                context
                    .spec_definitions
                    .predicates
                    .function_execution_name(callee)
            };
            selected_environment = environment.with_selected_call_binders_and_types(
                execution_callee,
                arity,
                bindings,
                type_arguments,
            );
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else {
            context
        };
        self.require_execution_frontier("`step`")?;
        // A produced instance of `step(callee, { ... })` reads its resource
        // arguments as `name.parameter`: each is the frontier call's argument,
        // evaluated before the call runs, bound below as the result is.
        let mut produced_arguments = Vec::new();
        if let (ProofStep::StepCall(transport), Some(call)) = (&step, &frontier_call) {
            for produced in transport.produced() {
                for (name, argument) in produced.call_arguments().iter().zip(&call.arguments) {
                    crate::instrumentation::record_deterministic_work(1);
                    let value = self.evaluate_at_frontier(
                        context,
                        &ContractExpression::CFragment(argument.clone()),
                        &format!("call argument `{name}`"),
                    )?;
                    produced_arguments.push((
                        name.clone(),
                        ContractExpression::CFragment(CExpression::Value(value)),
                    ));
                }
            }
        }
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // Every statement step executes in the whole proof context.
        let fact_context = Some(self.facts().assumptions());
        let mut checked = check_statement_step_with_policy(
            &mut execution,
            context,
            self.facts(),
            fact_context,
            prerequisite_policy,
        )?;
        // A fact the statement introduces (a callee's `ensures`, a store's
        // value) is recorded under its readable spelling at the successor
        // state, so a later premise can name it without re-lowering it against
        // another memory. Output-sized work: one synthesis per introduced
        // fact.
        for fact in &checked.added_facts {
            if let Some(surface) = synthesize_surface_proposition(
                fact,
                context.parameter_binding(),
                &checked.execution.core.state,
            ) {
                // At a call successor, a synthesized `old(...)` names the
                // callee's entry snapshot, while the same surface syntax in
                // the caller names the caller's function entry. Do not cache
                // that ambiguous spelling as caller provenance. Explicit
                // Snapshot-qualified forms (including proof marks) retain the exact
                // call-frontier identity needed to name such a fact later.
                if proposition_contains_old_expression(&surface) {
                    continue;
                }
                let _ = checked
                    .execution
                    .presentation
                    .surface_propositions
                    .record_lowering(&surface, fact);
            }
        }
        // The result is the value the checked statement left in its local:
        // one indexed read of that name,
        // bound as the proof-local value the surface name denotes from here on.
        let result_binding = match &result_target {
            Some((name, target)) => {
                let value = checked
                    .execution
                    .core
                    .state
                    .locals()
                    .get(target)
                    .cloned()
                    .ok_or_else(|| {
                        self.step_error(format!(
                            "`let {{ result: {name} }} = step(...)` found no assignment result"
                        ))
                    })?;
                Some((
                    name.clone(),
                    ContractExpression::CFragment(CExpression::Value(value)),
                ))
            }
            None => None,
        };
        let added_facts = checked.added_facts;
        let state = self
            .state
            .publish_checked_frontier_transition(
                checked.facts,
                checked.execution,
                added_facts.clone(),
                added_facts,
            )
            .map_err(|error| self.execution_update_error("`step`", error))?;
        let state = if result_binding.is_none() && produced_arguments.is_empty() {
            state
        } else {
            let mut locals = state.locals().clone();
            for (name, value) in result_binding.into_iter().chain(produced_arguments) {
                locals.values = locals.values.with_inserted(name, value);
            }
            state.with_locals(locals)
        };
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(&self.node, self.focused_branch_id(), Arc::new(step)),
        })
    }

    /// `name(args, { binder: instance })`: one application of a user-defined
    /// tactic at the execution frontier.
    ///
    /// The tactic's verified rule is applied by the kernel with no C
    /// statement; the binder map is the whole binding, exactly as for a call
    /// step, and every argument is lowered at the frontier as a fold field
    /// is. Every precondition must already be an available fact.
    pub(in crate::surface::proof) fn apply_execution_user_tactic(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        let ProofStep::UserTactic(application) = &step else {
            unreachable!("only a tactic application reaches this step")
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "a tactic is applied in a C function or tactic proof in this release",
            ));
        };
        self.require_execution_frontier("a tactic application")?;
        let callee = application.callee();
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let parameters = context
            .function_environment
            .get_function(callee)
            .ok_or_else(|| self.step_error(format!("unknown tactic `{callee}`")))?
            .parameters()
            .to_vec();
        if parameters.len() != application.arguments().len() {
            return Err(self.step_error(format!(
                "tactic `{callee}` expects {} argument(s), got {}",
                parameters.len(),
                application.arguments().len()
            )));
        }
        let mut bindings = BTreeMap::new();
        for binding in application.binders().iter().chain(application.produced()) {
            crate::instrumentation::record_deterministic_work(1);
            if bindings
                .insert(binding.binder_identity(), binding.identity())
                .is_some()
            {
                return Err(self.step_error(format!(
                    "duplicate binder `{}` in the tactic's map",
                    binding.binder()
                )));
            }
        }
        let environment = context
            .function_environment
            .clone()
            .with_selected_call_binders(callee, parameters.len(), bindings);
        let before = &*execution.core.state;
        let pre_state = context.old_reference_state(&execution.core.frontier, before);
        let values = parameter_values(context.parameter_binding())?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            before.memory(),
        );
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, before);
        let mut arguments = Vec::with_capacity(parameters.len());
        for (parameter, argument) in parameters.iter().zip(application.arguments()) {
            let argument = self.substitute_fixed_state_locals_in_expression(argument)?;
            // As at resource and pure-function parameters, the literal `0`
            // denotes a typed null pointer here. Do not coerce arbitrary
            // integer expressions, even when their evaluated value is zero.
            if parameter.c_type().is_pointer()
                && matches!(&argument, ContractExpression::IntegerLiteral(text) if text == "0")
            {
                arguments.push(CValue::typed_pointer(
                    crate::kernel::Pointer::null(),
                    parameter.c_type(),
                ));
                continue;
            }
            let value = capture_resource_field_initializer(
                &argument,
                &crate::kernel::ResourceFieldType::C(parameter.c_type()),
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs),
                pre_state,
                before,
                &execution.presentation.recorded_snapshots,
                context.spec_definitions,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "tactic `{callee}` argument `{}`: {message}",
                    parameter.name()
                ))
            })?;
            let crate::kernel::AlgebraicValue::C(value) = value else {
                unreachable!("a C parameter captures a C value")
            };
            arguments.push(value);
        }
        let before_state = (*execution.core.state).clone();
        let context_parameters = context.parsed_function.parameters();
        let context_arguments = context.arguments;
        let (state, facts) = execution
            .core
            .record_tactic_application(
                context.function,
                context.arguments,
                self.facts(),
                callee,
                &arguments,
                &environment,
            )
            .map_err(|refusal| match refusal {
                crate::kernel::TacticApplicationRefusal::MissingRequirement(
                    requirement,
                    context,
                ) => {
                    let spelling = synthesize_surface_proposition(
                        &requirement,
                        ParameterBinding::new(context_parameters, context_arguments),
                        &before_state,
                    )
                    .map(|proposition| {
                        crate::surface::diagnostics::describe_click_proposition(&proposition)
                    })
                    .unwrap_or_else(|| {
                        crate::surface::proof_diagnostics::render::render_proposition(&requirement)
                    });
                    let owed = context.map_or_else(String::new, |context| format!(" ({context})"));
                    self.step_error(format!(
                        "tactic `{callee}` requires `{spelling}`{owed}, which is not an available \
                         fact here; establish it first, for example with `have`"
                    ))
                }
                crate::kernel::TacticApplicationRefusal::Refused(message) => {
                    self.step_error(message)
                }
            })?;
        execution.core.state = state.into();
        let added_facts = facts.introduced_since(self.facts()).unwrap_or_default();
        let state = self
            .state
            .publish_checked_frontier_transition(facts, execution, added_facts.clone(), added_facts)
            .map_err(|error| self.execution_update_error("a tactic application", error))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(&self.node, self.focused_branch_id(), Arc::new(step)),
        })
    }

    /// The call at the frontier that `step(callee, { ... })` runs, once it is
    /// shown to call `callee` and each value entry to name one of the
    /// callee's `let` value parameters: one statement read, then one pass
    /// over those parameters per entry. `snprintf` names the formatted-output
    /// function of whatever format the call passes.
    fn frontier_call_for_named_function(
        &self,
        context: &ExecutionProofContext<'_>,
        transport: &CallBinderTransport,
    ) -> Result<FrontierCall, ClickError> {
        let written = transport.callee();
        let remaining =
            self.execution()
                .and_then(|execution| match &execution.core.frontier.position {
                    FrontierPosition::FunctionEntry => Some(context.function.body()),
                    FrontierPosition::StatementEntry { remaining } => Some(remaining.as_ref()),
                    _ => None,
                });
        // C++ cleanup wrappers do not introduce an executable step. Select
        // the same first operation that ordinary `step()` will execute, while
        // leaving the wrapper intact for the kernel's exception continuation.
        // Borrow only the leading source path. Splitting/cloning each try
        // wrapper here would also copy its unrelated cleanup handler.
        let mut operation = remaining;
        loop {
            operation = match operation {
                Some(CStatement::Seq(statements)) => Some(statements.first()),
                Some(CStatement::TryCatchInt32 { try_body, .. }) => Some(try_body.as_ref()),
                _ => break,
            };
            crate::instrumentation::record_deterministic_work(1);
        }
        let call = operation.and_then(|statement| match statement {
            CStatement::Call {
                function_name,
                arguments,
            }
            | CStatement::CallAssign {
                function_name,
                arguments,
                ..
            } => Some(FrontierCall {
                callee: function_name.clone(),
                arguments: arguments.clone(),
            }),
            _ => None,
        });
        let names_written = |callee: &str| {
            callee == written
                || crate::surface::call_source_spelling(callee) == written
                || context
                    .spec_definitions
                    .predicates
                    .function_execution_name(written)
                    == callee
                || (written == "snprintf"
                    && crate::languages::c::formatted_output::describe_function(callee).is_some())
        };
        let Some(call) = call.filter(|call| names_written(&call.callee)) else {
            return Err(self.step_error(format!(
                "`{transport}` requires a call to `{written}` at the current frontier"
            )));
        };
        if transport.value_arguments().is_empty() {
            return Ok(call);
        }
        let named = || {
            crate::languages::c::formatted_output::describe_function(&call.callee)
                .unwrap_or_else(|| format!("`{written}`"))
        };
        let Some(function) = context.function_environment.get_function(&call.callee) else {
            return Err(self.step_error(format!(
                "`{transport}` gives values to {}, which has no Click contract",
                named()
            )));
        };
        let parameters = function.contract_interface().value_parameters();
        for (name, _) in transport.value_arguments() {
            crate::instrumentation::record_deterministic_work(1);
            if !parameters.iter().any(|parameter| parameter.name() == name) {
                return Err(
                    self.step_error(format!("{} declares no value parameter `{name}`", named()))
                );
            }
        }
        Ok(call)
    }

    pub(super) fn apply_execution_mark(&self, name: &str) -> Result<KernelProofHandle, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut presentation = execution.presentation.clone();
        let selector = SnapshotSelector::Mark(name.to_string());
        if presentation.recorded_snapshots.contains_key(&selector) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        presentation
            .recorded_snapshots
            .insert(selector, (*execution.core.state).clone());
        self.state
            .replace_frontier_presentation(presentation)
            .map_err(|error| self.execution_update_error("`mark`", error))
    }

    /// Publish a completed conditional statement after its caller has proved
    /// every recorded obligation at this original frontier. The candidate must
    /// never be used as the context for those proofs. A failed preparation (for
    /// example pending loan recovery) has no successor and still needs retry.
    fn finish_prepared_step(
        &self,
        prepared: Result<Self, ClickError>,
        proved: &Self,
        step: &ProofStep,
    ) -> Result<Self, ClickError> {
        // Folds also use obligation probing, but have their own resource-scope
        // publication rather than a statement frontier.
        if matches!(step, ProofStep::FoldResource(_)) {
            return proved.apply_fast_simple_step(step);
        }
        let mut candidate = match prepared {
            Ok(candidate) => candidate,
            Err(_) => return proved.apply_fast_simple_step(step),
        };
        let introduced = proved
            .facts()
            .introduced_since(self.facts())
            .expect("obligation proofs extend their original fact context");
        let mut facts = candidate.facts().clone();
        for fact in &introduced {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        let original = self
            .execution()
            .expect("statement preparation has a frontier");
        let proven = proved
            .execution()
            .expect("obligation proofs retain the frontier");
        let mut execution = candidate
            .execution()
            .expect("prepared statement has a successor")
            .clone();
        // `have` publication keeps its source spelling and certificate facts
        // beside the logical context. Carry only the appended suffix, preserving
        // the candidate's new call bindings, snapshots, and typed read evidence.
        let retained = proven
            .presentation
            .surface_record
            .retained_have_facts
            .introduced_since(&original.presentation.surface_record.retained_have_facts)
            .expect("obligation proofs append retained facts");
        for fact in retained {
            execution
                .presentation
                .surface_propositions
                .record_lowering(
                    proven.presentation.surface_propositions.surface(&fact)?,
                    &fact,
                )?;
            execution.presentation.surface_record.retained_have_facts = execution
                .presentation
                .surface_record
                .retained_have_facts
                .with_kernel_checked_fact(fact);
        }
        // A completing statement also saved its conditional obligations in
        // the function outcome. Publish the proved input delta on those new
        // outcomes so contract certification sees the evidence too. Earlier
        // loop returns belong to their own paths, not this frontier.
        if let Some(completed) = execution.core.frontier.execution() {
            let additional = introduced
                .iter()
                .cloned()
                .map(ExecutionPureFact::new)
                .collect::<crate::kernel::ExecutionFacts>();
            let paths = completed
                .paths()
                .iter()
                .enumerate()
                .map(|(index, path)| {
                    if execution
                        .provenance_for_outcome(index)
                        .loop_return
                        .is_some()
                    {
                        path.clone()
                    } else {
                        crate::kernel::c_function_execution_candidate_with_additional_facts(
                            path,
                            &additional,
                        )
                    }
                })
                .collect();
            let completed = crate::kernel::c_function_execution_candidates_from_retained_paths(
                completed.state().clone(),
                completed.function().clone(),
                completed.arguments().to_vec(),
                paths,
            );
            if let Some(leaf) = &mut execution.presentation.checked_leaf_facts {
                Arc::make_mut(leaf).0 = completed
                    .candidate_at(0)
                    .expect("one checked outcome")
                    .clone();
            }
            execution.core.frontier.position = FrontierPosition::FunctionExit {
                execution: completed,
            };
        }
        // A terminal statement has already captured its facts for contract
        // certification. Extend that retained context by the checked input
        // delta too; otherwise it still describes the conditional probe.
        if let Some(leaf) = &mut execution.presentation.checked_leaf_facts {
            let (_, leaf_facts, _) = Arc::make_mut(leaf);
            for fact in &introduced {
                *leaf_facts = leaf_facts.with_kernel_checked_fact(fact.clone());
            }
        }
        let state = candidate
            .state
            .publish_checked_frontier_transition(
                facts,
                execution,
                candidate.state().added_facts().to_vec(),
                candidate.state().checked_facts().to_vec(),
            )
            .map_err(|error| self.execution_update_error("prepared step", error))?;
        candidate.state = state;
        Ok(candidate)
    }

    /// A simple tactic's fast path: a statement step under the `Fast`
    /// policy, or a `fold`, whose body checks are exact. Either refuses an
    /// obligation it cannot close exactly, or records it while probed.
    fn apply_fast_simple_step(&self, step: &ProofStep) -> Result<Self, ClickError> {
        match step {
            ProofStep::FoldResource(_) => {
                without_implicit_solve(|| self.driver().apply_step(step.clone()))
            }
            _ => self.apply_execution_statement_step_with_policy(
                step.clone(),
                StatementPrerequisitePolicy::Fast,
            ),
        }
    }

    /// Every requirement's Surface spelling must lower back to that
    /// requirement, so that the expanded `requires` entry matches it.
    fn debug_assert_spelling_relowers(
        &self,
        requirement: &UnresolvedRequirement,
        surface: &ClickProposition,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        let lowered = self.lower_surface_goal(surface, "requirement spelling");
        debug_assert!(
            lowered
                .as_ref()
                .is_ok_and(|lowered| self.written_states_requirement(lowered, requirement)),
            "the spelling `{}` of requirement {:?} lowers to {:?}",
            crate::surface::printing::source_click_proposition(surface),
            requirement.proposition,
            lowered.map_err(|error| error.to_string())
        );
    }

    /// This Proof advanced by `stepped`'s checked step, recorded as one
    /// `StepProved` node so the obligation proofs expand with the step.
    fn step_proved_successor(
        &self,
        stepped: Self,
        step: ProofStep,
        proof: StepProofCertificate,
    ) -> Self {
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: stepped.state,
            node: ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::StepProved {
                    step: Box::new(step),
                    proof,
                }),
            ),
        }
    }

    pub(super) fn execution_update_error(
        &self,
        operation: &str,
        error: ExecutionUpdateError,
    ) -> ClickError {
        match error {
            ExecutionUpdateError::NotFrontier => self.step_error(format!(
                "{operation} cannot advance C execution inside a proposition proof"
            )),
            ExecutionUpdateError::MissingExecution => {
                self.step_error("execution-frontier proof lost its semantic state")
            }
            ExecutionUpdateError::NotLoopBody => {
                self.step_error("`close_invariants` is only available in a loop-region proof")
            }
            ExecutionUpdateError::InvariantsAlreadyClosed => {
                self.step_error("the invariant bundle was closed more than once on one path")
            }
        }
    }

    /// The proof's facts with the body's memory effects and their store
    /// equations, as the loop's back edge reads them: the proof's own
    /// context extended by the effects, not a fold of every path fact.
    pub(in crate::surface::proof) fn back_edge_assumptions(
        &self,
        execution: &ExecutionProofState,
    ) -> PureFactContext {
        execution
            .core
            .effect_facts
            .iter()
            .map(|fact| fact.proposition().clone())
            .chain(crate::kernel::certified_store_equations(
                &execution.core.effect_facts,
            ))
            .fold(
                self.facts().pure_context(),
                PureFactContext::assume_proposition,
            )
    }

    /// Checks the heap, resource, and counted-population components at this
    /// loop-state join using the Proof-owned state and facts.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn check_loop_state_join(
        &self,
        loop_entry_state: &CState,
        loop_head_state: &CState,
        head_iterations: &crate::kernel::IntegerTerm,
        condition: &CExpression,
        invariant_checks: &[CLoopInvariantCheck],
        binders: &[crate::kernel::CLoopBinder],
        structural_measure: Option<&str>,
        composite_resource_definitions: &[CCompositeResourceDefinition],
    ) -> Result<(), ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop state join requires an execution proof"));
        }
        self.require_execution_frontier("loop state join")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop state join lost its execution state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop state join requires a loop-region proof"));
        }
        let assumptions = self.back_edge_assumptions(execution);
        // The back edge binds the loop's names again before anything reads
        // them: whatever the body called the instance it ends holding, the
        // binder names it, and a body that ends with no instance at those
        // arguments fails here by name.
        let back_edge_state = crate::kernel::c_loop_state_with_loop_binders_rebound(
            loop_head_state,
            &execution.core.state,
            binders,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop state join: {message}")))?;
        // D6: a structural `decreases` is decided here, against the instance
        // the binder held at the loop head. It is not a bundle member, so a
        // back edge that does not descend is named at the join.
        if let Some(measure) = structural_measure
            && let Some(failure) = crate::kernel::loop_structural_descent_failure(
                loop_head_state,
                &back_edge_state,
                binders,
                measure,
                composite_resource_definitions,
                &assumptions,
            )
        {
            return Err(self.step_error(format!("loop state join: {failure}")));
        }
        let invariant_obligations = crate::kernel::c_loop_invariant_obligations_at_back_edge(
            &back_edge_state,
            loop_entry_state,
            invariant_checks,
            head_iterations,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop invariant classification: {message}")))?;
        let assumptions = invariant_obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .fold(assumptions, PureFactContext::assume_proposition);
        if !crate::kernel::c_loop_condition_may_continue(&back_edge_state, condition, &assumptions)
            .map_err(|message| {
                self.step_error(format!("loop condition classification: {message}"))
            })?
        {
            return Ok(());
        }
        // Heap lifetime and resource ownership are compared against the head
        // the body actually started from. That is the loop entry context for
        // an ordinary loop, and the loop's own narrower resource context when
        // the loop declares `owns` or `views` clauses of its own. A binder's
        // model is what its invariants constrain, so the ownership comparison
        // sets it aside; the invariant obligations above checked it.
        crate::kernel::c_loop_binder_state_components_match_at_back_edge(
            loop_head_state,
            &back_edge_state,
            binders,
            &assumptions,
            composite_resource_definitions,
        )
        .map_err(|message| self.step_error(format!("loop state join: {message}")))
    }

    /// Consume the complete prepared bundle without lowering or proof search.
    pub(in crate::surface::proof) fn validate_loop_invariant_bundle(
        &self,
        invariant_checks: &[CLoopInvariantCheck],
        ranking_measures: &[crate::kernel::CRankingComponent],
    ) -> Result<(), ClickError> {
        self.state
            .validate_checked_invariant_lowerings(invariant_checks, ranking_measures)
            .map_err(|message| self.step_error(message))
    }

    /// Record closure only after validating the exact retained evidence.
    ///
    /// The retained evidence is created by `retain_invariant_body`, which also
    /// requests the frontier's closure, so a validated bundle is always an
    /// already-closed one. Certification therefore adds no proof step of its
    /// own: the bundle's certificate step is the `close_invariants() by` node
    /// carrying the checked body, never a bare closure request that no
    /// explicit proof could spell.
    pub(in crate::surface::proof) fn certify_loop_invariant_bundle(
        &self,
        invariant_checks: &[CLoopInvariantCheck],
        ranking_measures: &[crate::kernel::CRankingComponent],
    ) -> Result<Self, ClickError> {
        self.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if execution.core.region_invariants_close_requested {
            Ok(self.clone())
        } else {
            Err(self.step_error(
                "the loop invariant bundle carries checked body evidence without a closed frontier",
            ))
        }
    }

    /// Splits the focused branch preservation frontier under a proof-level `if`,
    /// introducing each arm's case assumption through the one shared
    /// case-assumption law, so lowered spellings, recorded surface
    /// propositions, and feasibility match the checked form exactly.
    /// Infeasible arms are omitted; the returned slots align `[then, else]`.
    /// Sibling arms stay separate — a preservation path never rejoins across
    /// the back edge — so no join consumes this split.
    pub(in crate::surface::proof) fn split_preservation_case(
        &self,
        condition: &ClickProposition,
        tactic_index: usize,
    ) -> Result<(Self, [Option<BranchId>; 2]), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a preservation `if` requires an execution proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("proof `if`")?;
        let mut base_execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // A mid-execution case condition may name the current statement's
        // entry snapshot before any step has crossed it; record it so the
        // form lowers, exactly as the checked `if` did.
        record_current_statement_entry(
            &base_execution.core.frontier,
            &mut base_execution.presentation.recorded_snapshots,
            &base_execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            tactic_index,
            "if",
        )?;
        // A split that is this statement's own C `if` records the decision the
        // C program made, at the entry snapshot where it was made, so a later
        // bundle closer can name it after the loop body has overwritten the
        // cells the condition read.
        let c_branch_condition =
            c_branch_condition_at_frontier(&base_execution, context, condition)?;
        let mut arms: [Option<(ProofFacts, ExecutionProofState, Vec<Proposition>)>; 2] =
            [None, None];
        let lowering_condition = self.substitute_fixed_state_locals_in_proposition(condition)?;
        for value in [true, false] {
            let mut arm_execution = base_execution.clone();
            if let Some(branch_condition) = &c_branch_condition {
                arm_execution
                    .presentation
                    .path_branch_premises
                    .push(if value {
                        branch_condition.clone()
                    } else {
                        negate_click_proposition(branch_condition)
                    });
            }
            let Some(added_fact) = introduce_proof_case_assumption(
                &mut arm_execution,
                &tactic_context,
                self.facts(),
                base_execution.core.has_structured_branch_history,
                condition,
                &lowering_condition,
                value,
            )?
            else {
                continue;
            };
            // Record where this proof-level case split sits in the path's
            // surface record, exactly as the checked form recorded it.
            if arm_execution.presentation.surface_record.blocker.is_none() {
                // The split sits after this path's own steps. The offset is
                // read back against the arm's `path_certificate()`, which
                // carries only the focused goal's lineage, so it is measured
                // the same way: a sibling arm stepped earlier in the same
                // derivation contributes steps to `certificate()` that this
                // path never took, and counting those puts the case past the
                // end of its own tactics.
                let tactic_offset = self.path_step_count()?;
                arm_execution
                    .presentation
                    .surface_record
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        selector: SurfacePathSelector::Proposition(condition.clone()),
                        value,
                        tactic_offset,
                    });
            }
            let added = added_fact.into_iter().collect::<Vec<_>>();
            let mut facts = self.facts().clone();
            for fact in &added {
                facts = facts.with_kernel_checked_fact(fact.clone());
            }
            arms[usize::from(!value)] = Some((facts, arm_execution, added));
        }
        match arms {
            [
                Some((then_facts, then_execution, then_added)),
                Some((else_facts, else_execution, else_added)),
            ] => {
                let split = self
                    .state
                    .publish_checked_frontier_split(
                        [(then_facts, then_execution), (else_facts, else_execution)],
                        [then_added, else_added],
                        Vec::new(),
                    )
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let (state, _, ids, _) = split.into_parts_with_facts();
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
                };
                Ok((successor, [Some(ids[0]), Some(ids[1])]))
            }
            [then_arm, else_arm] => {
                let (value, (facts, execution, added)) = if let Some(arm) = then_arm {
                    (true, arm)
                } else if let Some(arm) = else_arm {
                    (false, arm)
                } else {
                    return Err(self.step_error(
                        "no feasible arm exists for this preservation `if` condition",
                    ));
                };
                let state = self
                    .state
                    .publish_checked_frontier_transition(facts, execution, added, Vec::new())
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: self.node.clone(),
                };
                let mut ids = [None, None];
                ids[usize::from(!value)] = Some(successor.focused_branch_id());
                Ok((successor, ids))
            }
        }
    }

    /// The one mid-execution `transport` premise law, shared by the drivers:
    /// the source and target are lowered at the frontier, the premise
    /// planner names the premises, and this Proof applies the explicit
    /// `transport using` transition. The planner's failure is the answer,
    /// with its diagnostic. `source_refusal` is the refusal of the bare
    /// form's source-only attempt, which that diagnostic reports when it
    /// names a frame the source could not cross.
    pub(in crate::surface::proof) fn apply_planned_fact_transport(
        &self,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Self, ClickError> {
        self.apply_planned_fact_transport_inner(
            surface_source,
            surface_target,
            tactic_index,
            source_refusal,
        )
        .map_err(|error| {
            self.record_certification_failure_trace(self.claim_label(), 0);
            self.attach_step_diagnostic(error)
        })
    }

    fn apply_planned_fact_transport_inner(
        &self,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Self, ClickError> {
        let resolved_source = self.substitute_fixed_state_locals_in_proposition(surface_source)?;
        let resolved_target = self.substitute_fixed_state_locals_in_proposition(surface_target)?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`transport` requires an execution-frontier proof"));
        };
        let claim_label = context.claim_label;
        if self.focused_outcome_data().is_some() {
            return self.apply_planned_outcome_fact_transport(
                surface_source,
                surface_target,
                tactic_index,
                source_refusal,
            );
        }
        let premises = {
            let view = self.planning_execution_view()?;
            let (state, frontier, facts) = (view.state, view.frontier, &view.facts.to_vec());
            if frontier.is_at_function_entry() || frontier.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one completed execution step"
                )));
            }
            let assumptions = assumptions_from_propositions(facts);
            let pre_state = view.context.old_reference_state(frontier, state);
            let source = lower_fixed_state_proposition(
                &resolved_source,
                facts,
                context.parameter_binding(),
                FixedStateFrame::new(pre_state, state, None, &view.execution.presentation.recorded_snapshots),
                context.spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &source)
                .is_none()
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        facts,
                        state.resources().facts(),
                        context.parameter_binding(),
                        &view.execution.core.effect_facts,
                    )
                )));
            }
            let target = lower_fixed_state_proposition(
                &resolved_target,
                facts,
                context.parameter_binding(),
                FixedStateFrame::new(pre_state, state, None, &view.execution.presentation.recorded_snapshots),
                context.spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = super::super::cursor_execution::fact_transport_transition_facts(
                &view.execution.core.effect_facts,
                &source,
            );
            plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                view.facts,
                &transition_facts,
                context.parameter_binding(),
                state,
            )
            .map_err(|error| {
                let mut reason = fact_transport_planning_failure(
                    surface_source,
                    surface_target,
                    view.unfolded_predicates,
                    &error,
                    source_refusal,
                );
                if crate::instrumentation::deadline_exceeded() {
                    // Lowering already produced these checked identities.
                    // A stopped planner may print them without rechecking or
                    // trying further proof routes after its budget expired.
                    use crate::surface::proof_diagnostics::render;
                    let _typed = render::TypedNotationScope::enter();
                    let mut labels = render::SnapshotLabels::with_state(
                        context.parameter_binding(), state,
                    );
                    let source = render::render_proposition_labeled(&source, &mut labels);
                    let target = render::render_proposition_labeled(&target, &mut labels);
                    reason.push_str(&format!(
                        "\n  checked source (holds): {source}\n  checked target (wanted): {target}{}",
                        labels.trace_legend(),
                    ));
                }
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {reason}"))
            })?
        };
        self.driver().apply_step(ProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }

    /// [`Self::apply_planned_fact_transport`] on a focused function outcome:
    /// the same premise planner, reading the path's effects, the returned
    /// state and the outcome's facts.
    fn apply_planned_outcome_fact_transport(
        &self,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`transport` requires an execution proof"));
        };
        let claim_label = context.claim_label;
        let (Some(data), Some(execution)) = (self.focused_outcome_data(), self.execution()) else {
            return Err(self.step_error("`transport` lost its focused function outcome"));
        };
        let source = self.lower_surface_proposition_direct(surface_source, "`transport` source")?;
        if crate::kernel::search::ProofSearch::derive_proposition(
            self.facts().assumptions(),
            &source,
        )
        .is_none()
        {
            let facts = self.facts().to_vec();
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                describe_missing_pure_fact(
                    &source,
                    &facts,
                    data.core.state.resources().facts(),
                    context.parameter_binding(),
                    &*data.core.effect_facts,
                )
            )));
        }
        let target = self.lower_surface_proposition_direct(surface_target, "`transport` target")?;
        let transition_facts = super::super::cursor_execution::fact_transport_transition_facts(
            &*data.core.effect_facts,
            &source,
        );
        let premises = plan_explicit_fact_transport(
            surface_source,
            &source,
            &target,
            self.facts(),
            &transition_facts,
            context.parameter_binding(),
            &data.core.state,
        )
        .map_err(|error| {
            let reason = fact_transport_planning_failure(
                surface_source,
                surface_target,
                &execution.core.unfolded_predicates,
                &error,
                source_refusal,
            );
            ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {reason}"))
        })?;
        self.driver().apply_step(ProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }

    /// Records where the checked `close_invariants` tactic sat, so the
    /// kernel re-derivation its caller performs at the bundle check can be
    /// timed against that tactic's identity. Cursor metadata only.
    pub(in crate::surface::proof) fn record_invariant_closer(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`close_invariants`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement_index = execution.core.frontier.next_statement_index;
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.invariant_closer_step = Some(InvariantCloserStep {
                tactic_index,
                source_index,
                statement_index,
            });
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Records a region-level `solve` for the loop-invariant bundle. The
    /// tactic's semantic content is the bundle closer certified at the
    /// typed boundary, so only its identity is recorded here — cursor
    /// metadata for expansion capture and timing attribution, never a
    /// semantic transition.
    pub(in crate::surface::proof) fn defer_region_solve(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`solve`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(
                self.step_error("a region `solve` is only available in a loop-region proof")
            );
        }
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.region_solve = Some((tactic_index, source_index));
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Applies a frontier-local `loop` tactic as one checked operation on
    /// the focused branch execution frontier: the loop's phases verify through the
    /// shared loop-planning machinery, the certified loop rule replaces the
    /// `while` statement in the frontier's own statement tree, and the
    /// derived exit facts join this goal's context. The surface record and
    /// expansion capture ride the transitional cursor exactly as the
    /// checked form recorded them.
    pub(in crate::surface::proof) fn apply_frontier_local_loop(
        &self,
        mut expansion_capture: Option<&mut ExpansionCapture>,
        loop_clause: &StructuralClause,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`loop` requires an execution-frontier proof"));
        };
        let read_checkpoint = crate::surface::proof_trace::enabled_for(self.claim_label())
            .then(|| {
                self.focused_branch()
                    .map(|branch| branch.state.facts.assumptions().read_equality_checkpoint())
            })
            .flatten();
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`loop`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let source_facts = self.facts().clone();
        let mut facts = execution
            .presentation
            .loop_fact_list
            .as_ref()
            .and_then(|base| PureFactList::extended_to_proof_facts(base, &source_facts))
            .unwrap_or_else(|| PureFactList::from_proof_facts(&source_facts));
        // The next loop extends this copy; the indexes it builds here are
        // the ones every copy of it shares.
        facts.prepare_indexes();
        execution.presentation.loop_fact_list = Some(facts.clone());
        let base_facts = facts.len();
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let _timing = TacticTiming::new(
            context.claim_label,
            tactic_index,
            source_index,
            &ProofTactic::Loop(loop_clause.clone()),
            execution.core.frontier.next_statement_index,
        );
        // The loop clauses are written inside whatever proof scope reached
        // this frontier; the re-annotation resolves that scope's locals
        // before lowering them, as a `have` goal at this point would.
        let proof_locals = self.proof_local_values();
        let trace_lineage = self.trace_lineage(context.claim_label);
        let expanded_loop =
            crate::surface::proof_trace::with_loop_parent_lineage(trace_lineage, || {
                execute_frontier_local_loop(
                    expansion_capture.as_deref_mut(),
                    loop_clause,
                    &proof_locals,
                    self.facts(),
                    &mut execution,
                    &tactic_context,
                    &mut facts,
                    source_index,
                )
            })?;
        if capture_this_tactic {
            // The tactic's expansion is the expanded loop itself.
            let expansion = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(std::slice::from_ref(
                    &ProofTactic::Loop(expanded_loop.clone()),
                ))
                .expect("an expanded loop is one proof step")
                .steps()
                .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture, &expansion, false);
        }
        debug_assert!(facts.len() >= base_facts);
        let added = facts.facts_after(base_facts);
        let mut proof_facts = source_facts;
        for fact in &added {
            proof_facts = proof_facts.with_kernel_checked_fact(fact.clone());
        }
        // Retain the expanded loop clause as checked provenance so
        // whole-claim expansion serializes it without consulting the
        // transitional builder record.
        let loop_step = ProofCertificate::from_proof_tactics(std::slice::from_ref(
            &ProofTactic::Loop(expanded_loop),
        ))
        .map_err(|error| {
            self.step_error(format!(
                "`loop` produced an invalid expanded clause: {error}"
            ))
        })?
        .steps()[0]
            .clone();
        let state = self
            .state
            .publish_checked_frontier_transition(proof_facts, execution, added, Vec::new())
            .map_err(|error| self.execution_update_error("`loop`", error))?;
        let next = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: Some(Arc::new(loop_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                split_branches: Vec::new(),
            }),
        };
        if crate::surface::proof_trace::enabled_for(self.claim_label()) {
            // The loop's exported delta is the evidence available to its
            // continuation, including the exit disjunction. Do not truncate
            // that delta before it reaches the shared fact renderer.
            self.record_checked_trace_step(
                &next,
                "loop",
                None,
                None,
                usize::MAX,
                read_checkpoint.as_ref(),
            );
        }
        Ok(next)
    }
}

/// The body of the one `have` a proof of a step obligation retained.
fn retained_have_body(certificate: &ProofCertificate) -> Result<ProofCertificate, ClickError> {
    certificate
        .steps()
        .iter()
        .rev()
        .find_map(|step| match step {
            ProofStep::Have { proof, .. } => Some(proof.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| ClickError::new("a step obligation proof retained no `have`"))
}

/// Requirements up to alpha-equivalence, in the order first met.
fn distinct_requirements(recorded: Vec<UnresolvedRequirement>) -> Vec<UnresolvedRequirement> {
    let mut distinct: Vec<UnresolvedRequirement> = Vec::new();
    for requirement in recorded {
        if !distinct.iter().any(|seen| {
            crate::kernel::proof::propositions_are_alpha_equal(
                &seen.proposition,
                &requirement.proposition,
            )
        }) {
            distinct.push(requirement);
        }
    }
    distinct
}

thread_local! {
    static IMPLICIT_SOLVE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(in crate::surface::proof) fn implicit_solve_disabled() -> bool {
    IMPLICIT_SOLVE_DISABLED.with(std::cell::Cell::get)
        || super::super::implicit_solve_scope::selected_claim_is_strict()
}

/// Runs `operation` with the implicit `solve` off: a step gets only its fast
/// path and its written obligation proofs, with no search, so an obligation
/// nothing written proves is refused with its structured requirement.
/// The implicit tail is off with it: a script that leaves C to run, or a
/// goal open, at its end is refused instead of finished by search. This is
/// unconditional across all proof units. Audit uses
/// [`crate::surface::without_implicit_solve_for_claim`] when untouched proof
/// units are also visited during targeted verification.
pub fn without_implicit_solve<R>(operation: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            IMPLICIT_SOLVE_DISABLED.with(|disabled| disabled.set(self.0));
        }
    }
    let _restore = Restore(IMPLICIT_SOLVE_DISABLED.with(|disabled| disabled.replace(true)));
    operation()
}

/// The call a `step(callee, { ... })` runs at the frontier: its execution
/// name and argument expressions.
struct FrontierCall {
    callee: String,
    arguments: Vec<CExpression>,
}

/// The descent member of a ranked loop as its `decreases` clause writes it:
/// `m < at(<iteration entry>, m)` for one component, and for a tuple the
/// right-nested disjunction over pivots the kernel builds, each pivot strictly
/// smaller with every earlier component tied, `m == at(<iteration entry>, m)`.
/// The member reads its `pre` values at the iteration entry, as an `ensures`
/// reads them through `old`, so it is spelled the way its author would write
/// it, not reconstructed from the lowered goal.
fn ranking_descent_surface(bundle: &InvariantBodyContext) -> Option<ClickProposition> {
    let selector = bundle.iteration_entry_selector.as_ref()?;
    let components = &bundle.ranking_surfaces;
    if components.is_empty() || components.len() != bundle.ranking_measures.len() {
        return None;
    }
    let compare = |component: &ContractExpression, operator: ComparisonOperator| {
        ClickProposition::Comparison {
            left: component.clone(),
            operator,
            right: ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(component.clone()),
            },
        }
    };
    let arm = |pivot: usize| {
        (0..pivot).rev().fold(
            compare(&components[pivot], ComparisonOperator::LessThan),
            |rest, index| {
                ClickProposition::And(
                    Box::new(compare(&components[index], ComparisonOperator::Equal)),
                    Box::new(rest),
                )
            },
        )
    };
    (0..components.len()).rev().fold(None, |rest, pivot| {
        Some(match rest {
            None => arm(pivot),
            Some(rest) => ClickProposition::Or(Box::new(arm(pivot)), Box::new(rest)),
        })
    })
}

thread_local! {
    /// Set while one invariant bundle member is proved in its own `have`, so
    /// that proof closes the member itself rather than wrapping it again.
    static IN_BUNDLE_MEMBER_HAVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[path = "../driver/obligations.rs"]
mod driver;
