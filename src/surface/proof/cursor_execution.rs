use super::*;
use crate::kernel::CheckedCallEventScope;
use crate::kernel::ExecutionFactSource;
use crate::kernel::abstract_execution_state_for_interface_join_across;
use std::sync::Arc;

pub(super) struct BranchInterfaceJoinInputs<'a, 'proof> {
    pub(super) sibling_states: &'a [&'a ExecutionState; 2],
    pub(super) recorded_states: &'a RecordedStates,
    pub(super) proof: &'a Proof<'proof>,
    pub(super) entry_facts: &'a PureFactStore,
}

/// Checks a branch interface directly against the structural join's
/// persistent proof facts, without cloning or re-indexing unrelated facts.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_branch_interface_with_proof_facts(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    written_assertions: &[ProofAssertion],
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactStore,
    join_inputs: Option<BranchInterfaceJoinInputs<'_, '_>>,
    // `join_next_kernel_variable` is the counter every sibling arm abstracts
    // from: the highest of the arms' own. The arms' abstractions are compared
    // for equality, so they must count from one shared lower bound rather
    // than each from its own.
    join_next_kernel_variable: u64,
) -> Result<(), ClickError> {
    // Lower the resolved proof-local values, but retain their written names
    // for later certificates. Internal pointer values are not source syntax.
    assert_eq!(assertions.len(), written_assertions.len());
    let tactic_index = proof_context.tactic_index;
    let parameter_binding = proof_context.parameter_binding();
    let predicate_environment = proof_context.spec_definitions.predicates;
    let click_function_environment = proof_context.spec_definitions.functions;
    let resource_environment = proof_context.resource_environment;
    let claim_label = proof_context.claim_label;

    let state: &mut ExecutionState = &mut execution.core.state;

    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for (assertion, written) in assertions.iter().zip(written_assertions) {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let ProofAssertion::Fact(written_fact) = written else {
                    unreachable!("resolved interface assertion retains its written kind");
                };
                let fact = lower_fixed_state_proposition_with_assumptions(
                        surface_fact,
                        concrete_facts.assumptions(),
                        parameter_binding,
                        FixedStateFrame::new(proof_context.old_reference_state(&execution.core.frontier, state), state, None, &execution.presentation.recorded_states),
                        SpecDefinitions::new(predicate_environment, click_function_environment),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `branch ensuring` fact: {message}"
                        ))
                })?;
                execution
                    .presentation
                    .surface_propositions
                    .record_lowering(written_fact, &fact)?;
                if !crate::kernel::proof::checked_branch_fact_is_available(&concrete_facts, &fact) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish fact `{}`: {}",
                        describe_click_proposition(written_fact),
                        describe_missing_pure_fact(
                            &fact,
                            &concrete_facts,
                            state.resources().facts(),
                            parameter_binding,
                            &[]
                        )
                    )).with_spelled_requirement(
                        fact,
                        written_fact.clone(),
                        "`branch ensuring` fact".into(),
                    ));
                }
                if !concrete_facts.contains_top_level(&fact) {
                    concrete_facts = concrete_facts.with_kernel_checked_fact(fact);
                }
            }
            ProofAssertion::Resource(resource) => {
                let expected = lower_interface_resource_clause(
                    resource,
                    parameter_binding,
                    state,
                    concrete_facts.assumptions(),
                )?;
                let is_observed_core = resource_is_direct_observed_core(
                    resource,
                    &established_interface_resources,
                    resource_environment,
                    claim_label,
                    tactic_index,
                )?;
                if !is_observed_core
                    && !state
                        .resources()
                        .satisfies_fact(&expected, concrete_facts.assumptions())
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish resource fact: {}",
                        describe_missing_resource_fact(
                            &expected,
                            &concrete_facts,
                            state.resources().facts(),
                            parameter_binding,
                            &[]
                        )
                    )));
                }
                established_interface_resources.push(resource.clone());
            }
        }
    }
    let Some(join_inputs) = join_inputs else {
        *available_pure_facts = concrete_facts;
        return Ok(());
    };
    let entry_state = execution.core.frontier.execution_start_state(state).clone();
    // `old(...)` in an interface fact means the function's entry, also
    // inside a loop body, where the region's own start is a later state.
    let old_reference = proof_context
        .old_reference_state(&execution.core.frontier, state)
        .clone();
    let abstraction = abstract_execution_state_for_interface_join_across(
        state,
        join_inputs.sibling_states,
        join_next_kernel_variable,
    );
    let abstraction = abstraction.map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not abstract `branch` target state: {message}"
        ))
    })?;
    if let Some(goal) = abstraction.unproved_memory_separation(join_inputs.entry_facts) {
        let join_entry = join_inputs.proof;
        let spelling = join_entry
            .structural_goal_spelling(goal)
            .as_ref()
            .map(crate::surface::printing::source_click_proposition);
        let detail = spelling
            .as_ref()
            .map(|source| format!("; prove `{source}` before the branch"))
            .unwrap_or_default();
        return Err(join_entry.step_error_with_requirement(
            format!(
                "branch memory join requires separation from active borrows at the split{detail}"
            ),
            None,
            Some((
                "branch memory join separation",
                Box::new(goal.clone()),
                spelling,
            )),
        ));
    }
    let mut abstract_state = abstraction.state;
    let mut join_kernel_variable_mark = abstraction.next_kernel_variable;

    execution.presentation.case_assumptions.clear();
    execution.core.execution_abstraction = true;

    let mut exported_resources = ResourceContext::new();
    // Extend one indexed context as the interface publishes each fact.
    // Rebuilding the growing prefix for every assertion is quadratic even
    // though the interface itself is explicit output.
    let mut exported_pure_facts = PureFactStore::default();
    for assertion in assertions {
        if let ProofAssertion::Resource(resource) = assertion {
            // A named instance may carry a different model in each arm. The
            // rejoined proof holds it with a fresh model, drawn after the
            // abstraction's own identities; the kernel's check of the join
            // draws the same one.
            let with_fresh_model;
            let resource = match resource {
                ResourceClause::Named {
                    binding,
                    resource: declared,
                } if binding.schema.is_some() => {
                    let schema = binding.schema.as_ref().expect("checked just above");
                    let (fields, next) = crate::kernel::interface_join_instance_fields(
                        schema,
                        binding.instance()?,
                        join_kernel_variable_mark,
                    )
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not give interface resource `{}` a fresh model",
                            binding.name
                        ))
                    })?;
                    join_kernel_variable_mark = next;
                    with_fresh_model = ResourceClause::Named {
                        binding: ResourceInstanceBinding {
                            fields: Some(fields),
                            ..binding.clone()
                        },
                        resource: declared.clone(),
                    };
                    &with_fresh_model
                }
                other => other,
            };
            let fact = lower_interface_resource_clause(
                resource,
                parameter_binding,
                &abstract_state,
                // Each arm checked these argument reads above, before the
                // state was abstracted. Re-express the already-established
                // interface at its fresh join state; do not demand the
                // concrete state's initialization facts a second time.
                &concrete_facts
                    .assumptions()
                    .clone()
                    .allow_symbolic_contract_loads(),
            )
            .map_err(|_| {
                // The clause was read in this arm's own state above, so what
                // fails here is reading it in the state the arms join in.
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: the `ensuring` interface names `{}`, which each arm holds, but its arguments cannot be read in the state the arms join in. Fold the resource that owns the memory they read inside each arm and name that owner in `ensuring` instead",
                    crate::surface::validation::describe_resource_clause(resource),
                ))
            })?;
            let mut projections = Vec::new();
            append_lowered_resource_clause_loadable_fact(
                resource,
                &fact,
                &abstract_state,
                &mut projections,
            );
            exported_resources = exported_resources.unchecked_with_fact(fact);
            for fact in projections {
                if !exported_pure_facts.contains_top_level(&fact) {
                    exported_pure_facts = exported_pure_facts.with_kernel_checked_fact(fact);
                }
            }
            // An `old(...)` interface assertion may need the same view's
            // loadability at region entry. Use the arm's checked facts to
            // establish that spelling independently of the successor view.
            if matches!(resource, ResourceClause::ViewMemory(_)) {
                let _timing = crate::instrumentation::OperationTiming::new(
                    proof_context.parsed_function.name(),
                    claim_label,
                    "branch interface entry loadability",
                );
                if let Ok(entry_lowered) =
                    lower_resource_clause_at_state(resource, parameter_binding, &entry_state)
                {
                    let mut entry_loadables = Vec::new();
                    append_lowered_resource_clause_loadable_fact(
                        resource,
                        &entry_lowered,
                        &entry_state,
                        &mut entry_loadables,
                    );
                    for fact in entry_loadables {
                        crate::instrumentation::record_deterministic_work(1);
                        if concrete_facts.assumptions().proves_exact(&fact)
                            && !exported_pure_facts.contains_top_level(&fact)
                        {
                            exported_pure_facts =
                                exported_pure_facts.with_kernel_checked_fact(fact);
                        }
                    }
                }
            }
        }
    }
    abstract_state = abstract_state.with_resource_context(exported_resources.clone());
    let interface_records = execution.presentation.recorded_states.for_branch_interface(
        join_inputs.recorded_states,
        target,
        &abstract_state,
    );

    for (assertion, written) in assertions.iter().zip(written_assertions) {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let ProofAssertion::Fact(written_fact) = written else {
                unreachable!("resolved interface assertion retains its written kind");
            };
            let (fact, receipts) = lower_fixed_state_interface_join_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameter_binding,
                    FixedStateFrame::new(&old_reference, &abstract_state, None, &interface_records),
                    SpecDefinitions::new(predicate_environment, click_function_environment),
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `branch ensuring` fact: {message}"
                    ))
                })?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(written_fact, &fact)?;
            if !exported_pure_facts.contains_top_level(&fact) {
                exported_pure_facts = exported_pure_facts.with_kernel_checked_fact(fact);
            }
            // The domains the arms established for the fact's typed calls.
            for receipt in receipts {
                if !exported_pure_facts.contains_top_level(&receipt) {
                    exported_pure_facts = exported_pure_facts.with_kernel_checked_fact(receipt);
                }
            }
        }
    }

    // The checked join constructs the owning successor after consuming the
    // interface in both arms. This provisional context only supported lowering.
    *state = abstract_state;
    // The abstraction issued identities from the execution's one counter, and
    // the joined execution continues from where it left it. Keeping the old
    // counter here is what would let the next loop head, opaque call or heap
    // allocation hand a live abstracted value's identity to something else.
    // The kernel owns the counter, so this moves it forward through the
    // kernel's checked forward-only setter rather than writing the field.
    execution
        .core
        .advance_kernel_variable_mark(join_kernel_variable_mark)
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `branch` join abstraction: {message}"
            ))
        })?;
    *available_pure_facts = exported_pure_facts;
    Ok(())
}

/// The path's case facts, then `delta`'s, then its effects, as a completing
/// statement publishes them.
fn completed_execution_facts(
    core: &crate::kernel::proof::ExecutionProofCore,
    delta: &ExecutionFacts,
) -> crate::kernel::proof::CompletedExecutionFacts {
    core.completed_execution_facts(delta)
}

pub(super) fn append_execution_effect_facts(
    target: &mut ExecutionFacts,
    source: &(impl ExecutionFactSource + ?Sized),
) {
    let source = source.persistent_facts();
    let mut seen = BTreeSet::new();
    let accepted = source
        .iter()
        .enumerate()
        .filter_map(|(index, fact)| {
            // Keep kernel-certified transition facts as well as memory summaries,
            // without restating opaque call identities in surface certificates.
            ((is_memory_effect_proposition(fact.proposition()) || fact.is_certified())
                && !target.contains(fact)
                && seen.insert(fact))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    target.extend_shared(&source.selected(&accepted));
}

pub(super) fn fact_transport_transition_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
    source: &Proposition,
) -> ExecutionFacts {
    let source_memories = program_condition_fact_memories(source);
    let matching_effect = facts.fact_iter().position(|fact| {
        let before = match fact.proposition() {
            Proposition::MemoryMutatesOnly { before, .. }
            | Proposition::MemoryEffectSummary { before, .. }
            | Proposition::HeapAllocationFreed { before, .. } => before,
            _ => return false,
        };
        source_memories.contains(before)
    });
    let Some(start) = matching_effect else {
        return facts.persistent_facts();
    };
    let end = facts
        .fact_iter()
        .skip(start + 1)
        .position(|fact| is_memory_effect_proposition(fact.proposition()))
        .map(|offset| start + 1 + offset)
        .unwrap_or(facts.len());
    facts
        .fact_iter()
        .skip(start)
        .take(end - start)
        .cloned()
        .collect()
}

fn is_memory_effect_proposition(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::MemoryMutatesOnly { .. }
            | Proposition::MemoryEffectSummary { .. }
            | Proposition::HeapAllocationFreed { .. }
    )
}

fn resource_is_direct_observed_core(
    required: &ResourceClause,
    established: &[ResourceClause],
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<bool, ClickError> {
    for parent in established {
        let ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } = parent
        else {
            continue;
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_argument_substitutions(definition, parent, claim_label, tactic_index)?;
        for child in body.contains() {
            let child = instantiate_resource_clause(child, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate observed child of `{name}`: {message}"
                ))
            })?;
            let core = match child {
                ResourceClause::Named { .. } => continue,
                ResourceClause::Quantified { .. } | ResourceClause::Conditional { .. } => continue,
                ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                    ResourceClause::ViewMemory(segment)
                }
                ResourceClause::MemoryAggregate { .. } | ResourceClause::Iterated(_) => continue,
                ResourceClause::Declared {
                    kind,
                    name,
                    arguments,
                    parameter_types,
                    ..
                } => ResourceClause::Declared {
                    type_schema: None,
                    resource_type_arguments: Vec::new(),
                    resource_arguments: Vec::new(),
                    access: ResourceAccessMode::View,
                    kind,
                    name,
                    arguments,
                    parameter_types,
                },
            };
            if &core == required {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// The pure facts a step refusal lists as its proof context.
///
/// A step run inside a proof context hands the kernel that context as its
/// assumptions and passes the fact slice only as the statement-local delta,
/// so listing the slice alone shows `pure facts: []` beside a `requires` the
/// step did see. List the context the kernel checked against.
fn listed_context_pure_facts(
    delta: &(impl PropositionSource + ?Sized),
    context: Option<&PureFactContext>,
) -> Vec<Proposition> {
    const LIMIT: usize = 32;
    let mut facts = delta
        .propositions()
        .take(LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    if let Some(context) = context {
        facts.extend(context.diagnostic_fact_sample(LIMIT - facts.len(), 0).0);
    }
    facts.sort();
    facts.dedup();
    facts
}

#[cfg(test)]
thread_local! {
    static STEP_DIAGNOSTIC_RESOURCE_READS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(in crate::surface) fn take_step_diagnostic_resource_reads() -> usize {
    STEP_DIAGNOSTIC_RESOURCE_READS.with(|count| count.replace(0))
}

/// The full pre-step resource context is for diagnostic rendering.
fn step_diagnostic_resources(state: &ExecutionState) -> &[ResourceFact] {
    let resources = state.resources().facts();
    #[cfg(test)]
    STEP_DIAGNOSTIC_RESOURCE_READS.with(|count| count.set(count.get() + resources.len()));
    resources
}

fn describe_step_proof_context(
    delta: &(impl PropositionSource + ?Sized),
    context: Option<&PureFactContext>,
    resources: &[ResourceFact],
    binding: ParameterBinding<'_>,
    execution: &(impl ExecutionFactSource + ?Sized),
) -> String {
    let mut description = describe_proof_context(
        &listed_context_pure_facts(delta, context),
        resources,
        binding,
        execution,
    );
    let total = context.map_or(0, |context| {
        let (conditions, propositions) = context.fact_counts();
        conditions + propositions
    });
    if total.saturating_add(delta.propositions().take(33).count()) > 32 {
        description.push_str(
            "\n  pure facts shown are a bounded sample of the context and statement facts",
        );
    }
    description
}

pub(super) fn execute_branch_step_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    requested_branch: Option<bool>,
    prerequisite_policy: StatementPrerequisitePolicy,
    complete_empty_branch: bool,
    context: Option<&PureFactContext>,
) -> Result<bool, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let parameter_binding = proof_context.parameter_binding();
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let checked_call_events = execution.core.checked_call_events();
    let _checked_call_event_scope = CheckedCallEventScope::start(&checked_call_events);

    let state: &mut ExecutionState = &mut execution.core.state;

    let statement_index = execution.core.frontier.next_statement_index;
    let _site_scope = crate::surface::diagnostics::StatementSiteScope::enter(
        &proof_context.constants.source_layout,
        statement_index,
        proof_context.parsed_function,
    );
    let source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve region({statement_index})"
        ))
    })?;
    let (execution_start_state, mut current_state, statement, remaining) =
        next_top_level_statement_from_frontier_position(
            ExecutionView::new(
                &execution.core.frontier,
                &execution.presentation.recorded_states,
                &execution.presentation.surface_propositions,
            ),
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    // A Rust `match` arm's variant test that the facts do not decide has one
    // successor per variant, as an undecided C condition has two. Each is
    // its own proof arm: a proof `match` on the value names the fields its
    // arm learns, which a proof `if` on the test could not.
    if let Some(split) = enum_switch_proof_match(&statement, &current_state, context) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached a Rust `match` of `{}`, whose variant is not known here; each variant is its own proof arm. Write `{}` here, or end the script here and let its implicit tail split it",
            split.describe_scrutinee(),
            split.outline(),
        ))
        .with_path_case_match(split));
    }
    let ProgramStatement::If {
        condition,
        then_branch,
        else_branch,
    } = statement
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires the next C statement to be an `if`"
        )));
    };
    let SourceStatementKind::If {
        then_statement_index,
        else_statement_index,
    } = source_region.kind
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` found a C `if` outside its source region"
        )));
    };

    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        context,
    )?;
    if condition_transitions.len() != 1 {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        // The path facts of an undecided C condition carry the whole memory
        // state each load reads. Spelling them in the bounded source
        // vocabulary keeps the useful part -- which condition each arm
        // assumes -- without the repeated `SymbolicMemory` dump.
        let paths = condition_transitions
            .iter()
            .enumerate()
            .map(|(index, transition)| {
                format!(
                    "\n  condition path {index}: {}",
                    describe_pure_facts_for_diagnostic(&transition.path_facts, parameter_binding)
                )
            })
            .collect::<String>();
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths{paths}\n{}",
            describe_program_expression(&condition),
            condition_transitions.len(),
            describe_step_proof_context(
                available_pure_facts,
                context,
                step_diagnostic_resources(&current_state),
                parameter_binding,
                &[]
            )
        )));
    }
    let condition_transition = condition_transitions
        .into_iter()
        .next()
        .expect("one condition transition was required");
    let selected_then = condition_transition.is_true;
    if requested_branch.is_some_and(|take_then| selected_then != take_then) {
        let actual = if selected_then { "then" } else { "else" };
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requested the {} branch, but current pure facts prove the {actual} branch",
            if requested_branch == Some(true) {
                "then"
            } else {
                "else"
            }
        )));
    }

    execution
        .core
        .record_condition_transition(
            function,
            arguments,
            condition_transition.theorem.clone(),
            condition_transition.context.clone(),
            &condition_transition.path_facts,
            &[],
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded condition evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameter_binding)
            ))
        })?;
    *available_pure_facts = condition_transition.pure_facts;
    {
        let _allocation_resolution = crate::instrumentation::OperationTiming::new(
            function.name(),
            claim_label,
            "branch allocation resolution",
        );
        // Condition certification selects pending allocation and pthread-create
        // outcomes. Retain that exact checked successor: recomputing from the
        // old state can lose the selected resources or their mutation ancestry.
        current_state = execution.core.reached_state().clone();
    }
    let selected_branch = if selected_then {
        *then_branch
    } else {
        *else_branch
    };
    execution.core.frontier.next_statement_index = if selected_then {
        then_statement_index
    } else {
        else_statement_index
    };
    execution.core.frontier.execution_start_state = Some(execution_start_state);
    execution.core.state = current_state.into();
    // The selected arm is spliced before the `if`'s tail so the frontier's
    // own statement tree keeps every downstream statement reachable; the
    // patched source layout carries arm-final control successors, so no
    // continuation record is needed.
    if complete_empty_branch && matches!(selected_branch, ProgramStatement::Skip) {
        // The empty arm completes this branch region immediately; the patched
        // layout supplies its control successor and statically completed
        // branch regions.
        let skip_index = execution.core.frontier.next_statement_index;
        let state = (*execution.core.state).clone();
        let state = execution
            .core
            .record_automatic_lifetime_end(
                &state,
                proof_context
                    .constants
                    .source_layout
                    .automatic_exits(skip_index, false),
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "{}{}",
                    crate::surface::diagnostics::describe_runtime_error_over_locals(&error, &state),
                    crate::surface::diagnostics::describe_execution_statement_site(),
                ))
                .with_kind(runtime_refusal_kind(&error))
                .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(&error))
            })?;
        execution
            .presentation
            .recorded_states
            .record_effect(execution.core.last_footprint.as_ref());
        execution.core.state = state.clone().into();
        for exited in proof_context
            .constants
            .source_layout
            .exited_branch_regions(skip_index)
            .to_vec()
        {
            record_statement_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                exited,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
        let successor = proof_context
            .constants
            .source_layout
            .statement(skip_index)
            .map(|region| region.continuation_node);
        match remaining {
            Some(tail) => {
                if let Some(successor) = successor {
                    execution.core.frontier.next_statement_index = successor;
                }
                execution.core.frontier.position = FrontierPosition::StatementEntry {
                    remaining: tail.into(),
                };
            }
            None => match resume_after_completed_region(&mut execution.core.frontier) {
                Some(tail) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: tail.into(),
                    };
                }
                None if finish_exhausted_region(&mut execution.core.frontier) => {}
                None => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                    )));
                }
            },
        }
    } else {
        let spliced = match remaining {
            Some(tail) => program_seq(selected_branch, tail),
            None => selected_branch,
        };
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: spliced.into(),
        };
    }
    record_current_statement_entry(
        &execution.core.frontier,
        &mut execution.presentation.recorded_states,
        &execution.core.state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_concrete_loop_head_step(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: ExecutionState,
    current_state: ExecutionState,
    loop_statement: ProgramStatement,
    remaining: Option<ProgramStatement>,
    context: Option<&PureFactContext>,
) -> Result<(), ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let parameter_binding = proof_context.parameter_binding();

    execution.core.concrete_loop_execution = true;
    let ProgramStatement::Loop {
        test, update, body, ..
    } = &loop_statement
    else {
        unreachable!("loop phase entry requires its source loop");
    };
    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    record_loop_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        loop_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    execution.core.frontier.execution_start_state = Some(execution_start_state);
    let sources = execution
        .core
        .enter_loop_phases(function, arguments)
        .map_err(|refusal| {
            ClickError::new(describe_evidence_refusal(&refusal, parameter_binding))
        })?;
    execution.core.state = current_state.clone().into();
    let pass = crate::kernel::program_loop_pass(body, update.as_deref(), Some(test));
    let after_loop = remaining.map(Arc::new);
    let repeat = match &after_loop {
        Some(tail) => ProgramStatement::seq(Arc::new(loop_statement.clone()), tail.clone()),
        None => loop_statement.clone(),
    };
    execution.core.frontier.continuations.push(
        ProofExecutionContinuation::loop_body(
            Arc::new(repeat),
            statement_index,
            after_loop,
            continuation_node,
            proof_context
                .constants
                .source_layout
                .loop_continuation_entry(loop_index),
            sources,
        )
        .map_err(|refusal| {
            ClickError::new(describe_evidence_refusal(&refusal, parameter_binding))
        })?,
    );
    let decision_at_header = test.position == crate::kernel::LoopTestPosition::BeforeBody
        && test.source_condition().is_some();
    execution.core.frontier.next_statement_index = if decision_at_header {
        proof_context
            .constants
            .source_layout
            .loop_test_phase_entry(loop_index)
            .ok_or_else(|| ClickError::new("loop test has no semantic source position"))?
    } else {
        proof_context
            .constants
            .source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| ClickError::new("loop has no source phase entry"))?
    };
    execution.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: Arc::new(pass),
    };
    if decision_at_header {
        execute_step_from_frontier_position_selecting_path(
            execution,
            proof_context,
            available_pure_facts,
            tactic_name,
            prerequisite_policy,
            LoopStepPolicy::EnterBody,
            None,
            context,
            None,
        )?;
    } else {
        record_statement_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            execution.core.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
    }
    Ok(())
}

pub(super) fn next_top_level_statement_from_frontier_position(
    view: ExecutionView<'_>,
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<NextTopLevelStatement, ClickError> {
    match &view.frontier.position {
        FrontierPosition::FunctionEntry => {
            let (execution_start_state, current_state) = if view.frontier.entry_member_prefix {
                (
                    view.frontier.execution_start_state.clone().ok_or_else(|| {
                        ClickError::new("checked entry member change lost its caller state")
                    })?,
                    state.clone(),
                )
            } else {
                let execution_start_state = state.clone();
                let current_state = program_function_entry_state(&execution_start_state, function, arguments)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                        ))
                    })?;
                (execution_start_state, current_state)
            };
            current_state.prepare_execution_variable_reservations();
            let (statement, remaining) =
                split_next_source_operation(function.body()).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, current_state, statement, remaining))
        }
        FrontierPosition::StatementEntry { remaining } => {
            let execution_start_state = view
                .frontier
                .execution_start_state
                .clone()
                .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` has no execution start state"
                ))
            })?;
            let (statement, remaining) =
                split_next_source_operation(remaining).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, state.clone(), statement, remaining))
        }
        FrontierPosition::FunctionExit { .. } => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        ))),
        FrontierPosition::RegionBoundary => Err(ClickError::new(match view.frontier.region {
            ExecutionRegionKind::BranchArm => format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` ran past the end of its branch body; an arm of `branch` must stop at the shared continuation"
            ),
            _ => format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run past the loop back-edge boundary"
            ),
        })),
    }
}

pub(super) fn record_loop_program_state(
    recorded_states: &mut RecordedStates,
    function_block: &FunctionBlock,
    loop_index: usize,
    kind: ProgramPointKind,
    state: ExecutionState,
) {
    record_code_region_program_state(
        recorded_states,
        function_block,
        CodeRegion::Loop(loop_index),
        kind,
        state,
    );
}

pub(super) fn record_statement_program_state(
    recorded_states: &mut RecordedStates,
    function_block: &FunctionBlock,
    statement_index: usize,
    kind: ProgramPointKind,
    state: ExecutionState,
) {
    record_code_region_program_state(
        recorded_states,
        function_block,
        CodeRegion::Statement(statement_index),
        kind,
        state,
    );
}

pub(super) fn record_code_region_program_state(
    recorded_states: &mut RecordedStates,
    function_block: &FunctionBlock,
    region: CodeRegion,
    kind: ProgramPointKind,
    state: ExecutionState,
) {
    let point_region = match region {
        CodeRegion::Function => CodeRegionRef::Function,
        CodeRegion::Loop(index) => {
            for label in function_block
                .structural_clauses()
                .for_loop(index)
                .into_iter()
                .filter_map(StructuralClause::label)
            {
                recorded_states.label_loop(index, label);
            }
            CodeRegionRef::Loop(index)
        }
        CodeRegion::Statement(index) => CodeRegionRef::Region(index),
    };
    recorded_states.insert(
        ProgramPointRef {
            region: point_region,
            kind,
        },
        state,
    );
}

pub(super) const PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT: usize = 32;

pub(super) fn surface_at_program_point<K: RecordedStateKey + ?Sized>(
    surface: &SyntaxProposition,
    key: &K,
) -> Result<SyntaxProposition, ClickError> {
    let selector = key.to_selector();
    annotate_surface_at_program_point(surface, &selector, ProgramPointAnnotation::Reread)
}

/// Freeze a case selector at its checked frontier without retargeting explicit
/// states or `old` expressions already carried by the selector.
pub(super) fn surface_frozen_at_program_point<K: RecordedStateKey + ?Sized>(
    surface: &SyntaxProposition,
    key: &K,
) -> Result<SyntaxProposition, ClickError> {
    annotate_surface_at_program_point(surface, &key.to_selector(), ProgramPointAnnotation::Freeze)
}

#[derive(Clone, Copy)]
enum ProgramPointAnnotation {
    Freeze,
    /// Re-read every operand in the selected state, replacing an existing `at`
    /// selector: fact transport across a statement re-reads the source
    /// form at the statement's exit, having proved the cells unchanged.
    Reread,
}

fn annotate_surface_at_program_point(
    surface: &SyntaxProposition,
    selector: &ProgramPointSelector,
    annotation: ProgramPointAnnotation,
) -> Result<SyntaxProposition, ClickError> {
    if matches!(
        surface,
        SyntaxProposition::Loadable { .. }
            | SyntaxProposition::Separate { .. }
            | SyntaxProposition::ResourceViewable { .. }
            | SyntaxProposition::Contains { .. }
    ) {
        return Ok(SyntaxProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface.clone()),
        });
    }
    // A negated numeral whose magnitude is no `int64` names no state and
    // stays as written: inside `at(..)` an unsuffixed numeral is read as a
    // C constant, so `at(S, -9223372036854775808)` would negate a `uint64`
    // magnitude rather than denote the `int64` minimum it spelled. Every
    // other numeral reads the same either way and keeps its anchor.
    let integer_literal = |expression: &SyntaxTerm| match expression {
        SyntaxTerm::Negate(inner) => matches!(
            inner.as_ref(),
            SyntaxTerm::IntegerLiteral(magnitude) if magnitude.parse::<i64>().is_err()
        ),
        _ => false,
    };
    let expression_at_program_point = |expression: &SyntaxTerm| match (annotation, expression) {
        (_, SyntaxTerm::Old(_)) | (ProgramPointAnnotation::Freeze, SyntaxTerm::At { .. }) => {
            expression.clone()
        }
        (_, literal) if integer_literal(literal) => literal.clone(),
        (ProgramPointAnnotation::Reread, SyntaxTerm::At { expression, .. }) => SyntaxTerm::At {
            selector: selector.clone(),
            expression: expression.clone(),
        },
        (_, expression) => SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(expression.clone()),
        },
    };
    // Construct one node outside the traversal frame. In debug builds these
    // by-value syntax temporaries are large; retaining them on every recursive
    // visit used tens of KiB per level inside an already nested proof planner.
    #[inline(never)]
    fn rebuild(
        proposition: &SyntaxProposition,
        expression_at_program_point: &impl Fn(&SyntaxTerm) -> SyntaxTerm,
        selector: &ProgramPointSelector,
        completed: &mut Vec<SyntaxProposition>,
    ) -> SyntaxProposition {
        let mut child = || Box::new(completed.pop().expect("visited state child"));
        match proposition {
            SyntaxProposition::Value(expression) => {
                SyntaxProposition::Value(expression_at_program_point(expression))
            }
            SyntaxProposition::Comparison {
                left,
                operator,
                right,
            } => SyntaxProposition::Comparison {
                left: expression_at_program_point(left),
                operator: *operator,
                right: expression_at_program_point(right),
            },
            SyntaxProposition::FloatClassification {
                expression,
                classification,
            } => SyntaxProposition::FloatClassification {
                expression: expression_at_program_point(expression),
                classification: *classification,
            },
            SyntaxProposition::IsA { class, pointer } => SyntaxProposition::IsA {
                class: class.clone(),
                pointer: expression_at_program_point(pointer),
            },
            SyntaxProposition::Defined { .. } => SyntaxProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition.clone()),
            },
            SyntaxProposition::At { .. } => proposition.clone(),
            SyntaxProposition::And(_, _) => {
                let right = child();
                SyntaxProposition::And(child(), right)
            }
            SyntaxProposition::Or(_, _) => {
                let right = child();
                SyntaxProposition::Or(child(), right)
            }
            SyntaxProposition::Not(_) => SyntaxProposition::Not(child()),
            SyntaxProposition::Implies(_, _) => {
                let right = child();
                SyntaxProposition::Implies(child(), right)
            }
            SyntaxProposition::ForAll {
                click_type: interface_type,
                name,
                ..
            } => SyntaxProposition::ForAll {
                click_type: interface_type.clone(),
                name: name.clone(),
                written_name: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            SyntaxProposition::Exists {
                click_type: interface_type,
                name,
                ..
            } => SyntaxProposition::Exists {
                click_type: interface_type.clone(),
                name: name.clone(),
                written_name: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            SyntaxProposition::RangeAll {
                start, end, item, ..
            } => SyntaxProposition::RangeAll {
                start: expression_at_program_point(start),
                end: expression_at_program_point(end),
                item: item.clone(),
                written_item: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            SyntaxProposition::RangeAny {
                start, end, item, ..
            } => SyntaxProposition::RangeAny {
                start: expression_at_program_point(start),
                end: expression_at_program_point(end),
                item: item.clone(),
                written_item: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            SyntaxProposition::PredicateCall { name, arguments } => {
                SyntaxProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_program_point).collect(),
                }
            }
            SyntaxProposition::Separate { .. }
            | SyntaxProposition::ResourceViewable { .. }
            | SyntaxProposition::Contains { .. }
            | SyntaxProposition::Loadable { .. } => proposition.clone(),
        }
    }
    // Postorder traversal stores references and completed output on the heap,
    // not large syntax values in one Rust call frame per logical connective.
    // Preserve left-to-right traversal, opaque `at` nodes, and the same bound.
    let mut pending = vec![(surface, 0, false)];
    let mut completed = Vec::new();
    while let Some((proposition, depth, visited)) = pending.pop() {
        if visited {
            let rebuilt = rebuild(
                proposition,
                &expression_at_program_point,
                selector,
                &mut completed,
            );
            completed.push(rebuilt);
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        if depth >= PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT {
            return Err(ClickError::new(
                "Surface Click state annotation exceeded its structural depth bound",
            ));
        }
        pending.push((proposition, depth, true));
        match proposition {
            SyntaxProposition::And(left, right)
            | SyntaxProposition::Or(left, right)
            | SyntaxProposition::Implies(left, right) => {
                pending.push((right, depth + 1, false));
                pending.push((left, depth + 1, false));
            }
            SyntaxProposition::Not(body)
            | SyntaxProposition::ForAll { body, .. }
            | SyntaxProposition::Exists { body, .. }
            | SyntaxProposition::RangeAll { body, .. }
            | SyntaxProposition::RangeAny { body, .. } => {
                pending.push((body, depth + 1, false));
            }
            _ => {}
        }
    }
    debug_assert_eq!(completed.len(), 1);
    Ok(completed.pop().expect("visited state root"))
}

/// Returns a program point selector explicitly carried by a proposition produced
/// by [`surface_at_program_point`]. Callers must still
/// re-lower any newly anchored form and check that it denotes the exact
/// retained kernel fact.
pub(in crate::surface) fn surface_program_point_selector(
    surface: &SyntaxProposition,
) -> Option<ProgramPointSelector> {
    let expression_site = |expression: &SyntaxTerm| match expression {
        SyntaxTerm::At { selector, .. } => Some(selector.clone()),
        _ => None,
    };
    match surface {
        SyntaxProposition::Value(expression) => expression_site(expression),
        SyntaxProposition::Comparison { left, right, .. } => {
            expression_site(left).or_else(|| expression_site(right))
        }
        SyntaxProposition::FloatClassification { expression, .. } => expression_site(expression),
        SyntaxProposition::At { selector, .. } => Some(selector.clone()),
        SyntaxProposition::And(left, right)
        | SyntaxProposition::Or(left, right)
        | SyntaxProposition::Implies(left, right) => {
            surface_program_point_selector(left).or_else(|| surface_program_point_selector(right))
        }
        SyntaxProposition::Not(body)
        | SyntaxProposition::ForAll { body, .. }
        | SyntaxProposition::Exists { body, .. } => surface_program_point_selector(body),
        SyntaxProposition::RangeAll {
            start, end, body, ..
        }
        | SyntaxProposition::RangeAny {
            start, end, body, ..
        } => expression_site(start)
            .or_else(|| expression_site(end))
            .or_else(|| surface_program_point_selector(body)),
        SyntaxProposition::PredicateCall { arguments, .. } => {
            arguments.iter().find_map(expression_site)
        }
        SyntaxProposition::Separate { .. }
        | SyntaxProposition::ResourceViewable { .. }
        | SyntaxProposition::Contains { .. }
        | SyntaxProposition::Loadable { .. }
        | SyntaxProposition::Defined { .. } => None,
        SyntaxProposition::IsA { pointer, .. } => expression_site(pointer),
    }
}

/// Resume an entered `try`'s handler after a `Throw` outcome instead of
/// terminating the path. Pops continuations through the handler
/// continuation (abandoning the unwound region, as C++ unwinding does),
/// binds the payload, and positions the frontier at the handler entry.
/// Returns `Ok(true)` with the handler entered, or `Ok(false)` when no
/// handler continuation is present (existing termination behavior then
/// applies). Only entered `try` bodies push handler continuations, so C
/// execution always takes the `Ok(false)` path. The bundled binding
/// transitions are ordinary checked transitions recorded like any other;
/// they are not user-visible steps.
#[allow(clippy::too_many_arguments)]
pub(super) fn route_throw_to_handler(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    introduced_facts: &mut Vec<Proposition>,
    function: &ProgramFunction,
    parameter_binding: ParameterBinding<'_>,
    function_block: &FunctionBlock,
    function_environment: &ExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    context: Option<&PureFactContext>,
    throw_value: &ProgramValue,
    thrown_state: &ExecutionState,
    throw_facts: &PureFactList,
) -> Result<bool, ClickError> {
    let handler = loop {
        match execution.core.frontier.continuations.pop() {
            Some(mut continuation) => {
                if let Some(exceptional) = continuation.exceptional.take() {
                    // The handler replaces the abandoned try body, but its
                    // normal completion must still resume after the try.
                    // Clear this handler so a rethrow cannot catch itself.
                    execution.core.frontier.continuations.push(continuation);
                    break Some(exceptional);
                }
                // Non-handler continuations in the abandoned region are
                // discarded with it.
            }
            None => break None,
        }
    };
    let Some(handler) = handler else {
        return Ok(false);
    };
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    // A `try` binds the payload exactly as the kernel's own `try` execution
    // does: declare the handler binding, then assign the thrown value, which
    // is always `int32` by `TryCatchInt32` semantics. An unwind cleanup binds
    // nothing: its cleanup runs and then the same exception continues.
    let mut state = thrown_state.clone();
    let mut facts = throw_facts.clone();
    let binding_steps = match &handler.entry {
        ExceptionalEntry::Catch(binding) => vec![
            program_declare(binding.clone(), crate::kernel::ProgramType::Int32),
            program_assign(
                binding.clone(),
                ProgramExpression::Value(throw_value.clone()),
            ),
        ],
        ExceptionalEntry::Unwind(_) => Vec::new(),
    };
    for statement in binding_steps {
        let mut kernel_variable = execution.core.kernel_variable_mark();
        let (transitions, _) = certified_statement_transitions(
            &state,
            &facts,
            &statement,
            function_environment,
            Some(proof_context.spec_definitions.predicates),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut execution.core.next_opaque_call,
            &mut kernel_variable,
            prerequisite_policy,
            context,
        )?;
        execution
            .core
            .advance_kernel_variable_mark(kernel_variable)
            .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
        let [transition] = transitions.try_into().map_err(|_| {
            ClickError::new(format!(
                "{transition_label}: handler binding transition did not complete"
            ))
        })?;
        let StatementOutcome::Normal(next_state) = &transition.outcome else {
            return Err(ClickError::new(format!(
                "{transition_label}: handler binding transition did not complete normally"
            )));
        };
        let next_state = next_state.clone();
        let footprint_bound = execution.core.record_statement_transition_with_descent(
            function,
            parameter_binding.arguments,
            &transition.native_step,
            transition.context.clone(),
            &transition.execution_facts,
        ).map_err(|refusal| {
            ClickError::new(format!(
                "{transition_label}: recorded handler binding evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameter_binding)
            ))
        })?;
        execution
            .presentation
            .recorded_states
            .record_effect(execution.core.last_footprint.as_ref());
        execution
            .presentation
            .record_generated_load_bindings(&transition.generated_load_bindings);
        append_execution_effect_facts(
            &mut execution.core.effect_facts,
            &transition.execution_facts,
        );
        facts = transition.pure_facts.clone();
        introduced_facts.extend(transition.introduced_facts.iter().cloned());
        facts.extend(footprint_bound.iter().cloned());
        introduced_facts.extend(footprint_bound);
        state = *next_state;
    }
    *available_pure_facts = facts;
    execution.core.state = state.clone().into();
    let mut handler_source = match &handler.entry {
        ExceptionalEntry::Catch(_) => handler.handler.clone(),
        ExceptionalEntry::Unwind(cleanup) => Arc::new(crate::kernel::program_unwind_continuation(
            cleanup,
            ProgramExpression::Value(throw_value.clone()),
        )),
    };
    loop {
        let (head, tail) = split_next_source_operation(&handler_source).map_err(|message| {
            ClickError::new(format!(
                "{claim_label} tactic {tactic_index}: `{tactic_name}` failed to enter its exception handler: {message}"
            ))
        })?;
        if !matches!(head, ProgramStatement::Skip) {
            break;
        }
        let Some(tail) = tail else {
            break;
        };
        handler_source = Arc::new(tail);
    }
    execution.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: handler_source,
    };
    execution.core.frontier.next_statement_index = handler.handler_first_index;
    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        handler.handler_first_index,
        ProgramPointKind::Entry,
        state,
    );
    Ok(true)
}

#[cfg(test)]
thread_local! {
    static PLANNING_STATEMENT_TRANSITIONS: std::cell::RefCell<Vec<(String, usize, String)>> = const {
        std::cell::RefCell::new(Vec::new())
    };
}

/// Records a statement step whose checking derived a prerequisite by a
/// search the proof does not retain.
#[cfg(test)]
pub(in crate::surface::proof) fn record_planning_statement_transition(
    claim: &str,
    tactic_index: usize,
    tactic: &str,
) {
    PLANNING_STATEMENT_TRANSITIONS.with(|transitions| {
        transitions
            .borrow_mut()
            .push((claim.to_string(), tactic_index, tactic.to_string()));
    });
}

#[cfg(test)]
pub(super) fn count_planning_statement_transitions<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    let result = operation();
    let after = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    (result, after - before)
}

#[cfg(test)]
pub(super) fn collect_planning_statement_transitions<R>(
    operation: impl FnOnce() -> R,
) -> (R, Vec<(String, usize, String)>) {
    let before = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    let result = operation();
    let transitions =
        PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow()[before..].to_vec());
    (result, transitions)
}

pub(super) fn execute_step_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    loop_step_policy: LoopStepPolicy,
) -> Result<Vec<Proposition>, ClickError> {
    execute_step_from_frontier_position_selecting_path(
        execution,
        proof_context,
        available_pure_facts,
        tactic_name,
        prerequisite_policy,
        loop_step_policy,
        None,
        None,
        None,
    )
}

pub(super) struct ExecutionPointStepSuccessor {
    pub(super) execution: ExecutionProofState,
    pub(super) pure_facts: PureFactList,
    pub(super) introduced_facts: Vec<Proposition>,
}

/// The checked frontier and the two direct outcomes of a call whose throw
/// edge is caught by an active transparent `try` continuation.  This is a
/// preparation result only: the proof-object layer owns publishing the two
/// descendants and joining their certificates.
pub(super) struct PreparedCallOutcomeSplit {
    pub(super) execution: ExecutionProofState,
    pub(super) execution_start_state: ExecutionState,
    pub(super) current_state: ExecutionState,
    pub(super) statement_index: usize,
    pub(super) statement: ProgramStatement,
    pub(super) source_frontier_position: FrontierPosition,
    pub(super) source_frontier_index: usize,
    pub(super) continuation_index: usize,
    pub(super) continuation_remaining: Option<ProgramStatement>,
    pub(super) next_opaque_call: u64,
    pub(super) next_kernel_variable: u64,
    pub(super) transitions: Vec<crate::surface::CertifiedStatementTransition>,
}

/// Descend through transparent try/catch syntax when necessary, then certify
/// the direct call at its frontier without mutating the caller's proof state.
/// It also accepts a frontier that `step()` has already entered, provided the
/// active exceptional continuation is still present. Ordinary `step()` still
/// uses the one-successor path below; this helper exists only for the explicit
/// proof-object outcome split.
pub(super) fn prepare_call_outcome_split(
    execution: &ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &PureFactList,
    context: Option<&PureFactContext>,
    tactic_name: &str,
) -> Result<Option<PreparedCallOutcomeSplit>, ClickError> {
    let mut prepared = execution.clone();
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;
    let mut statement_index = prepared.core.frontier.next_statement_index;
    let source_frontier_position = prepared.core.frontier.position.clone();
    let source_frontier_index = statement_index;
    let mut source_region = proof_context
        .constants
        .source_layout
        .statement(statement_index)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve region({statement_index})"
            ))
        })?;
    let (execution_start_state, current_state, mut statement, mut remaining) =
        next_top_level_statement_from_frontier_position(
            prepared.view(),
            &prepared.core.state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;

    while let Some((try_body, entry, handler)) = exceptional_region(&statement) {
        let SourceStatementKind::Try {
            try_statement_index,
            handler_statement_index,
            after_try_statement_index,
            ..
        } = source_region.kind
        else {
            break;
        };
        prepared
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                loop_control: None,
                remaining: remaining.map(Arc::new),
                next_statement_index: after_try_statement_index,
                exceptional: Some(ExceptionalContinuation {
                    entry,
                    handler,
                    handler_first_index: handler_statement_index,
                }),
            });
        remaining = Some(try_body.clone());
        statement_index = try_statement_index;
        source_region = proof_context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve region({statement_index})"
                ))
            })?;
        (statement, remaining) = split_next_source_operation(
            remaining
                .as_ref()
                .expect("try descent installed a try-body source"),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
            ))
        })?;
    }
    if !matches!(
        statement,
        ProgramStatement::Call { .. }
            | ProgramStatement::CallConstruct { .. }
            | ProgramStatement::CallResult { .. }
    ) {
        return Ok(None);
    }
    // Without an active handler the throw leaves the function: the threw arm
    // ends at function exit with that throw outcome, while the returned arm
    // continues with the rest of the function.
    // The preparation may have started at `FunctionEntry`. Re-present the
    // exact call source as a normal statement frontier for the arm's cursor;
    // the original container is retained separately for evidence matching.
    prepared.core.frontier.next_statement_index = statement_index;
    prepared.core.frontier.execution_start_state = Some(execution_start_state.clone());
    prepared.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: match remaining.clone() {
            Some(tail) => Arc::new(ProgramStatement::seq(
                Arc::new(statement.clone()),
                Arc::new(tail),
            )),
            None => Arc::new(statement.clone()),
        },
    };
    prepared.core.state = current_state.clone().into();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let mut next_opaque_call = prepared.core.next_opaque_call;
    let mut next_kernel_variable = prepared.core.kernel_variable_mark();
    let (transitions, _) = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &statement,
        proof_context.function_environment,
        Some(proof_context.spec_definitions.predicates),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut next_opaque_call,
        &mut next_kernel_variable,
        StatementPrerequisitePolicy::Retained,
        context,
    )?;
    let normal = transitions
        .iter()
        .filter(|transition| matches!(transition.outcome, StatementOutcome::Normal(_)))
        .count();
    let thrown = transitions
        .iter()
        .filter(|transition| matches!(transition.outcome, StatementOutcome::Throw { .. }))
        .count();
    if normal != 1 || thrown != 1 || transitions.len() != 2 {
        return Ok(None);
    }
    Ok(Some(PreparedCallOutcomeSplit {
        execution: prepared,
        execution_start_state,
        current_state,
        statement_index,
        statement,
        source_frontier_position,
        source_frontier_index,
        continuation_index: source_region.continuation_node,
        continuation_remaining: remaining,
        next_opaque_call,
        next_kernel_variable,
        transitions,
    }))
}

/// The checked value of a call whose result is used by the program.
pub(super) fn checked_returned_call_value(
    statement: &ProgramStatement,
    state: &ExecutionState,
) -> Option<StoredExecutionValue> {
    match statement {
        ProgramStatement::CallConstruct { target, .. } => state.locals().get(target),
        ProgramStatement::CallResult { call, .. } => state.step_result(*call),
        _ => None,
    }
    .cloned()
}

fn record_call_parameters(
    execution: &mut ExecutionProofState,
    function_block: &FunctionBlock,
    statement_index: usize,
    call_parameters: Option<&crate::kernel::CallParameters>,
) {
    if let Some(parameters) = call_parameters {
        record_statement_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            statement_index,
            ProgramPointKind::Parameters,
            parameters.state().clone(),
        );
        execution.presentation.surface_record.last_call_parameters = Some(ProgramPointRef {
            region: CodeRegionRef::Region(statement_index),
            kind: ProgramPointKind::Parameters,
        });
    }
}

/// Record one of the two transitions retained by
/// [`prepare_call_outcome_split`].  This is intentionally a recorder, not an
/// evaluator: the theorem, outcome, facts, and borrow evidence all come from
/// the one checked transition list produced during preparation.
pub(super) fn apply_prepared_call_outcome_transition(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    introduced_facts: &mut Vec<Proposition>,
    prepared: &PreparedCallOutcomeSplit,
    transition: &crate::surface::CertifiedStatementTransition,
    context: Option<&PureFactContext>,
) -> Result<(), ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let function_environment = proof_context.function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `outcomes`");

    // Record the selected theorem against the original try wrapper. Matching
    // it against the synthetic call-only cursor would bypass the kernel's
    // validated try descent and leave the next source undefined.
    execution.core.frontier.position = prepared.source_frontier_position.clone();
    execution.core.frontier.next_statement_index = prepared.source_frontier_index;
    execution.core.next_opaque_call = prepared.next_opaque_call;
    execution
        .core
        .advance_kernel_variable_mark(prepared.next_kernel_variable)
        .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        prepared.statement_index,
        ProgramPointKind::Entry,
        prepared.current_state.clone(),
    );
    execution
        .presentation
        .record_generated_load_bindings(&transition.generated_load_bindings);
    execution
        .presentation
        .record_generated_load_source_events(&transition.generated_load_source_events);
    let footprint_bound = execution
        .core
        .record_statement_transition_with_descent(
            function,
            arguments,
            &transition.native_step,
            transition.context.clone(),
            &transition.execution_facts,
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "{transition_label}: recorded call outcome evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, ParameterBinding::new(parameters, arguments))
            ))
        })?;
    execution
        .presentation
        .recorded_states
        .record_effect(execution.core.last_footprint.as_ref());
    append_execution_effect_facts(
        &mut execution.core.effect_facts,
        &transition.execution_facts,
    );
    introduced_facts.extend(transition.introduced_facts.iter().cloned());
    let mut successor_pure_facts = transition.pure_facts.clone();
    successor_pure_facts.extend(footprint_bound.iter().cloned());
    introduced_facts.extend(footprint_bound);

    let (next_state, is_throw) = match &transition.outcome {
        StatementOutcome::Normal(state) => (state.clone(), false),
        StatementOutcome::Throw { state, .. } => (state.clone(), true),
        _ => {
            return Err(ClickError::new(
                "`outcomes` received a non-returned/non-thrown call transition",
            ));
        }
    };
    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        prepared.statement_index,
        ProgramPointKind::Exit,
        *next_state.clone(),
    );

    record_call_parameters(
        execution,
        function_block,
        prepared.statement_index,
        transition.call_parameters.as_ref(),
    );

    if is_throw {
        let StatementOutcome::Throw { value, state } = &transition.outcome else {
            unreachable!("the outcome was checked as a throw");
        };
        if !route_throw_to_handler(
            execution,
            proof_context,
            available_pure_facts,
            introduced_facts,
            function,
            ParameterBinding::new(parameters, arguments),
            function_block,
            function_environment,
            claim_label,
            tactic_index,
            "outcomes",
            StatementPrerequisitePolicy::Retained,
            context,
            &value.native(),
            state,
            &successor_pure_facts,
        )? {
            // No handler: the throw is this path's function outcome.
            record_completed_continuation_exits(&mut execution.core.frontier);
            // Over a proof context the transition's facts are only what the
            // call added; the return is decided under that context with them.
            let return_assumptions = match context {
                Some(context) => successor_pure_facts
                    .iter()
                    .fold(context.clone(), |assumptions, fact| {
                        assumptions.assume_proposition(fact.clone())
                    }),
                None => successor_pure_facts.context(),
            };
            let case_outcomes =
                crate::kernel::program_function_outcomes_from_statement_outcome_with_resource_cases(
                    &prepared.execution_start_state,
                    function,
                    arguments,
                    transition.outcome.clone(),
                    transition.obligations.clone(),
                    &return_assumptions,
                );
            let mut completed_outcomes = Vec::new();
            for (outcome, obligations, case_facts) in case_outcomes {
                let mut completed_execution_facts =
                    completed_execution_facts(&execution.core, &transition.execution_facts);
                for fact in case_facts {
                    completed_execution_facts.push(ExecutionPureFact::new(fact));
                }
                completed_outcomes.push((
                    outcome,
                    completed_execution_facts,
                    obligations,
                    execution.core.borrow_evidence().clone(),
                ));
            }
            append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
            *available_pure_facts = successor_pure_facts;
            let completed =
                crate::kernel::program_function_execution_candidates_from_completed_outcomes(
                    prepared.execution_start_state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    completed_outcomes,
                );
            set_function_exit_execution(
                &mut execution.core.frontier,
                claim_label,
                tactic_index,
                "outcomes",
                prepared.execution_start_state.clone(),
                completed,
            )?;
            execution.core.frontier.next_statement_index = prepared.continuation_index;
            execution.core.state = prepared.execution_start_state.clone().into();
        }
        return Ok(());
    }

    *available_pure_facts = successor_pure_facts;
    execution.core.frontier.execution_start_state = Some(prepared.execution_start_state.clone());
    execution.core.state = (*next_state.clone()).into();
    let remaining = if let Some(remaining) = prepared.continuation_remaining.clone() {
        execution.core.frontier.next_statement_index = prepared.continuation_index;
        Some(remaining)
    } else {
        resume_after_completed_region(&mut execution.core.frontier)
    };
    match remaining {
        Some(remaining) => {
            execution.core.frontier.position = FrontierPosition::StatementEntry {
                remaining: remaining.into(),
            };
            record_statement_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                execution.core.frontier.next_statement_index,
                ProgramPointKind::Entry,
                *next_state,
            );
        }
        None if finish_exhausted_region(&mut execution.core.frontier) => {}
        None => {
            return Err(ClickError::new(
                "`outcomes` returned from a call without a following source statement",
            ));
        }
    }
    Ok(())
}

/// Executes one source statement into one checked proof successor.
///
/// Execution uncertainty stays inside the symbolic kernel state. Only an
/// explicit proof `if`, C `branch`, or loop construct may change the number of
/// proof goals; a linear statement step never publishes hidden siblings.
#[allow(clippy::too_many_arguments)]
pub(super) fn execute_step_successor_from_frontier_position(
    execution: &ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    loop_step_policy: LoopStepPolicy,
    context: Option<&PureFactContext>,
) -> Result<ExecutionPointStepSuccessor, ClickError> {
    let mut successor = execution.clone();
    let mut successor_facts = available_pure_facts.clone();
    let introduced_facts = execute_step_from_frontier_position_selecting_path(
        &mut successor,
        proof_context,
        &mut successor_facts,
        tactic_name,
        prerequisite_policy,
        loop_step_policy,
        None,
        context,
        None,
    )?;
    Ok(ExecutionPointStepSuccessor {
        execution: successor,
        pure_facts: successor_facts,
        introduced_facts,
    })
}

/// Prefer parameter-relative places; where those leave a value unnamed, try
/// the locals live before the operation too. Recognize the shared printer's
/// explicit placeholders as well as legacy source-place elisions.
fn describe_runtime_error_before_statement(
    error: &crate::kernel::RuntimeError,
    state: &ExecutionState,
    function: &crate::languages::interface::ImportedFunction,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let missing_names = |text: &str| {
        text.matches('…').count()
            + text.matches("<pointer ").count()
            + text.matches("<unnamed ").count()
    };
    let over_parameters = describe_runtime_error(error, parameter_binding);
    let missing_parameters = missing_names(&over_parameters);
    if missing_parameters == 0 {
        return over_parameters;
    }
    let (locals, local_values) =
        crate::surface::diagnostics::local_naming_tables_with_source(state, Some(function));
    let mut names = parameter_binding.parameters.to_vec();
    let mut values = parameter_binding.arguments.to_vec();
    names.extend(locals);
    values.extend(local_values);
    let over_locals = describe_runtime_error(error, ParameterBinding::new(&names, &values));
    if missing_names(&over_locals) < missing_parameters {
        over_locals
    } else {
        over_parameters
    }
}

#[allow(clippy::too_many_arguments)]
fn execute_step_from_frontier_position_selecting_path(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    loop_step_policy: LoopStepPolicy,
    selected_path_fact: Option<&Proposition>,
    context: Option<&PureFactContext>,
    path_cases: Option<&mut Vec<CertifiedStatementTransition>>,
) -> Result<Vec<Proposition>, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let parameter_binding = proof_context.parameter_binding();
    let function_environment = proof_context.function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let checked_call_events = execution.core.checked_call_events();
    let _checked_call_event_scope = CheckedCallEventScope::start(&checked_call_events);

    let state: &mut ExecutionState = &mut execution.core.state;

    let mut statement_index = execution.core.frontier.next_statement_index;
    let _site_scope = crate::surface::diagnostics::StatementSiteScope::enter(
        &proof_context.constants.source_layout,
        statement_index,
        proof_context.parsed_function,
    );
    let (execution_start_state, current_state, mut source_statement, mut remaining) =
        next_top_level_statement_from_frontier_position(
            ExecutionView::new(
                &execution.core.frontier,
                &execution.presentation.recorded_states,
                &execution.presentation.surface_propositions,
            ),
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    if function_block.one_call_proof
        && matches!(
            execution.core.frontier.position,
            FrontierPosition::FunctionEntry
        )
    {
        source_statement = function.body().clone();
        remaining = None;
    }
    // Descend into `try` bodies transparently so an implicit cleanup call
    // inside one is its own steppable statement. Only the typed C++ frontend
    // produces `TryCatchInt32` (and only it gets the `Try` layout kind), so
    // C stepping never takes this branch. The handler continuation lets a
    // later `Throw` resume at the handler entry instead of terminating the
    // path; normal completion pops it with the tail like any other
    // continuation.
    let mut source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve region({statement_index})"
        ))
    })?;
    let is_test = matches!(source_statement, ProgramStatement::LoopTest { .. });
    let test_owner = is_test
        .then(|| execution.core.frontier.active_loop_phase_source())
        .flatten();
    let hidden_test = is_test
        && proof_context
            .constants
            .source_layout
            .is_hidden_loop_test(statement_index);
    let phase_source = hidden_test.then_some(test_owner).flatten();
    if function_environment.selected_call_contract.is_some()
        && !matches!(source_region.kind, SourceStatementKind::Plain)
    {
        return Err(ClickError::new(
            "step(Contract) requires a call at the current frontier",
        ));
    }
    if let Some(transport) = &function_environment.selected_call_binders
        && !matches!(
            source_region.kind,
            SourceStatementKind::Plain | SourceStatementKind::Try { .. }
        )
    {
        return Err(ClickError::new(format!(
            "`step({}, {{ ... }})` requires a call to `{}` at the current frontier",
            transport.function, transport.function
        )));
    }
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            "step",
            None,
            prerequisite_policy,
            false,
            context,
        )?;
        debug_assert!(entered);
        return Ok(Vec::new());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain
        | SourceStatementKind::If { .. }
        | SourceStatementKind::Try { .. } => None,
    };
    let mut descended_try = false;
    while let Some((try_body, entry, handler)) = exceptional_region(&source_statement) {
        let (try_first, handler_first, after_try) = match source_region.kind {
            SourceStatementKind::Try {
                try_statement_index,
                handler_statement_index,
                after_try_statement_index,
                ..
            } => (
                try_statement_index,
                handler_statement_index,
                after_try_statement_index,
            ),
            _ => break,
        };
        descended_try = true;
        execution
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                loop_control: None,
                remaining: remaining.map(Arc::new),
                next_statement_index: after_try,
                exceptional: Some(ExceptionalContinuation {
                    entry,
                    handler,
                    handler_first_index: handler_first,
                }),
            });
        remaining = Some(try_body.clone());
        statement_index = try_first;
        source_region = proof_context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve region({statement_index})"
                ))
            })?;
        (source_statement, remaining) = split_next_source_operation(
            remaining
                .as_ref()
                .expect("try-body descent just set a remaining statement"),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
            ))
        })?;
    }
    if matches!(source_statement, ProgramStatement::Loop { .. }) && loop_index.is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source loop at region({statement_index})"
        )));
    }
    if let (Some(loop_index), ProgramStatement::Loop { .. }) = (loop_index, &source_statement)
        && matches!(loop_step_policy, LoopStepPolicy::EnterBody)
    {
        execute_concrete_loop_head_step(
            execution,
            proof_context,
            available_pure_facts,
            tactic_name,
            prerequisite_policy,
            statement_index,
            loop_index,
            source_region.continuation_node,
            execution_start_state,
            current_state,
            source_statement,
            remaining,
            context,
        )?;
        return Ok(Vec::new());
    }
    let step_statement = source_statement;
    if function_environment.selected_call_contract.is_some()
        && !statement_contains_call(&step_statement)
    {
        return Err(ClickError::new(
            "step(Contract) requires a call at the current frontier",
        ));
    }
    // The step names the call it binds, so the statement the frontier is about
    // to run has to be that call: one comparison against the statement, not a
    // search for a matching call.
    if let Some(transport) = &function_environment.selected_call_binders {
        // A non-void one-call theorem runs its generated call and return
        // together. Validate the selected binder map against that one
        // leading call, not against the sequence wrapper. Ordinary C steps
        // still require a call at the exact frontier.
        let selected_statement = if function_block.one_call_proof
            && matches!(
                execution.core.frontier.position,
                FrontierPosition::FunctionEntry
            )
            && let ProgramStatement::Seq(statements) = &step_statement
        {
            statements.first().as_ref()
        } else {
            &step_statement
        };
        let called = match selected_statement {
            ProgramStatement::Call {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallConstruct {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallResult {
                function_name,
                arguments,
                ..
            } => Some((function_name.as_str(), arguments.len())),
            _ => None,
        };
        match called {
            Some((name, arity))
                if transport.names_call_to(name)
                    || function_environment.selected_call_contract.as_deref()
                        == Some(transport.function.as_ref()) =>
            {
                if arity != transport.arity {
                    return Err(ClickError::new(format!(
                        "`{name}` is called with {arity} argument(s) here, but the step writes {}",
                        transport.arity
                    )));
                }
            }
            _ => {
                return Err(ClickError::new(format!(
                    "`step({}, {{ ... }})` requires a call to `{}` at the current frontier; next operation: {}",
                    transport.function,
                    transport.function,
                    describe_statement_head(&step_statement)
                )));
            }
        }
    }

    // The surface step for this statement is written from the proof state
    // *before* the statement runs. Its own check establishes this
    // statement's entry states only while re-executing it, so construction
    // must see the program points exactly as they were before these entry
    // recordings: points the recording adds or overwrites here are presented
    // at their prior value (or absence) while the step is written.
    let mut construction_regions = vec![CodeRegion::Statement(statement_index)];
    if let Some(loop_index) = loop_index {
        construction_regions.push(CodeRegion::Loop(loop_index));
    }
    record_statement_program_state(
        &mut execution.presentation.recorded_states,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(loop_index) = loop_index {
        record_loop_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            loop_index,
            ProgramPointKind::Entry,
            current_state.clone(),
        );
    }
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let next_opaque_call_before_step = execution.core.next_opaque_call;
    // The kernel owns the counter: the step reads a copy, the evaluation
    // advances it, and the checked setter installs the result.
    let mut stepped_kernel_variable = execution.core.kernel_variable_mark();
    let mut transitions = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &step_statement,
        function_environment,
        Some(proof_context.spec_definitions.predicates),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut execution.core.next_opaque_call,
        &mut stepped_kernel_variable,
        prerequisite_policy,
        context,
    )?
    .0;
    execution
        .core
        .advance_kernel_variable_mark(stepped_kernel_variable)
        .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
    if let Some(selected_path_fact) = selected_path_fact {
        transitions.retain(|transition| transition.path_facts.contains(selected_path_fact));
    }
    // A summarized loop whose body may `return` has one continuing successor,
    // the join of its guard-false and `break` exits or its natural forward
    // jump, and one terminal
    // successor per returned path. The step follows the continuing one; each
    // returned path is retained as an already-completed path of this
    // execution and joins the function's exit paths at the boundary, where
    // its postcondition and resource obligations are checked on the value
    // and state it returned. A loop whose every successor returns completes
    // the frontier below like any other terminal operation.
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(planned) =
            loop_index.and_then(|index| execution.presentation.loop_return_proofs.get(&index))
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, StatementOutcome::Return { .. }))
            .count()
            != planned.paths.len()
    {
        return Err(ClickError::new(
            "checked loop return outcomes do not align with their preservation proofs",
        ));
    }
    let mut loop_return_transitions = Vec::new();
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && transitions.len() > 1
        && transitions
            .iter()
            .filter(|transition| {
                matches!(
                    transition.outcome,
                    StatementOutcome::Normal(_) | StatementOutcome::Jump { .. }
                )
            })
            .count()
            == 1
        && transitions.iter().all(|transition| {
            matches!(
                transition.outcome,
                StatementOutcome::Normal(_)
                    | StatementOutcome::Jump { .. }
                    | StatementOutcome::Return { .. }
            )
        })
    {
        let (returned, continuing): (Vec<_>, Vec<_>) = transitions
            .into_iter()
            .partition(|transition| matches!(transition.outcome, StatementOutcome::Return { .. }));
        transitions = continuing;
        loop_return_transitions = returned;
    }
    if transitions.len() > 1
        && transitions.iter().all(|transition| {
            matches!(
                transition.outcome,
                StatementOutcome::Return { .. } | StatementOutcome::Throw { .. }
            )
        })
    {
        // One checked source operation can have several completed outcomes,
        // including a terminal direct call followed by a return.
        // Preserve every theorem with its own outcome for contract closing.

        let mut common_pure_facts = transitions[0].pure_facts.clone();
        common_pure_facts.retain_from(available_pure_facts, |fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.pure_facts.contains(fact))
        });
        let mut common_introduced_facts = transitions[0].introduced_facts.clone();
        common_introduced_facts.retain(|fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.introduced_facts.contains(fact))
        });
        execution
            .core
            .record_statement_outcomes_with_descent(
                function,
                arguments,
                &transitions
                    .iter()
                    .map(|transition| {
                        (
                            transition.native_step.as_ref(),
                            &transition.execution_facts,
                        )
                    })
                    .collect::<Vec<_>>(),
                transitions[0].context.clone(),
            )
            .map_err(|refusal| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded statement evidence the proof object rejected: {}",
                    describe_evidence_refusal(&refusal, parameter_binding)
                ))
            })?;
        let generated_load_source_events = transitions
            .iter()
            .flat_map(|transition| transition.generated_load_source_events.iter())
            .cloned()
            .collect::<Vec<_>>();
        for transition in &transitions {
            execution
                .presentation
                .record_generated_load_bindings(&transition.generated_load_bindings);
        }
        // A loop whose every successor returns leaves no continuing state
        // to record its exit at; one returned state binds the iteration
        // identities every returned path's facts are stated over.
        let loop_return_exit_state = loop_index.and_then(|_| {
            transitions
                .iter()
                .find_map(|transition| match &transition.outcome {
                    StatementOutcome::Return { state, .. } => Some((**state).clone()),
                    _ => None,
                })
        });
        let mut completed_outcomes = Vec::new();
        let mut terminal_cases = Vec::new();
        let retain_terminal_cases = matches!(step_statement, ProgramStatement::Return(_));
        for transition in transitions {
            let return_assumptions = transition.pure_facts.context();
            let case_outcomes =
                crate::kernel::program_function_outcomes_from_statement_outcome_with_resource_cases(
                    &execution_start_state,
                    function,
                    arguments,
                    transition.outcome.clone(),
                    transition.obligations.clone(),
                    &return_assumptions,
                );
            for (outcome, obligations, case_facts) in case_outcomes {
                let mut completed_execution_facts =
                    completed_execution_facts(&execution.core, &transition.execution_facts);
                for fact in case_facts {
                    completed_execution_facts.push(ExecutionPureFact::new(fact));
                }
                terminal_cases.push(transition.path_facts.clone());
                completed_outcomes.push((
                    outcome,
                    completed_execution_facts,
                    obligations,
                    crate::kernel::concat_checked_borrow_evidence(
                        execution.core.borrow_evidence(),
                        &transition.borrow_evidence,
                    ),
                ));
            }
        }
        if retain_terminal_cases {
            execution.retain_terminal_statement_cases(
                terminal_cases,
                current_state.clone(),
                ProgramPointRef {
                    region: CodeRegionRef::Region(statement_index),
                    kind: ProgramPointKind::Entry,
                },
            );
        }
        append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
        let state: &mut ExecutionState = &mut execution.core.state;
        let completed =
            crate::kernel::program_function_execution_candidates_from_completed_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                completed_outcomes,
            );
        if let (Some(loop_index), Some(exit_state)) = (loop_index, loop_return_exit_state) {
            record_loop_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                exit_state,
            );
            execution.presentation.surface_record.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            });
        }
        let execution_state = execution_start_state.clone();
        set_function_exit_execution(
            &mut execution.core.frontier,
            claim_label,
            tactic_index,
            tactic_name,
            execution_start_state,
            completed,
        )?;
        execution.core.frontier.next_statement_index = source_region.continuation_node;
        *available_pure_facts = common_pure_facts;
        *state = execution_state;
        execution
            .presentation
            .record_generated_load_source_events(&generated_load_source_events);
        return Ok(common_introduced_facts);
    }
    if selected_path_fact.is_none()
        && matches!(
            step_statement,
            ProgramStatement::Call { .. }
                | ProgramStatement::CallConstruct { .. }
                | ProgramStatement::CallResult { .. }
        )
        && transitions.len() == 2
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, StatementOutcome::Normal(_)))
            .count()
            == 1
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, StatementOutcome::Throw { .. }))
            .count()
            == 1
    {
        // A maybe-throwing call has two successors, like an undecided C
        // `if`: each is its own proof arm, so one linear step cannot take
        // both.
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached `{}`, which may throw; its returned and threw successors are separate proof arms. Write `outcomes {{ returned => {{ ... }} threw => {{ ... }} }}` here, or end the script here and let its implicit tail split it",
            describe_statement_head(&step_statement)
        )).with_call_outcomes_split());
    }
    // A statement whose checked successors differ only in their path facts
    // -- a load that may or may not read the cell an earlier store wrote --
    // is one C operation with several cases. A step never publishes those
    // cases as hidden siblings; a planner that asks for them receives them
    // unchanged and splits the proof on their conditions. Nothing has been
    // committed yet, so the caller runs the statement again from this
    // frontier on each side of that split.
    if transitions.len() > 1
        && !descended_try
        && let Some(path_cases) = path_cases
        && statement_successors_are_path_cases(&transitions)
    {
        execution.core.next_opaque_call = next_opaque_call_before_step;
        *path_cases = transitions;
        return Ok(Vec::new());
    }
    // Assertion failures already supplied their obligations above. During
    // preparation retain the unique successful arm; the driver proves the
    // assertion at input before this conditional successor can be published.
    if crate::surface::proof::execution_planning::collecting_step_requirements()
        && matches!(step_statement, ProgramStatement::Assert { .. })
        && transitions
            .iter()
            .all(|transition| matches!(transition.outcome, StatementOutcome::Normal(_)))
    {
        let succeeds = |transition: &CertifiedStatementTransition| {
            !transition
                .obligations
                .iter()
                .any(ProofObligation::is_assertion_failure)
        };
        if transitions
            .iter()
            .filter(|transition| succeeds(transition))
            .count()
            == 1
        {
            transitions.retain(succeeds);
        }
    }
    'select_prepared: {
        if transitions.len() != 1 {
            if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
                let safe = transitions
                    .iter()
                    .filter(|transition| {
                        matches!(
                            transition.outcome,
                            StatementOutcome::Normal(_) | StatementOutcome::Return { .. }
                        )
                    })
                    .collect::<Vec<_>>();
                if let [safe] = safe.as_slice()
                    && let Some(required) = safe
                        .pure_facts
                        .iter()
                        .find(|fact| !exact_fact_is_available(fact, available_pure_facts))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` is missing exact prerequisite needed to select the safe statement transition: `{}`",
                        crate::surface::diagnostics::describe_stated_fact_over_locals(
                            required,
                            &current_state
                        )
                    )));
                }
            }
            if let Some(kind) =
                transitions
                    .iter()
                    .find_map(|transition| match &transition.outcome {
                        StatementOutcome::UndefinedBehavior(kind) => Some(kind.clone()),
                        _ => None,
                    })
            {
                // The goal is the path condition of the one defined transition
                // that the available facts do not already state.
                let mut defined = transitions.iter().filter(|transition| {
                    matches!(
                        transition.outcome,
                        StatementOutcome::Normal(_) | StatementOutcome::Return { .. }
                    )
                });
                // One definedness check (a shift count in range) can need
                // several of the path's facts; together they are its one goal.
                let goal = match (defined.next(), defined.next()) {
                    (Some(defined), None) => defined
                        .path_facts
                        .iter()
                        .filter(|fact| !exact_fact_is_available(fact, available_pure_facts))
                        .cloned()
                        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right))),
                    _ => None,
                };
                if crate::surface::proof::execution_planning::collecting_step_requirements()
                    && transitions.iter().all(|transition| {
                        matches!(
                            transition.outcome,
                            StatementOutcome::Normal(_)
                                | StatementOutcome::Return { .. }
                                | StatementOutcome::UndefinedBehavior(_)
                        )
                    })
                    && let Some(goal) = goal.as_ref()
                {
                    // Construct the obligation from the selected path's delta.
                    // Failure-site diagnostics may re-evaluate expressions;
                    // they do not belong on successful preparation.
                    crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires proof excluding {}{}", kind.description(), crate::surface::diagnostics::describe_execution_statement_site()
                        )).with_statement_safety_goal(goal.clone()),
                    )?;
                    transitions.retain(|transition| {
                        matches!(
                            transition.outcome,
                            StatementOutcome::Normal(_) | StatementOutcome::Return { .. }
                        )
                    });
                    break 'select_prepared;
                }
                let site = crate::surface::diagnostics::describe_undefined_behavior_site(
                    &current_state,
                    &step_statement,
                    &context
                        .cloned()
                        .unwrap_or_else(|| available_pure_facts.context()),
                    &kind,
                );
                let required = kind.required_goal().cloned();
                let refusal_kind =
                    crate::surface::diagnostics::undefined_behavior_refusal_kind(&kind);
                let outcome = FunctionOutcome::UndefinedBehavior(kind);
                let error = ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}{site}{}\n{}",
                    describe_function_outcome(&outcome, parameter_binding),
                    crate::surface::diagnostics::describe_execution_statement_site(),
                    if required.is_some() {
                        // The structured diagnostic supplies the facts/resources
                        // with the goal's label map. An embedded context dump
                        // would introduce a second, conflicting set of labels.
                        String::new()
                    } else {
                        describe_step_proof_context(
                            available_pure_facts,
                            context,
                            step_diagnostic_resources(&current_state),
                            parameter_binding,
                            &[],
                        )
                    }
                ));
                let error = error
                    .with_reported_assertion_goal(required)
                    .with_kind(refusal_kind)
                    .with_proof_refusal(crate::surface::ProofRefusal::Tactic);
                let Some(goal) = goal else {
                    return Err(error);
                };
                // Definedness is one of the statement's requirements, like a
                // callee's precondition: a probing step records it as an open
                // obligation, so a `step() by { ... }` body or the implicit
                // `solve` proves it at the pre-state. Retain that already evaluated
                // transition instead of executing the statement a second time.
                let error = error.with_statement_safety_goal(goal);
                crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                    error.clone(),
                )?;
                return Err(error);
            }
            if let Some(error) =
                transitions
                    .iter()
                    .find_map(|transition| match &transition.outcome {
                        StatementOutcome::RuntimeError(error) => Some(error),
                        _ => None,
                    })
            {
                let kind = runtime_refusal_kind(error);
                let unsupported = kind == crate::surface::ClickErrorKind::Internal;
                let description = if unsupported {
                    "reached an unsupported modeled operation"
                } else {
                    "could not verify C operation"
                };
                let resources = step_diagnostic_resources(&current_state);
                let detail = crate::surface::diagnostics::describe_unestablished_assembly_fact(
                    error,
                    &listed_context_pure_facts(available_pure_facts, context),
                    resources,
                    parameter_binding,
                    &[],
                )
                .unwrap_or_else(|| {
                    format!(
                        "{}{}",
                        describe_runtime_error_before_statement(
                            error,
                            &current_state,
                            proof_context.parsed_function,
                            parameter_binding,
                        ),
                        describe_missing_range_end_note(
                            error,
                            resources,
                            Some(&current_state),
                            parameter_binding
                        )
                    )
                });
                if matches!(
                    error,
                    crate::kernel::RuntimeError::UninitializedMutex { .. }
                        | crate::kernel::RuntimeError::UnsupportedConcurrentMutex
                ) {
                    return Err(ClickError::new(detail)
                        .with_kind(kind)
                        .with_proof_refusal(crate::surface::ProofRefusal::Tactic));
                }
                return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` {description}: {}\n  C operation: {}{}{}\n{}",
                detail,
                describe_statement_head(&step_statement),
                describe_call_bindings(&step_statement, function_environment),
                crate::surface::diagnostics::describe_execution_statement_site(),
                describe_step_proof_context(
                available_pure_facts, context,
                    resources,
                    parameter_binding,
                    &[]
                )
            ))
            .with_kind(kind)
            .with_runtime_missing_resource(error)
            .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(error)));
            }
            let path_case_split = statement_successors_are_path_cases(&transitions);
            let split_condition = if path_case_split {
                let cases = transitions
                    .iter()
                    .map(PathCase::of_statement)
                    .collect::<Vec<_>>();
                path_case_split_condition(
                    &cases,
                    &|fact| available_pure_facts.contains(fact),
                    &current_state,
                    proof_context,
                )
                .map(|(_, condition)| condition)
            } else {
                None
            };
            let case_split_guidance = if path_case_split {
                describe_path_case_split_guidance(split_condition.as_ref(), transitions.len())
            } else {
                String::new()
            };
            let error = ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor for `{}`, got {}{}\n{}{}{}{}",
                describe_execution_statement_head(&step_statement),
                transitions.len(),
                crate::surface::diagnostics::describe_execution_statement_site(),
                describe_undecided_statement_successors(&transitions, parameter_binding),
                case_split_guidance,
                describe_multiple_statement_successors_guidance(
                    &step_statement,
                    transitions.len(),
                    transitions
                        .iter()
                        .filter(|transition| {
                            matches!(transition.outcome, StatementOutcome::Throw { .. })
                        })
                        .count()
                        == 1,
                ),
                describe_step_proof_context(
                    available_pure_facts,
                    context,
                    step_diagnostic_resources(&current_state),
                    parameter_binding,
                    &[]
                )
            ));
            return Err(match (path_case_split, split_condition) {
                (true, Some(condition)) => error.with_path_case_condition(condition),
                (true, None) => error.with_path_case_split(),
                (false, _) => error,
            });
        }
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    execution
        .presentation
        .record_generated_load_bindings(&transition.generated_load_bindings);
    let generated_load_source_events = transition.generated_load_source_events.clone();
    let mut introduced_facts = transition.introduced_facts.clone();
    // The returned paths fork from the trace as it is before the loop's
    // continuing theorem is recorded on it.
    let loop_return_parent = (!loop_return_transitions.is_empty()).then(|| execution.core.clone());
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(loop_index) = loop_index
        && matches!(transition.outcome, StatementOutcome::Normal(_))
        && let Some(loop_clause) = function_block.structural_clauses().for_loop(loop_index)
    {
        record_loop_exit_invariants(
            &mut execution.presentation.surface_propositions,
            loop_clause,
            &transition.loop_invariant_correspondence,
            loop_index,
        )?;
    }
    if let (Some(loop_index), Some(iterations)) = (loop_index, &transition.loop_iterations) {
        execution
            .presentation
            .recorded_states
            .record_loop_iterations_root(loop_index, iterations.clone());
    }

    let footprint_bound = execution
        .core
        .record_statement_transition_with_descent(
            function,
            arguments,
            &transition.native_step,
            transition.context.clone(),
            &transition.execution_facts,
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded statement evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameter_binding)
            ))
        })?;
    let statement_footprint = execution.core.last_footprint.clone();
    // A loop exit names the state before its enclosing scope retires locals.
    // Keep that intermediate boundary; ordinary statements include cleanup.
    if loop_index.is_some() {
        execution
            .presentation
            .recorded_states
            .record_effect(statement_footprint.as_ref());
    }
    if let Some(parent) = loop_return_parent {
        for (return_index, returned) in loop_return_transitions.into_iter().enumerate() {
            // The path's fact base: what was available at the loop, plus what
            // the returned path itself states. Nothing the continuing path
            // establishes after the loop is cited on it.
            let mut returned_facts = loop_index
                .and_then(|index| execution.presentation.loop_return_proofs.get(&index))
                .map(|planned| planned.entry_facts.clone())
                .unwrap_or_else(|| available_pure_facts.fact_store());
            for fact in returned.pure_facts.iter() {
                if !returned_facts.contains(fact) {
                    returned_facts = returned_facts.with_kernel_checked_fact(fact.clone());
                }
            }
            let (outcome, obligations) =
                crate::kernel::program_function_outcome_from_statement_outcome(
                    &execution_start_state,
                    function,
                    returned.outcome.clone(),
                    returned.obligations.clone(),
                    returned_facts.assumptions(),
                );
            let completed_execution_facts =
                completed_execution_facts(&parent, &returned.execution_facts);
            let borrow_evidence = crate::kernel::concat_checked_borrow_evidence(
                parent.borrow_evidence(),
                &returned.borrow_evidence,
            );
            execution
                .core
                .record_pending_loop_return(
                    &parent,
                    function,
                    arguments,
                    &returned.native_step,
                    &returned.context,
                    &returned.execution_facts,
                    &returned.obligations,
                    outcome,
                    completed_execution_facts.into_facts(),
                    obligations,
                    returned_facts,
                    borrow_evidence,
                    loop_index,
                    return_index,
                )
                .map_err(|refusal| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded a loop's returned path the proof object rejected: {}",
                        describe_evidence_refusal(&refusal, parameter_binding)
                    ))
                })?;
        }
    }
    // A direct memory-state transport needs no surface `transport`
    // tactic, but its target still needs a stable source form for a
    // later proof step. Record that form during both planning and
    // explicit certificate validation; otherwise check immediately forgets
    // evaluator guards such as `defined(x + 1)` that planning retained.
    let exit_point = ProgramPointRef {
        region: CodeRegionRef::Region(statement_index),
        kind: ProgramPointKind::Exit,
    };
    for transport in transition
        .fact_transports
        .iter()
        .filter(|transport| !transport.statement_local)
    {
        let surfaces = execution
            .presentation
            .surface_propositions
            .surfaces(&transport.source)
            .cloned()
            .collect::<Vec<_>>();
        for surface in surfaces {
            let exit_surface = surface_at_program_point(&surface, &exit_point)?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(&exit_surface, &transport.target)?;
        }
    }
    // Preserve a surface name for each store while its exact source statement
    // is still known. The certified equation records the address evaluated
    // before the write and the memory immediately after it; a later attempt
    // to reconstruct that name from the final state can only re-evaluate the
    // address and loses this association for deep, state-dependent indices.
    let store_exit_point = ProgramPointRef {
        region: CodeRegionRef::Region(statement_index),
        kind: ProgramPointKind::Exit,
    };
    let word_store_source = word_store_source(
        &step_statement,
        &current_state,
        &transition.outcome,
        &store_exit_point,
    )
    .filter(|_| {
        let layout = &proof_context.constants.source_layout;
        layout.automatic_exits(statement_index, false).is_empty()
            && layout.automatic_exits(statement_index, true).is_empty()
    });
    for fact in transition.execution_facts.fact_iter() {
        let Some(equation) = fact.certified_store_equation() else {
            continue;
        };
        if let Some(surface) = &word_store_source
            && let Some(address) = fact.certified_store_source_address()
            && execution
                .presentation
                .surface_propositions
                .record_store_source(equation, surface, address)
        {
            continue;
        }
        if let Some(SyntaxProposition::Comparison {
            left,
            operator,
            right,
        }) = synthesize_surface_proposition(equation, parameter_binding, &current_state)
        {
            let store_entry_point = ProgramPointRef {
                region: CodeRegionRef::Region(statement_index),
                kind: ProgramPointKind::Entry,
            };
            let at = |point: &ProgramPointRef, expression: SyntaxTerm| SyntaxTerm::At {
                selector: ProgramPointSelector::ProgramPoint(point.clone()),
                expression: Box::new(expression),
            };
            // The neutral pointer addition makes the Index use the outer
            // exit state's memory while its base and index retain their
            // entry values.
            let exit_load = if let SyntaxTerm::Index(base, index) = left {
                SyntaxTerm::Index(
                    Box::new(SyntaxTerm::Add(
                        Box::new(at(&store_entry_point, *base)),
                        Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                            int32(0),
                        ))),
                    )),
                    Box::new(at(&store_entry_point, *index)),
                )
            } else {
                left
            };
            let surface = SyntaxProposition::Comparison {
                left: at(&store_exit_point, exit_load),
                operator,
                right: at(&store_entry_point, right),
            };
            execution
                .presentation
                .surface_propositions
                .record_lowering(&surface, equation)?;
        }
    }
    let execution_pure_facts = transition.execution_facts;
    append_execution_effect_facts(&mut execution.core.effect_facts, &execution_pure_facts);
    let transition_obligations = transition.obligations;
    let mut successor_pure_facts = transition.pure_facts;
    successor_pure_facts.extend(footprint_bound.iter().cloned());
    introduced_facts.extend(footprint_bound);
    // Falling off a void function is a return in the kernel's C semantics.
    // A source-less one-call proof can reach this boundary without the
    // explicit return node normally inserted by C parsing.
    let outcome = match transition.outcome {
        StatementOutcome::Normal(state)
            if function.return_type() == crate::kernel::ProgramType::Void
                && remaining.is_none()
                && execution.core.frontier.region == ExecutionRegionKind::Function
                && execution.core.frontier.continuations.is_empty() =>
        {
            StatementOutcome::Return {
                value: ProgramValue::Void.into(),
                state,
            }
        }
        outcome => outcome,
    };
    if let Some(loop_index) = loop_index
        && let StatementOutcome::Normal(state) = &outcome
    {
        record_loop_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            loop_index,
            ProgramPointKind::Exit,
            *state.clone(),
        );
    }
    let mut outcome = outcome;
    let abrupt = !matches!(outcome, StatementOutcome::Normal(_));
    let ended = if matches!(outcome, StatementOutcome::Continue(_)) {
        proof_context
            .constants
            .source_layout
            .automatic_continue_exits(statement_index)
    } else {
        proof_context
            .constants
            .source_layout
            .automatic_exits(statement_index, abrupt)
    };
    match &mut outcome {
        StatementOutcome::Normal(state)
        | StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Return { state, .. }
        | StatementOutcome::Throw { state, .. }
        | StatementOutcome::Jump { state, .. } => {
            **state = execution
                .core
                .record_automatic_lifetime_end(state, ended)
                .map_err(|error| {
                    ClickError::new(format!(
                        "{}{}",
                        crate::surface::diagnostics::describe_runtime_error_over_locals(
                            &error, state
                        ),
                        crate::surface::diagnostics::describe_execution_statement_site(),
                    ))
                    .with_kind(runtime_refusal_kind(&error))
                    .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(&error))
                })?;
            if loop_index.is_none() {
                execution.core.last_footprint =
                    match (&statement_footprint, &execution.core.last_footprint) {
                        (Some(statement), Some(cleanup)) => Some(
                            crate::kernel::RegionFootprint::with_scope_cleanup(statement, cleanup),
                        ),
                        (Some(statement), None) => Some(statement.clone()),
                        (_, cleanup) => cleanup.clone(),
                    };
            }
        }
        _ => {}
    }
    execution
        .presentation
        .recorded_states
        .record_effect(execution.core.last_footprint.as_ref());
    if let Some(statement_exit_state) = match &outcome {
        StatementOutcome::Normal(state)
        | StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Jump { state, .. }
        | StatementOutcome::Return { state, .. }
        | StatementOutcome::Throw { state, .. } => Some(state.clone()),
        StatementOutcome::UndefinedBehavior(_) | StatementOutcome::RuntimeError(_) => None,
        StatementOutcome::VerificationDiverges => None,
    } {
        record_statement_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            *statement_exit_state,
        );
        execution
            .presentation
            .recorded_states
            .record_read_events(statement_index, &execution_pure_facts);
        record_call_parameters(
            execution,
            function_block,
            statement_index,
            transition.call_parameters.as_ref(),
        );
        if matches!(outcome, StatementOutcome::Normal(_))
            && let Some(result) = &transition.call_result
        {
            execution
                .presentation
                .recorded_states
                .record_call_transition_result(statement_index, result.clone());
        }
        if let Some(loop_index) = loop_index
            && !matches!(outcome, StatementOutcome::Normal(_))
        {
            record_loop_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    StatementOutcome::Normal(state)
                    | StatementOutcome::LoopTestFalse(state)
                    | StatementOutcome::Break(state)
                    | StatementOutcome::Continue(state)
                    | StatementOutcome::Jump { state, .. }
                    | StatementOutcome::Return { state, .. }
                    | StatementOutcome::Throw { state, .. } => *state.clone(),
                    StatementOutcome::UndefinedBehavior(_)
                    | StatementOutcome::RuntimeError(_)
                    | StatementOutcome::VerificationDiverges => unreachable!(),
                },
            );
        }
    }

    let phase_test_succeeded = hidden_test && matches!(outcome, StatementOutcome::Normal(_));
    if let (Some(owner), StatementOutcome::LoopTestFalse(state)) = (test_owner, &outcome)
        && let Some(index) = proof_context
            .constants
            .source_layout
            .loop_index_at_header(owner.header_index)
    {
        record_loop_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            index,
            ProgramPointKind::Exit,
            *state.clone(),
        );
        record_statement_program_state(
            &mut execution.presentation.recorded_states,
            function_block,
            owner.header_index,
            ProgramPointKind::Exit,
            *state.clone(),
        );
        for exited in proof_context
            .constants
            .source_layout
            .exited_branch_regions(owner.header_index)
            .to_vec()
        {
            record_statement_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                exited,
                ProgramPointKind::Exit,
                *state.clone(),
            );
        }
    }
    match outcome {
        StatementOutcome::Normal(next_state) => {
            // Completing this statement statically completes the recorded
            // chain of enclosing branch regions it ends.
            for exited in proof_context
                .constants
                .source_layout
                .exited_branch_regions(statement_index)
                .to_vec()
            {
                record_statement_program_state(
                    &mut execution.presentation.recorded_states,
                    function_block,
                    exited,
                    ProgramPointKind::Exit,
                    *next_state.clone(),
                );
            }
            let remaining = if let Some(remaining) = remaining {
                execution.core.frontier.next_statement_index = source_region.continuation_node;
                Some(remaining)
            } else {
                resume_after_completed_region(&mut execution.core.frontier)
            };
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            execution.core.state = (*next_state.clone()).into();
            match remaining {
                Some(remaining) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: remaining.into(),
                    };
                    record_statement_program_state(
                        &mut execution.presentation.recorded_states,
                        function_block,
                        execution.core.frontier.next_statement_index,
                        ProgramPointKind::Entry,
                        *next_state,
                    );
                }
                None if finish_exhausted_region(&mut execution.core.frontier) => {
                    // The region's boundary state is also the entry state of
                    // its statically known continuation, exactly as the arm
                    // recorded it when continuations were popped at runtime.
                    record_statement_program_state(
                        &mut execution.presentation.recorded_states,
                        function_block,
                        source_region.continuation_node,
                        ProgramPointKind::Entry,
                        *next_state,
                    );
                }
                None => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                    )));
                }
            }
        }
        StatementOutcome::Return { .. } | StatementOutcome::Throw { .. } => {
            // A `Throw` inside an entered `try` body resumes at the handler
            // entry instead of terminating the path. Only entered `try`
            // bodies push handler continuations, so C execution (and throws
            // outside any `try`) always takes the termination path below.
            // Routed paths fall through to the shared epilogue like normally
            // completed steps.
            let routed = if let StatementOutcome::Throw { value, state } = &outcome {
                route_throw_to_handler(
                    execution,
                    proof_context,
                    available_pure_facts,
                    &mut introduced_facts,
                    function,
                    parameter_binding,
                    function_block,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    prerequisite_policy,
                    context,
                    &value.native(),
                    state,
                    &successor_pure_facts,
                )?
            } else {
                false
            };
            if !routed {
                record_completed_continuation_exits(&mut execution.core.frontier);
                let return_assumptions = {
                    let _return_context = crate::instrumentation::OperationTiming::new(
                        function.name(),
                        claim_label,
                        "statement return context",
                    );
                    successor_pure_facts.context()
                };
                let case_outcomes =
                    crate::kernel::program_function_outcomes_from_statement_outcome_with_resource_cases(
                        &execution_start_state,
                        function,
                        arguments,
                        outcome.clone(),
                        transition_obligations.clone(),
                        &return_assumptions,
                    );
                let mut completed_outcomes = Vec::new();
                for (outcome, obligations, case_facts) in case_outcomes {
                    let mut completed_execution_facts =
                        completed_execution_facts(&execution.core, &execution_pure_facts);
                    for fact in case_facts {
                        completed_execution_facts.push(ExecutionPureFact::new(fact));
                    }
                    completed_outcomes.push((
                        outcome,
                        completed_execution_facts,
                        obligations,
                        execution.core.borrow_evidence().clone(),
                    ));
                }
                append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
                let completed =
                    crate::kernel::program_function_execution_candidates_from_completed_outcomes(
                        execution_start_state.clone(),
                        function.clone(),
                        arguments.to_vec(),
                        completed_outcomes,
                    );
                // The returning statement's own successor facts are this
                // path's, exactly as a continuing statement's are: a loop
                // rule's `Return` path states the conditions the body took
                // on the way to its `return` (`flag == 0` for a body that
                // returns under `if (flag == 0)`), and the proof that closes
                // the postcondition on the returned value folds through them
                // only when they are its facts, not merely the candidate's.
                // A plain `return x;` adds nothing here and loses nothing.
                *available_pure_facts = successor_pure_facts;
                if let Some(loop_index) = loop_index
                    && matches!(outcome, StatementOutcome::Return { .. })
                {
                    // Those facts are stated over the loop's iteration
                    // identities. The loop's exit state, recorded above
                    // from this returned state, binds them; the statement's
                    // entry state, where premises are otherwise read,
                    // predates the head's havoc and cannot spell them.
                    execution.presentation.surface_record.last_step_entry = Some(ProgramPointRef {
                        region: CodeRegionRef::Loop(loop_index),
                        kind: ProgramPointKind::Exit,
                    });
                }
                let execution_state = execution_start_state.clone();
                set_function_exit_execution(
                    &mut execution.core.frontier,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    execution_start_state,
                    completed,
                )?;
                execution.core.frontier.next_statement_index = source_region.continuation_node;
                execution.core.state = execution_state.into();
            }
        }
        StatementOutcome::LoopTestFalse(next_state)
        | StatementOutcome::Break(next_state)
        | StatementOutcome::Continue(next_state) => {
            // The control statement's own successor facts are this path's:
            // `if (i == 3) break;` leaves the loop knowing `i == 3`, and a
            // `break` exit that lost its guard would state nothing at all.
            // A false test likewise keeps the facts from its decision.
            // The frontier itself was advanced when the evidence was
            // recorded: inside a loop-body region these controls reach its
            // typed boundary, and a concretely executed loop resumes at its
            // own continuation.
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            execution.core.state = (*next_state).into();
            if matches!(
                execution.core.frontier.position,
                FrontierPosition::RegionBoundary
            ) && !execution.core.frontier.continuations.is_empty()
            {
                if let Some(remaining) = resume_after_completed_region(&mut execution.core.frontier)
                {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: Arc::new(remaining),
                    };
                } else {
                    finish_exhausted_region(&mut execution.core.frontier);
                }
            }
        }
        StatementOutcome::Jump {
            target,
            state: next_state,
        } => {
            if execution.core.frontier.natural_backedge_target == Some(target)
                && execution.core.frontier.in_loop_body
            {
                *available_pure_facts = successor_pure_facts;
                execution.core.frontier.position = FrontierPosition::RegionBoundary;
                execution.core.frontier.loop_control = Default::default();
                execution.core.frontier.execution_start_state = Some(execution_start_state);
                execution.core.state = (*next_state).into();
                return Ok(introduced_facts);
            }
            if execution.core.frontier.in_loop_body && function.control_target(target).is_some() {
                *available_pure_facts = successor_pure_facts;
                execution.core.frontier.position = FrontierPosition::RegionBoundary;
                execution.core.frontier.loop_control =
                    crate::kernel::proof::LoopControlExit::Jump(target);
                execution.core.frontier.execution_start_state = Some(execution_start_state);
                execution.core.state = (*next_state).into();
                return Ok(introduced_facts);
            }
            let target_id = target;
            let target = function.control_target(target_id).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced an unknown goto target"
                ))
            })?;
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            let target_statement_index = loop_index
                .and_then(|loop_index| {
                    proof_context
                        .constants
                        .source_layout
                        .natural_exit_target(loop_index)
                        .filter(|natural_target| *natural_target == target_id)
                        .and_then(|_| {
                            proof_context
                                .constants
                                .source_layout
                                .natural_exit_statement_index(loop_index)
                        })
                })
                .unwrap_or(target.statement_index);
            record_statement_program_state(
                &mut execution.presentation.recorded_states,
                function_block,
                target_statement_index,
                ProgramPointKind::Entry,
                *next_state.clone(),
            );
            execution.core.state = (*next_state).into();
        }
        StatementOutcome::VerificationDiverges => {
            let completed_execution_facts =
                completed_execution_facts(&execution.core, &execution_pure_facts);
            let mut completed_outcomes = vec![(
                FunctionOutcome::VerificationDiverges,
                completed_execution_facts,
                transition_obligations,
                execution.core.borrow_evidence().clone(),
            )];
            append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
            let completed =
                crate::kernel::program_function_execution_candidates_from_completed_outcomes(
                    execution_start_state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    completed_outcomes,
                );
            let execution_state = execution_start_state.clone();
            set_function_exit_execution(
                &mut execution.core.frontier,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            execution.core.frontier.next_statement_index = source_region.continuation_node;
            execution.core.state = execution_state.into();
        }
        StatementOutcome::UndefinedBehavior(kind) => {
            let site = crate::surface::diagnostics::describe_undefined_behavior_site(
                &current_state,
                &step_statement,
                &context
                    .cloned()
                    .unwrap_or_else(|| available_pure_facts.context()),
                &kind,
            );
            let required = kind.required_goal().cloned();
            let refusal_kind = crate::surface::diagnostics::undefined_behavior_refusal_kind(&kind);
            let outcome = FunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}{site}{}\n{}",
                describe_function_outcome(&outcome, parameter_binding),
                crate::surface::diagnostics::describe_execution_statement_site(),
                if required.is_some() {
                    // The structured diagnostic supplies the facts/resources
                    // with the goal's label map. An embedded context dump
                    // would introduce a second, conflicting set of labels.
                    String::new()
                } else {
                    describe_step_proof_context(
                        available_pure_facts,
                        context,
                        step_diagnostic_resources(&current_state),
                        parameter_binding,
                        &execution_pure_facts,
                    )
                }
            ))
            .with_reported_assertion_goal(required)
            .with_kind(refusal_kind)
            .with_proof_refusal(crate::surface::ProofRefusal::Tactic));
        }
        StatementOutcome::RuntimeError(error) => {
            let kind = runtime_refusal_kind(&error);
            let unsupported = kind == crate::surface::ClickErrorKind::Internal;
            let description = if unsupported {
                "reached an unsupported modeled operation"
            } else {
                "could not verify C operation"
            };
            let resources = step_diagnostic_resources(&current_state);
            let detail = crate::surface::diagnostics::describe_unestablished_assembly_fact(
                &error,
                &listed_context_pure_facts(available_pure_facts, context),
                resources,
                parameter_binding,
                &execution_pure_facts,
            )
            .unwrap_or_else(|| {
                format!(
                    "{}{}",
                    describe_runtime_error_before_statement(
                        &error,
                        &current_state,
                        proof_context.parsed_function,
                        parameter_binding,
                    ),
                    describe_missing_range_end_note(
                        &error,
                        resources,
                        Some(&current_state),
                        parameter_binding
                    )
                )
            });
            if matches!(
                error,
                crate::kernel::RuntimeError::UninitializedMutex { .. }
                    | crate::kernel::RuntimeError::UnsupportedConcurrentMutex
            ) {
                return Err(ClickError::new(detail)
                    .with_kind(kind)
                    .with_proof_refusal(crate::surface::ProofRefusal::Tactic));
            }
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` {description}: {}\n  C operation: {}{}{}\n{}",
                detail,
                describe_statement_head(&step_statement),
                describe_call_bindings(&step_statement, function_environment),
                crate::surface::diagnostics::describe_execution_statement_site(),
                describe_step_proof_context(
                available_pure_facts, context,
                    resources,
                    parameter_binding,
                    &execution_pure_facts
                )
            ))
            .with_kind(kind)
            .with_runtime_missing_resource(&error)
            .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(&error)));
        }
    }
    execution
        .presentation
        .record_generated_load_source_events(&generated_load_source_events);
    // Standalone fact-transport steps are written against the post-statement
    // state, so their construction runs after the statement's exit states
    // are in place. Each transport adds its target to the certificate-visible
    // certificate facts, and finishing the transports retires the stale
    // pre-statement sources, mirroring what the certificate's own check
    // carries across this statement.
    // A source-invisible post-test occupies the old loop-head step. Once it
    // succeeds, enter the unchanged post-test loop's body in that same step.
    if phase_test_succeeded
        && phase_source
            .is_some_and(|phase| phase.test_position == crate::kernel::LoopTestPosition::AfterBody)
        && matches!(
            execution.core.frontier.position,
            FrontierPosition::StatementEntry { .. }
        )
        && let FrontierPosition::StatementEntry { remaining } = &execution.core.frontier.position
        && matches!(
            split_next_source_operation(remaining).map(|(head, _)| head),
            Ok(ProgramStatement::Loop { .. })
        )
    {
        execute_step_from_frontier_position_selecting_path(
            execution,
            proof_context,
            available_pure_facts,
            tactic_name,
            prerequisite_policy,
            loop_step_policy,
            selected_path_fact,
            context,
            None,
        )?;
    }
    Ok(introduced_facts)
}

/// Execution exhausted the frontier's own statement tree with no enclosing
/// continuation. A bounded region — a loop-preservation body or a branch
/// arm — reaches its typed boundary; a whole-function region has no boundary
/// short of `return`, so the caller keeps its end-of-function error.
pub(super) fn finish_exhausted_region(frontier: &mut ExecutionFrontier) -> bool {
    match frontier.region {
        ExecutionRegionKind::LoopBody | ExecutionRegionKind::BranchArm => {
            debug_assert!(frontier.continuations.is_empty());
            frontier.position = FrontierPosition::RegionBoundary;
            true
        }
        ExecutionRegionKind::Function => false,
    }
}

pub(super) fn resume_after_completed_region(
    frontier: &mut ExecutionFrontier,
) -> Option<ProgramStatement> {
    while let Some(continuation) = frontier.continuations.pop() {
        frontier.next_statement_index = continuation.next_statement_index;
        if let Some(remaining) = continuation.remaining {
            return Some(Arc::unwrap_or_clone(remaining));
        }
    }
    None
}

fn record_completed_continuation_exits(frontier: &mut ExecutionFrontier) {
    while frontier.continuations.pop().is_some() {}
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_current_statement_entry(
    frontier: &ExecutionFrontier,
    recorded_states: &mut RecordedStates,
    state: &ExecutionState,
    function_block: &FunctionBlock,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    let current_state = match &frontier.position {
        FrontierPosition::FunctionEntry => program_function_entry_state(state, function, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                ))
            })?,
        FrontierPosition::StatementEntry { .. } => state.clone(),
        FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => {
            return Ok(())
        }
    };
    record_statement_program_state(
        recorded_states,
        function_block,
        frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

pub(super) const BOUNDED_EXECUTE_STEP_LIMIT: usize = 10_000;

/// The C branches one implicit tail may split at. Each arm runs to
/// function exit, so `n` sequential branches give `2^n` paths; past this many
/// splits the search stops promptly and names the explicit join. No gate test
/// splits more than 32 times (2026-10-21); a function of ten sequential
/// branches splits 1,023 times and still runs.
pub(super) const BOUNDED_EXECUTE_SPLIT_LIMIT: usize = 1_024;

/// Whether several checked successors of one statement are the cases of a
/// path split: each completes the statement normally or returns, and each
/// assumes a path fact some other successor does not, so the facts tell the
/// cases apart.
/// A loop's own test has two such cases: true continues the pass, false
/// leaves the loop, whose outcome is the loop's exit.
fn statement_successors_are_path_cases(transitions: &[CertifiedStatementTransition]) -> bool {
    let facts = transitions
        .iter()
        .map(|transition| transition.path_facts.as_slice())
        .collect::<Vec<_>>();
    transitions.iter().all(|transition| {
        matches!(
            transition.outcome,
            StatementOutcome::Normal(_)
                | StatementOutcome::Return { .. }
                | StatementOutcome::Jump { .. }
                | StatementOutcome::LoopTestFalse(_)
        ) && !distinguishing_path_facts(&transition.path_facts, &facts).is_empty()
    })
}

/// The facts in `facts` that not every case in `cases` assumes: the
/// conditions that select this case.
fn distinguishing_path_facts<'t>(
    facts: &'t [Proposition],
    cases: &[&[Proposition]],
) -> Vec<&'t Proposition> {
    facts
        .iter()
        .filter(|fact| !cases.iter().all(|other| other.contains(fact)))
        .collect()
}

/// One case of a path split: the checked path facts that select it.
struct PathCase<'t> {
    path_facts: &'t [Proposition],
}

impl<'t> PathCase<'t> {
    fn of_statement(transition: &'t CertifiedStatementTransition) -> Self {
        Self {
            path_facts: &transition.path_facts,
        }
    }
}

/// The Click condition a proof-level case split separates a C condition's
/// checked paths on first, when one has a spelling: the same choice the
/// planner makes before a `branch` whose condition has more paths than arms.
pub(super) fn condition_path_case_split_condition(
    path_facts: &[&[Proposition]],
    available: &dyn Fn(&Proposition) -> bool,
    state: &ExecutionState,
    proof_context: &ExecutionProofContext<'_>,
) -> Option<(ConditionTerm, SyntaxProposition)> {
    let cases = path_facts
        .iter()
        .map(|path_facts| PathCase { path_facts })
        .collect::<Vec<_>>();
    path_case_split_condition(&cases, available, state, proof_context)
}

/// The proof `match` that separates a Rust `match` of an enum local: one arm
/// per variant, each field bound as `<local>_<variant>_<index>` with the
/// variant in snake case, made fresh against the function's locals. Every
/// arm's binders differ, so all stay bound after the implicit tail finishes.
fn enum_switch_proof_match(
    statement: &ProgramStatement,
    state: &ExecutionState,
    facts: Option<&PureFactContext>,
) -> Option<ProofMatch> {
    let ProgramStatement::If { condition, .. } = statement else {
        return None;
    };
    let mut test = condition;
    while let ProgramExpression::Or(left, _) = test {
        test = left;
    }
    let ProgramExpression::EnumIs { value, .. } = test else {
        return None;
    };
    let (scrutinee, name, native) = match value.as_ref() {
        ProgramExpression::Variable(name) => (
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.clone())),
            name.to_string(),
            state.locals().get_native(name)?,
        ),
        ProgramExpression::StepResult { step, .. } => (
            crate::surface::diagnostics::step_result_expression(*step)?,
            "field".into(),
            state.step_result(*step)?.native(),
        ),
        _ => return None,
    };
    let ProgramValue::Parameter(term) = native.as_ref() else {
        return None;
    };
    if term.algebraic_type.rigid
        || matches!(
            term.node,
            crate::kernel::AlgebraicTermNode::Constructor { .. }
        )
        || facts.is_some_and(|facts| facts.knows_algebraic_constructor(term))
    {
        return None;
    }
    let arms = term
        .algebraic_type
        .variants
        .iter()
        .map(|variant| {
            let mut used = BTreeSet::new();
            let snake = snake_case(&variant.name);
            let bindings = (0..variant.fields.len())
                .map(|index| {
                    let mut binding = format!("{name}_{snake}_{index}");
                    while state.locals().contains_name(&binding) || !used.insert(binding.clone()) {
                        binding.push('_');
                    }
                    binding
                })
                .collect();
            ProofInductionArm {
                type_name: term.algebraic_type.name.clone(),
                variant: variant.name.clone(),
                bindings,
                tactics: Vec::new(),
            }
        })
        .collect();
    Some(ProofMatch {
        scrutinee,
        ensuring: None,
        arms,
    })
}

/// `IsEmpty` as `is_empty`.
fn snake_case(name: &str) -> String {
    let mut snake = String::new();
    for (index, character) in name.chars().enumerate() {
        if character.is_uppercase() {
            if index > 0 {
                snake.push('_');
            }
            snake.extend(character.to_lowercase());
        } else {
            snake.push(character);
        }
    }
    snake
}

/// The condition a case split of `cases` splits on first: a distinguishing
/// condition fact that some case assumes true and another false, that the
/// facts do not already decide, and that Click can spell in source terms.
/// A condition every case decides is preferred, in the cases' order: it is
/// the one the operation consults first on every path (`x > 0` in
/// `x > 0 && y > 0`, the address comparison before a load reads the cell it
/// selects), so the facts of each side are then the facts that side's paths
/// have. Splitting leaves fewer cases on each side, so repeating the split
/// separates every case.
fn path_case_split_condition(
    cases: &[PathCase<'_>],
    available: &dyn Fn(&Proposition) -> bool,
    state: &ExecutionState,
    proof_context: &ExecutionProofContext<'_>,
) -> Option<(ConditionTerm, SyntaxProposition)> {
    let facts = cases.iter().map(|case| case.path_facts).collect::<Vec<_>>();
    let decides = |case: &PathCase<'_>, condition: &ConditionTerm, value: bool| {
        case.path_facts
            .contains(&Proposition::condition_is(condition.clone(), value))
    };
    let candidates = cases
        .iter()
        .flat_map(|case| distinguishing_path_facts(case.path_facts, &facts))
        .filter_map(|fact| {
            let Proposition::ConditionIs(condition, _) = fact else {
                return None;
            };
            let splits = [true, false].into_iter().all(|value| {
                cases
                    .iter()
                    .any(|case| decides(case, condition.native_compat(), value))
            });
            let undecided = [true, false]
                .into_iter()
                .all(|value| !available(&Proposition::condition_is(condition.clone(), value)));
            (splits && undecided).then_some(condition)
        })
        .collect::<Vec<_>>();
    let decided_by_every_case = |condition: &ConditionTerm| {
        cases
            .iter()
            .all(|case| decides(case, condition, true) || decides(case, condition, false))
    };
    candidates
        .iter()
        .filter(|condition| decided_by_every_case(condition.native_compat()))
        .chain(
            candidates
                .iter()
                .filter(|condition| !decided_by_every_case(condition.native_compat())),
        )
        .find_map(|condition| {
            let surface = synthesize_surface_proposition(
                &Proposition::condition_is((*condition).clone(), true),
                ParameterBinding::new(
                    proof_context.parsed_function.parameters(),
                    proof_context.arguments,
                ),
                state,
            )?;
            Some((condition.native_compat().clone(), surface))
        })
}

/// What to write when a simple tactic meets a split it does not make: the
/// proof `if` on the condition a planner would split on first, which gives
/// each side its own frontier.
fn describe_path_case_split_guidance(
    split_condition: Option<&SyntaxProposition>,
    case_count: usize,
) -> String {
    let split = match split_condition {
        Some(condition) => format!(
            "Split the proof on the case condition first, then step each case:\n  if {} {{\n      step(); ...\n  }} else {{\n      step(); ...\n  }}\nThe implicit tail makes this split itself where the script ends.\n",
            crate::surface::diagnostics::describe_click_proposition(condition)
        ),
        None => "Click could not express a case condition in proof syntax, so the implicit tail cannot make this split. Use explicit cases and `step()` to expose the remaining obligation; a different source-level case split may work. The missing spelling is a tooling limitation.\n".to_string(),
    };
    format!(
        "These successors are {} cases of one C operation, told apart only by the conditions above; a simple step never splits the proof. {split}",
        case_count,
    )
}

pub(super) fn split_next_source_operation(
    statement: &ProgramStatement,
) -> Result<(ProgramStatement, Option<ProgramStatement>), String> {
    match statement {
        ProgramStatement::Seq(statements) => {
            let (source_statement, first_remaining) =
                split_next_source_operation(statements.first())?;
            let remaining = match first_remaining {
                Some(first_remaining) => {
                    ProgramStatement::Seq(statements.with_statement(0, Arc::new(first_remaining)))
                }
                None => statements.rest().as_ref().clone(),
            };
            Ok((source_statement, Some(remaining)))
        }
        statement => Ok((statement.clone(), None)),
    }
}

#[cfg(test)]
pub(super) fn sequence_from_statements(
    statements: &[ProgramStatement],
) -> Option<ProgramStatement> {
    let mut level = statements.to_vec();
    while level.len() > 1 {
        let mut next_level = Vec::with_capacity(level.len().div_ceil(2));
        let mut statements = level.into_iter();
        while let Some(first) = statements.next() {
            next_level.push(match statements.next() {
                Some(second) => program_seq(first, second),
                None => first,
            });
        }
        level = next_level;
    }
    level.pop()
}

/// Appends the returned paths of summarized loops this execution retained to
/// the outcomes it completes with. Each was certified where its loop was
/// summarized; the function boundary is where it rejoins the path set, in
/// the order the proof object appends their traces.
fn append_pending_loop_returns(
    core: &mut crate::kernel::proof::ExecutionProofCore,
    completed_outcomes: &mut Vec<(
        FunctionOutcome,
        crate::kernel::proof::CompletedExecutionFacts,
        Vec<ProofObligation>,
        crate::kernel::CheckedBorrowCallEvidenceSequence,
    )>,
) {
    for pending in core.complete_pending_loop_returns() {
        completed_outcomes.push((
            pending.outcome,
            crate::kernel::proof::CompletedExecutionFacts::from_facts(pending.execution_facts),
            pending.obligations,
            pending.borrow_evidence,
        ));
    }
}

fn set_function_exit_execution(
    frontier: &mut ExecutionFrontier,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    execution_start_state: ExecutionState,
    execution: FunctionExecutionCandidates,
) -> Result<(), ClickError> {
    if frontier.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        )));
    }
    frontier.execution_start_state = Some(execution_start_state);
    frontier.position = FrontierPosition::FunctionExit { execution };
    Ok(())
}

/// The driver's account of a refused record call: the proof object's reason,
/// then what it expected and what it was offered when the judgment concerned
/// statements or a premise.
pub(super) fn describe_evidence_refusal(
    refusal: &crate::kernel::proof::EvidenceRefusal,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let mut text = refusal.reason.to_string();
    if let Some(expected) = &refusal.expected {
        text.push_str(&format!(
            "; the source statement to consume next is `{}`",
            describe_statement_head(expected)
        ));
    }
    if let Some(proved) = &refusal.proved {
        text.push_str(&format!(
            ", the theorem proves `{}`",
            describe_statement_head(proved)
        ));
    }
    if let Some(premise) = &refusal.premise {
        text.push_str(&format!(
            "; the premise is {}",
            describe_pure_fact(premise, parameter_binding)
        ));
    }
    text
}

/// Present the callee's parameter names alongside the written call arguments
/// when a call fails; no symbolic heap value is guessed for this diagnostic.
fn describe_call_bindings(
    statement: &ProgramStatement,
    environment: &ExecutionEnvironment,
) -> String {
    let (name, arguments) = match statement {
        ProgramStatement::Call {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallConstruct {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallResult {
            function_name,
            arguments,
            ..
        } => (function_name.as_str(), arguments.as_slice()),
        _ => return String::new(),
    };
    let parameters = environment
        .get_function_contract(name)
        .map(|contract| contract.interface().parameters())
        .or_else(|| {
            environment
                .get_function(name)
                .map(|function| function.parameters())
        });
    let Some(parameters) = parameters else {
        return String::new();
    };
    let bindings = parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            format!(
                "{} = {}",
                parameter.name(),
                describe_program_expression(argument)
            )
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        String::new()
    } else {
        format!("\n  call bindings: {}", bindings.join(", "))
    }
}

/// A one-line C spelling of a statement's head, enough to recognize it in
/// a diagnostic: the first statement of a sequence, a loop or branch by its
/// condition, a body by its operation.
pub(super) fn describe_statement_head(statement: &ProgramStatement) -> String {
    match statement {
        ProgramStatement::Seq(statements) => describe_statement_head(statements.first()),
        ProgramStatement::Skip => "skip".to_string(),
        ProgramStatement::Break => "break".to_string(),
        ProgramStatement::Continue => "continue".to_string(),
        ProgramStatement::Goto { target, .. } => format!("goto target({})", target.0),
        ProgramStatement::EndAutomaticLifetimes { .. } => "automatic lifetime end".to_string(),

        ProgramStatement::Declare { name, .. } => format!("declare {name}"),
        ProgramStatement::DeclareAggregate { name, .. } => format!("declare aggregate {name}"),
        ProgramStatement::Assign {
            name, expression, ..
        } => {
            format!("{name} = {}", describe_program_expression(expression))
        }
        ProgramStatement::CallConstruct {
            target,
            function_name,
            arguments,
        } => {
            let call = format!(
                "{}({})",
                crate::surface::diagnostics::describe_called_function(function_name),
                arguments
                    .iter()
                    .map(describe_program_expression)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            format!("{target} = {call}")
        }
        ProgramStatement::Call {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallResult {
            function_name,
            arguments,
            ..
        } => format!(
            "{}({})",
            crate::surface::diagnostics::describe_called_function(function_name),
            arguments
                .iter()
                .map(describe_program_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ProgramStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
            ends_program_on_failure,
            ..
        } => {
            let function = if *ends_program_on_failure {
                "operator new"
            } else if *zeroed {
                "calloc"
            } else {
                "malloc"
            };
            format!(
                "{target} = {function}({})",
                describe_program_expression(bytes)
            )
        }
        ProgramStatement::HeapFree { pointer } => {
            format!("free({})", describe_program_expression(pointer))
        }
        ProgramStatement::Assert { condition, .. } => {
            format!("assert({})", describe_program_expression(condition))
        }
        ProgramStatement::StepValue { expression, .. } => {
            format!("value {}", describe_program_expression(expression))
        }
        ProgramStatement::Return(expression) => {
            format!("return {}", describe_program_expression(expression))
        }
        ProgramStatement::ThrowOpaque(payload_type) => {
            format!("throw opaque {}", payload_type.name())
        }
        ProgramStatement::Throw(expression) => {
            format!("throw {}", describe_program_expression(expression))
        }
        ProgramStatement::TryCatchInt32 { binding, .. } => format!("try ... catch (int {binding})"),
        ProgramStatement::UnwindCleanup { body, .. } => describe_statement_head(body),
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            format!(
                "*{} = {}",
                describe_program_expression(pointer),
                describe_program_expression(value)
            )
        }
        ProgramStatement::InitializeScalarArray {
            target,
            count,
            copy,
            fresh,
            ..
        } => format!(
            "{} {} with {} scalar elements{}",
            if *fresh { "initialize" } else { "write" },
            describe_program_expression(target),
            count,
            if *copy {
                " by state copy"
            } else {
                " by repetition"
            }
        ),
        ProgramStatement::CopyAggregate { target, source, .. } => format!(
            "copy aggregate {} <- {}",
            describe_program_expression(target),
            describe_program_expression(source)
        ),
        ProgramStatement::Update {
            target, operand, ..
        } => format!(
            "update {} with {}",
            describe_program_expression(target),
            describe_program_expression(operand)
        ),
        ProgramStatement::If { condition, .. } => {
            format!("if ({})", describe_program_expression(condition))
        }
        ProgramStatement::LoopTest { condition, .. } => {
            format!(
                "the loop's test ({})",
                describe_program_expression(condition)
            )
        }
        ProgramStatement::Loop {
            test: loop_test, ..
        } => match loop_test.source_condition() {
            Some(condition) => format!("while ({})", describe_program_expression(condition)),
            None => "loop with test preparation".to_owned(),
        },
        ProgramStatement::Switch { expression, .. } => {
            format!("switch ({})", describe_program_expression(expression))
        }
    }
}

#[cfg(test)]
mod cursor_sequence_tests {
    use super::*;

    fn state_test_leaf(name: String) -> SyntaxProposition {
        SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramBinding(name),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::Old(Box::new(SyntaxTerm::ProgramBinding("entry".into()))),
        }
    }

    fn annotate_on_small_stack(
        surface: SyntaxProposition,
    ) -> (Result<SyntaxProposition, ClickError>, usize) {
        std::thread::Builder::new()
            .name("program-point-annotation-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(move || {
                crate::instrumentation::measure_deterministic_work(|| {
                    annotate_surface_at_program_point(
                        &surface,
                        &ProgramPointSelector::Mark("chosen".into()),
                        ProgramPointAnnotation::Reread,
                    )
                })
            })
            .unwrap()
            .join()
            .expect("state annotation must not retain large recursive frames")
    }

    #[test]
    fn state_annotation_leaves_the_int64_minimum_unanchored() {
        let observed = SyntaxTerm::Call {
            name: "to_integer".into(),
            arguments: vec![SyntaxTerm::ProgramBinding("q".into())],
        };
        let minimum = SyntaxTerm::Negate(Box::new(SyntaxTerm::IntegerLiteral(
            "9223372036854775808".into(),
        )));
        let surface = SyntaxProposition::Comparison {
            left: minimum.clone(),
            operator: ComparisonOperator::LessEqual,
            right: observed.clone(),
        };
        let selector = ProgramPointSelector::Mark("chosen".into());
        let annotated =
            annotate_surface_at_program_point(&surface, &selector, ProgramPointAnnotation::Reread)
                .unwrap();
        assert_eq!(
            annotated,
            SyntaxProposition::Comparison {
                left: minimum,
                operator: ComparisonOperator::LessEqual,
                right: SyntaxTerm::At {
                    selector: selector.clone(),
                    expression: Box::new(observed.clone()),
                },
            }
        );
        // A numeral `at(..)` reads the same way keeps its anchor.
        let zero = SyntaxTerm::IntegerLiteral("0".into());
        let surface = SyntaxProposition::Comparison {
            left: zero.clone(),
            operator: ComparisonOperator::LessEqual,
            right: observed,
        };
        let SyntaxProposition::Comparison { left, .. } =
            annotate_surface_at_program_point(&surface, &selector, ProgramPointAnnotation::Reread)
                .unwrap()
        else {
            panic!("a comparison stays a comparison");
        };
        assert_eq!(
            left,
            SyntaxTerm::At {
                selector,
                expression: Box::new(zero),
            }
        );
    }

    #[test]
    fn state_annotation_depth_is_stack_safe_and_bounded() {
        for depth in [7, 15, 23, PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT - 1] {
            let mut surface = state_test_leaf("current".into());
            for _ in 0..depth {
                surface = SyntaxProposition::Not(Box::new(surface));
            }
            let (result, work) = annotate_on_small_stack(surface);
            let result = result.unwrap();
            assert_eq!(work, depth + 1);
            let mut leaf = &result;
            for _ in 0..depth {
                let SyntaxProposition::Not(body) = leaf else {
                    panic!("annotation must preserve every connective");
                };
                leaf = body;
            }
            let SyntaxProposition::Comparison { left, right, .. } = leaf else {
                panic!("annotation must preserve the leaf");
            };
            assert!(matches!(
                left,
                SyntaxTerm::At {
                    selector: ProgramPointSelector::Mark(_),
                    ..
                }
            ));
            assert!(matches!(right, SyntaxTerm::Old(_)));
        }
        let mut too_deep = state_test_leaf("current".into());
        for _ in 0..PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT {
            too_deep = SyntaxProposition::Not(Box::new(too_deep));
        }
        let (result, work) = annotate_on_small_stack(too_deep);
        assert!(
            result
                .unwrap_err()
                .message()
                .contains("structural depth bound")
        );
        assert_eq!(work, PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT + 1);
    }

    #[test]
    fn state_annotation_work_is_linear_and_preserves_operand_order() {
        for leaves in [8, 16, 32, 64] {
            let mut level = (0..leaves)
                .map(|index| state_test_leaf(index.to_string()))
                .collect::<Vec<_>>();
            while level.len() > 1 {
                let mut children = level.into_iter();
                level = Vec::new();
                while let Some(left) = children.next() {
                    let right = children.next().unwrap();
                    level.push(SyntaxProposition::Implies(Box::new(left), Box::new(right)));
                }
            }
            let (result, work) = annotate_on_small_stack(level.pop().unwrap());
            let result = result.unwrap();
            assert_eq!(work, 2 * leaves - 1);
            let mut pending = vec![&result];
            let mut index = 0;
            while let Some(node) = pending.pop() {
                match node {
                    SyntaxProposition::Implies(left, right) => {
                        pending.push(right);
                        pending.push(left);
                    }
                    SyntaxProposition::Comparison { left, .. } => {
                        let SyntaxTerm::At { expression, .. } = left else {
                            panic!("the comparison must read the selected state");
                        };
                        assert_eq!(
                            expression.as_ref(),
                            &SyntaxTerm::ProgramBinding(index.to_string())
                        );
                        index += 1;
                    }
                    _ => panic!("annotation changed a connective"),
                }
            }
            assert_eq!(index, leaves);
        }
    }

    #[test]
    fn large_straight_line_cursor_advances_on_a_small_stack() {
        std::thread::Builder::new()
            .name("large-straight-line-cursor".to_string())
            .stack_size(256 * 1024)
            .spawn(|| {
                let statements = vec![ProgramStatement::Skip; 10_000];
                let mut remaining = sequence_from_statements(&statements)
                    .expect("the generated block should not be empty");
                let mut count = 0;
                loop {
                    let (statement, tail) = split_next_source_operation(&remaining)
                        .expect("a balanced sequence should have a next operation");
                    assert_eq!(statement, ProgramStatement::Skip);
                    count += 1;
                    let Some(tail) = tail else {
                        break;
                    };
                    remaining = tail;
                }
                assert_eq!(count, 10_000);
            })
            .expect("the small-stack cursor thread should start")
            .join()
            .expect("large straight-line cursor advancement should be stack bounded");
    }
}

#[cfg(test)]
mod refusal_scaling_tests {
    use super::*;
    include!("../../scaling_tests/surface/proof/cursor_refusals.rs");
}

/// A word store copies the entry value of its named local. The exit spelling
/// reads the cell through the same unchanged pointer and index bindings.
fn word_store_source(
    statement: &ProgramStatement,
    entry: &ExecutionState,
    outcome: &StatementOutcome,
    exit_point: &ProgramPointRef,
) -> Option<SyntaxProposition> {
    use crate::kernel::{MachineTerm, ProgramType, ProgramValue};

    let (pointer, value) = match statement {
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore {
            pointer,
            value,
            value_type: ProgramType::UInt32,
            volatile: false,
            ..
        } => (pointer, value),
        _ => return None,
    };
    let ProgramExpression::Variable(value) = value else {
        return None;
    };
    let StatementOutcome::Normal(exit) = outcome else {
        return None;
    };
    let stable = |binding: &crate::kernel::BindingName, ty| {
        entry
            .locals()
            .nonvolatile_scalar(binding, ty)
            .zip(exit.locals().nonvolatile_scalar(binding, ty))
            .is_some_and(|(before, after)| before.same_retained_root(after))
    };
    let (base, index) = match pointer {
        ProgramExpression::Add(base, index) => (base.as_ref(), Some(index.as_ref())),
        pointer => (pointer, None),
    };
    let ProgramExpression::Variable(pointer) = base else {
        return None;
    };
    if !stable(pointer, ProgramType::UInt32Pointer) {
        return None;
    }
    let index = match index {
        None => SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
        Some(ProgramExpression::Variable(index)) if stable(index, ProgramType::Int32) => {
            SyntaxTerm::Binding(index.source_spelling()?.to_owned())
        }
        Some(
            index @ ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Constant { .. })),
        ) => SyntaxTerm::ProgramExpression(index.clone()),
        _ => return None,
    };
    entry
        .locals()
        .nonvolatile_scalar(value, ProgramType::UInt32)?;

    let at = |point: &ProgramPointRef, expression| SyntaxTerm::At {
        selector: ProgramPointSelector::ProgramPoint(point.clone()),
        expression: Box::new(expression),
    };
    let entry_point = ProgramPointRef {
        region: exit_point.region.clone(),
        kind: ProgramPointKind::Entry,
    };
    let read = SyntaxTerm::Index(
        Box::new(SyntaxTerm::Binding(pointer.source_spelling()?.to_owned())),
        Box::new(index),
    );
    Some(SyntaxProposition::Comparison {
        left: at(exit_point, read),
        operator: crate::surface::ComparisonOperator::Equal,
        right: at(
            &entry_point,
            SyntaxTerm::Binding(value.source_spelling()?.to_owned()),
        ),
    })
}
