//! Entry inputs produced once and retained by ordinary contract closing.

use super::*;
use crate::kernel::primitives::program_point::{PathLink, ProgramPointId};
use crate::kernel::primitives::{FunctionContractInterface, PopulationEffects};

/// The contract's own entry view, evaluated clauses and derived resource
/// facts. Execution and its proof forks share this input; closing never binds
/// the arguments or reevaluates these clauses against a later proof state.
pub(crate) struct RetainedClosingEntry {
    pub(super) caller: ExecutionState,
    pub(super) arguments: Vec<ProgramExpression>,
    pub(super) state: ExecutionState,
    pub(super) required: ResourceContext,
    pub(super) checked: Arc<[CheckedResourceFact]>,
    pub(super) assumptions: PureFactContext,
    pub(super) facts: Arc<[Proposition]>,
    pub(super) projection: Option<Arc<Result<FunctionMemoryEffectProjection, String>>>,
    pub(super) exit: std::sync::Mutex<Option<Box<RetainedExitProjection>>>,
}

impl std::fmt::Debug for RetainedClosingEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RetainedClosingEntry")
            .field("clauses", &self.checked.len())
            .finish_non_exhaustive()
    }
}

impl PreparedContractEntryCases {
    pub(super) fn closing_resource_guards(&self) -> Result<&[Proposition], ContractClosingRefusal> {
        if let Some(guards) = self.resource_guards.get() {
            return Ok(guards);
        }
        if !self
            .function
            .contract_interface()
            .composite_definitions_need_entry_cases
            && self
                .function
                .resource_requires()
                .iter()
                .chain(self.function.resource_ensures())
                .all(|clause| clause.guard().is_none())
        {
            return Ok(self.resource_guards.get_or_init(Vec::new));
        }
        let entry = &self.closing_entry;
        let guards = contract_resource_guards(
            &entry.caller,
            &self.function,
            &entry.arguments,
            &entry.assumptions.clone().assume_entry_clause_spans(),
        )?;
        Ok(self.resource_guards.get_or_init(|| guards))
    }
}

impl RetainedClosingEntry {
    pub(in crate::kernel) fn from_producer(
        caller: ExecutionState,
        function: &ProgramFunction,
        arguments: Vec<ProgramExpression>,
        state: ExecutionState,
        required: ResourceContext,
        checked: Arc<[CheckedResourceFact]>,
        assumptions: PureFactContext,
        mut facts: Vec<Proposition>,
    ) -> Self {
        let state = contract_view_of_entry(state, function, &arguments);
        let resources = with_unmatched_instance_body_views(
            state.resources().clone(),
            required.facts(),
            function,
            &state,
            &assumptions,
        );
        // These resources were constructed by entry opening and definitional
        // projection. Publish their facts without validating the same output.
        facts.extend(resources.observable_facts_assuming_valid(&assumptions));
        let state = state.with_resource_context(resources);
        let assumptions = assumptions_with_propositions(&assumptions, &facts);
        let projection =
            function
                .contract_claims()
                .iter()
                .any(|claim| matches!(claim.target(), FunctionContractClaimTarget::Effect))
                .then(|| {
                    Arc::new(
                crate::kernel::functions::project_contract_memory_effects_with_guard_policy(
                    &state, function.contract_interface(), Some(&checked), &assumptions,
                    &mut ExecutionBudget::beside_live_state(), true,
                ).map_err(|limit| limit.describe()).and_then(|projection| projection)
            )
                });
        Self {
            caller,
            arguments,
            state,
            required,
            checked,
            assumptions,
            facts: facts.into(),
            projection,
            exit: Default::default(),
        }
    }

    /// Retain one successful projection for this closing entry. The proof
    /// may move to another exit or strengthen its facts between consumers.
    /// Both are cache misses, with no search through earlier exits.
    pub(super) fn prepare_exit_projection(
        &self,
        function: &ProgramFunction,
        raw: &ExecutionState,
        at_exit: &mut ExecutionState,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContext> {
        crate::instrumentation::record_deterministic_work(1);
        let logical_reads = assumptions.equality_graph.logical_read_generation();
        if let Some(found) = self
            .exit
            .lock()
            .expect("closing exit projection")
            .as_ref()
            .filter(|retained| retained.matches(function, raw, at_exit, assumptions, logical_reads))
        {
            at_exit.point = found.point.clone();
            return Some(found.resources.clone());
        }
        let resources = expand_certification_exit(function, at_exit, assumptions)?;
        // Registration can discover a logical read definition during the
        // projection. Only publish a result for a stable input checkpoint.
        if assumptions.equality_graph.logical_read_generation() == logical_reads {
            *self.exit.lock().expect("closing exit projection") =
                Some(Box::new(RetainedExitProjection {
                    interface: Arc::clone(&function.contract_interface),
                    raw_memory: raw.memory().clone(),
                    raw_point: raw.point.id(),
                    point: at_exit.point.clone(),
                    population_effects: Arc::clone(&at_exit.population_effects),
                    memory: at_exit.memory().clone(),
                    input_resources: at_exit.resources().clone(),
                    assumptions: assumptions.clone(),
                    logical_reads,
                    resources: resources.clone(),
                }));
        }
        Some(resources)
    }

    pub(super) fn for_resource_case(
        &self,
        function: &ProgramFunction,
        guards: &[Proposition],
    ) -> Result<Self, ContractClosingRefusal> {
        // Use only entry premises and the pre-state guard values selected
        // for this outcome. Other facts proved by the body are not entry facts.
        let assumptions = assumptions_with_propositions(&self.assumptions, guards);
        let mut state = program_function_entry_state(&self.caller, function, &self.arguments)
            .ok_or_else(|| {
                ContractClosingRefusal::Internal(
                    "could not rebind arguments for a contract return check".into(),
                )
            })?;
        if !function
            .composite_resource_definitions()
            .iter()
            .any(CompositeResourceDefinition::is_recursive)
        {
            let resources =
                expand_certification_exit(function, &state, &assumptions).ok_or_else(|| {
                    ContractClosingRefusal::Incomplete(
                        "could not expand the entry resources for a contract return check".into(),
                    )
                })?;
            state = state.with_resource_context(resources);
        }
        Ok(Self::from_producer(
            self.caller.clone(),
            function,
            self.arguments.clone(),
            state,
            self.required.clone(),
            self.checked.clone(),
            assumptions,
            self.facts.to_vec(),
        ))
    }
}

/// The common projection before closing adds claim-specific instance views
/// and observation facts. The consuming state retains its own locals and
/// ledgers even when the projected resource partition can be shared.
pub(super) fn expand_certification_exit(
    function: &ProgramFunction,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    crate::kernel::functions::expand_all_composite_resource_facts_at_state(
        state.resources(),
        function.composite_resource_definitions(),
        state,
        assumptions,
    )
}

pub(super) struct RetainedExitProjection {
    interface: Arc<FunctionContractInterface>,
    raw_memory: SymbolicMemory,
    raw_point: Option<ProgramPointId>,
    point: PathLink,
    population_effects: Arc<PopulationEffects>,
    assumptions: PureFactContext,
    logical_reads: u64,
    memory: SymbolicMemory,
    input_resources: ResourceContext,
    resources: ResourceContext,
}

impl RetainedExitProjection {
    fn matches(
        &self,
        function: &ProgramFunction,
        raw: &ExecutionState,
        at_exit: &ExecutionState,
        assumptions: &PureFactContext,
        logical_reads: u64,
    ) -> bool {
        // Expansion reads the raw exit's resource partition, its memory and
        // path, and the creation ledger for authority controls. No local
        // variable environment is read by body expansion: every body binds
        // its own explicit resource arguments.
        Arc::ptr_eq(&self.interface, &function.contract_interface)
            && self.raw_memory.same_storage_roots(raw.memory())
            && self.raw_point == raw.point.id()
            && same_optional_root(&self.raw_memory.pending_steps, &raw.memory().pending_steps)
            && self.memory.same_storage_roots(at_exit.memory())
            && self
                .input_resources
                .shares_projection_inputs_with(at_exit.resources())
            && Arc::ptr_eq(&self.population_effects, &at_exit.population_effects)
            && self.logical_reads == logical_reads
            && self.assumptions.shares_persistent_storage_with(assumptions)
            && self.assumptions.content_fingerprint == assumptions.content_fingerprint
            && self
                .assumptions
                .equality_graph
                .admitted
                .typed_pointer_read_definitions
                .shares_root_with(
                    &assumptions
                        .equality_graph
                        .admitted
                        .typed_pointer_read_definitions,
                )
            && self.assumptions.reasoning_policy == assumptions.reasoning_policy
            && self.assumptions.decided_algebraic_ifs == assumptions.decided_algebraic_ifs
            && same_optional_root(&self.assumptions.store_owners, &assumptions.store_owners)
            && self.assumptions.equality_graph.input_key() == assumptions.equality_graph.input_key()
            && self
                .assumptions
                .equality_graph
                .shares_read_configuration_with(&assumptions.equality_graph)
    }
}

fn same_optional_root<T>(left: &Option<Arc<T>>, right: &Option<Arc<T>>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        (None, None) => true,
        _ => false,
    }
}

/// The already checked transfer supplies the footprint's entry state and
/// clause metadata. Projection failures belong to the open footprint goal.
#[derive(Clone)]
pub(crate) struct RetainedClosingFootprint {
    pub(super) state: ExecutionState,
    pub(super) resources: Option<Arc<[CheckedResourceFact]>>,
    pub(super) entry_assumptions: PureFactContext,
    pub(super) projection: std::sync::OnceLock<Result<FunctionMemoryEffectProjection, String>>,
}

impl RetainedClosingFootprint {
    pub(in crate::kernel) fn from_transfer(
        transfer: &crate::kernel::functions::CheckedBoundaryResourceTransfer,
        assumptions: &PureFactContext,
    ) -> Self {
        let function = transfer.checked_function();
        let state = transfer.callee_entry().clone();
        let resources = function
            .resource_derived_mutable_frame()
            .then(|| Arc::<[CheckedResourceFact]>::from(transfer.checked_entry_clauses()));
        Self {
            state,
            resources,
            entry_assumptions: assumptions.clone(),
            projection: std::sync::OnceLock::new(),
        }
    }

    /// Range checking is part of the still-open footprint goal. Its immutable
    /// entry inputs are retained even when this function never writes storage.
    pub(super) fn projection(
        &self,
        function: &ProgramFunction,
    ) -> Result<&FunctionMemoryEffectProjection, String> {
        self.projection
            .get_or_init(|| {
                project_contract_memory_effects(
                    &self.state,
                    function.contract_interface(),
                    self.resources.as_deref(),
                    &self.entry_assumptions,
                    &mut ExecutionBudget::beside_live_state(),
                )
                .map_err(|limit| limit.describe())
                .and_then(|projection| projection)
            })
            .as_ref()
            .map_err(Clone::clone)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(
        clauses: usize,
        unrelated: usize,
    ) -> (
        ProgramFunction,
        Arc<PreparedContractEntryCases>,
        SymbolicExecutionPath,
        FunctionOutcome,
    ) {
        let requirements = (0..clauses)
            .map(|index| {
                ResourceSpec::token(
                    ResourceAccessMode::Own,
                    format!("input_{index}"),
                    vec![],
                    vec![],
                )
            })
            .collect::<Vec<_>>();
        let function = program_function(
            ProgramType::Void,
            "retained_entry",
            vec![],
            ProgramStatement::Skip,
        )
        .with_resource_summary(requirements.clone(), requirements)
        .with_contract(
            (0..unrelated)
                .map(|index| SpecProposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                    resource_state_dependent: false,
                })
                .collect(),
            vec![],
            vec![],
            std::iter::once(FunctionContractClaim::body_safety())
                .chain(
                    (0..clauses).map(|index| FunctionContractClaim::ensure_resource(index, index)),
                )
                .collect(),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_facts(
            (0..clauses).map(|index| ResourceFact::own_token(format!("input_{index}"), vec![])),
        );
        let caller = ExecutionState::new().with_resource_context(resources);
        let environment = ExecutionEnvironment::new();
        let opened = crate::kernel::proof::OpenedContractEntry::open(
            &caller,
            &function,
            &[],
            &Vec::<Proposition>::new(),
            &environment,
        )
        .unwrap();
        let entry = opened.prepared_cases().clone();
        assert!(
            entry.closing_footprint.get().is_some(),
            "entry opening owns footprint preparation"
        );
        let execution = prove_checked_program_function_execution_with_environment(
            caller,
            function.clone(),
            vec![],
            entry.closing_entry.assumptions.clone(),
            environment,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        );
        let path = execution.paths()[0].clone();
        let outcome = path_function_outcome(&path).unwrap().clone();
        assert!(
            matches!(outcome, FunctionOutcome::Return { .. }),
            "the fixture must return"
        );
        (function, entry, path, outcome)
    }

    #[test]
    fn closing_reuses_the_entry_clauses_instead_of_evaluating_them_again() {
        let (function, entry, path, outcome) = fixture(2, 0);
        assert!(
            entry.closing_entry.projection.is_none(),
            "no effect clause requests a projection"
        );
        assert!(
            entry
                .closing_footprint
                .get()
                .unwrap()
                .projection
                .get()
                .is_none(),
            "entry opening retains footprint inputs without checking an unused goal"
        );
        let (prepared, attempts) =
            crate::kernel::functions::measure_resource_clause_attempts(|| {
                prepare_closing_path(
                    &function,
                    &path,
                    &entry.closing_entry,
                    &outcome,
                    vec![],
                    false,
                    false,
                    None,
                    false,
                    None,
                )
            });
        let prepared = prepared.unwrap();
        assert_eq!(attempts, 0);
        assert!(Arc::ptr_eq(
            &prepared.checked_required_resources,
            &entry.closing_entry.checked
        ));
        assert!(
            FunctionEnsureGoalContext::from_retained_entry(
                &function,
                &entry.closing_entry,
                &outcome,
                &entry.closing_entry.assumptions,
            )
            .is_some()
        );
        // The independent API keeps its established clause-evaluation route.
        let (independent, attempts) =
            crate::kernel::functions::measure_resource_clause_attempts(|| {
                prepare_function_claim_path(
                    &function,
                    &path,
                    vec![],
                    false,
                    false,
                    None,
                    false,
                    None,
                    Some(&outcome),
                )
            });
        assert!(independent.is_ok());
        assert!(attempts >= 2);
    }

    #[test]
    fn goal_preparation_and_closing_share_the_same_exit_partition() {
        let (function, entry, mut path, mut outcome) = fixture(0, 0);
        let function =
            function.with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
                "boxed",
                vec![],
                None,
                false,
                vec![ResourceSpec::token(
                    ResourceAccessMode::Own,
                    "child".to_string(),
                    vec![],
                    vec![],
                )],
                vec![],
            )]);
        let FunctionOutcome::Return { state, .. } = &mut outcome else {
            unreachable!()
        };
        **state = (**state).clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_fact(ResourceFact::own_composite("boxed".into(), vec![])),
        );
        let retained = &entry.closing_entry;
        let assumptions = retained.assumptions.clone();
        path.post_assumptions = Some(assumptions.clone());
        let prepared = FunctionEnsureGoalContext::from_retained_entry(
            &function,
            retained,
            &outcome,
            &assumptions,
        )
        .unwrap();
        let closed = prepare_closing_path(
            &function,
            &path,
            retained,
            &outcome,
            vec![],
            false,
            false,
            None,
            false,
            None,
        )
        .unwrap();
        assert!(
            prepared
                .post_state
                .resources()
                .shares_storage_with(closed.post_resources.as_ref().unwrap())
        );
    }

    #[test]
    fn a_return_case_shares_clause_metadata_and_keeps_its_guard() {
        let (state, function, arguments) =
            super::super::super::prepared_entry_cases_tests::fixture(1, 0);
        let opened = crate::kernel::proof::OpenedContractEntry::open(
            &state,
            &function,
            &arguments,
            &Vec::<Proposition>::new(),
            &ExecutionEnvironment::new(),
        )
        .unwrap();
        let entry = &opened.prepared_cases().closing_entry;
        let guards =
            contract_resource_guards(&state, &function, &arguments, &entry.assumptions).unwrap();
        assert_eq!(guards.len(), 1);
        let case = entry.for_resource_case(&function, &guards).unwrap();
        assert!(Arc::ptr_eq(&case.checked, &entry.checked));
        assert!(case.assumptions.proves_exact(&guards[0]));
        assert!(!entry.assumptions.proves_exact(&guards[0]));
    }

    #[test]
    fn a_deferred_return_without_its_recorded_reason_is_an_internal_error() {
        let (function, entry, path, outcome) = fixture(0, 0);
        let result = prepare_closing_path(
            &function,
            &path,
            &entry.closing_entry,
            &outcome,
            vec![],
            false,
            true,
            None,
            false,
            None,
        );
        let Err(failure) = result else {
            panic!("a deferred return requires its original reason");
        };
        assert!(matches!(
            failure.into_closing_refusal(),
            ContractClosingRefusal::Internal(message) if message.contains("no valid boundary error")
        ));
    }

    #[test]
    fn a_write_outside_the_allowed_effect_ranges_reports_the_range() {
        let (function, entry, path, outcome) = fixture(0, 0);
        let mut prepared = prepare_closing_path(
            &function,
            &path,
            &entry.closing_entry,
            &outcome,
            vec![],
            false,
            false,
            None,
            false,
            None,
        )
        .unwrap();
        let memory = prepared.caller_state.memory().clone();
        let address = Address {
            base: "global:counter".into(),
            offset: OldAddressOffset::Constant(0),
        };
        let extent = crate::kernel::AccessExtent::Bytes(4);
        let range = MemoryRange::of_access(&address, extent);
        prepared.effect_facts = vec![crate::kernel::ExecutionPureFact::certified(
            Proposition::MemoryMutatesOnly {
                before: memory.clone(),
                after: memory,
                writes: vec![(address, extent)],
            },
        )]
        .into();
        assert!(matches!(
            check_effect_on_prepared_path(&function, &prepared, &prepared.assumptions),
            Err(ContractClosingRefusal::Range(actual)) if actual == range
        ));
    }

    mod scaling_tests {
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/retained_context.rs"
        );
    }
}
