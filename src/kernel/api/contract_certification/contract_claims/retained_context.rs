//! Entry inputs produced once and retained by ordinary contract closing.

use super::*;

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
}

impl std::fmt::Debug for RetainedClosingEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RetainedClosingEntry")
            .field("clauses", &self.checked.len())
            .finish_non_exhaustive()
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
        }
    }

    pub(in crate::kernel) fn for_case(
        &self,
        function: &ProgramFunction,
        state: ExecutionState,
        assumptions: PureFactContext,
    ) -> Self {
        Self::from_producer(
            self.caller.clone(),
            function,
            self.arguments.clone(),
            state,
            self.required.clone(),
            self.checked.clone(),
            assumptions,
            self.facts.to_vec(),
        )
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
                    ResourceContext::new(),
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
                    ResourceContext::new(),
                    false,
                    None,
                    Some(&outcome),
                )
            });
        assert!(independent.is_ok());
        assert!(attempts >= 2);
    }

    #[test]
    fn retained_entry_cases_keep_their_guards_and_shared_clause_metadata() {
        let (state, function, arguments) =
            super::super::super::prepared_entry_cases_tests::fixture(2, 0);
        let opened = crate::kernel::proof::OpenedContractEntry::open(
            &state,
            &function,
            &arguments,
            &Vec::<Proposition>::new(),
            &ExecutionEnvironment::new(),
        )
        .unwrap();
        let entry = opened.prepared_cases();
        for (case, guards) in entry.cases.iter().zip(&entry.guard_cases) {
            assert!(Arc::ptr_eq(
                &case.closing_entry.checked,
                &entry.closing_entry.checked
            ));
            for guard in guards {
                assert!(case.closing_entry.assumptions.proves_exact(guard));
                assert!(
                    !case
                        .closing_entry
                        .assumptions
                        .proves_exact(&negate_contract_case_proposition(guard))
                );
            }
        }
    }

    mod scaling_tests {
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/retained_context.rs"
        );
    }
}
