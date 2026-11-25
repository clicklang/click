//! Producer-bound publication of a function outcome and its claim theorems.

use super::*;
use crate::kernel::proof::{OutcomeExecutionFacts, OutcomeIdentity, OutcomeProofCore};

/// Created alongside the checked path, from the producer's own inputs. The
/// specification and ordinary outcome goal retain the same generative binding.
#[derive(Clone)]
pub(crate) struct PublishedFunctionOutcome {
    identity: OutcomeIdentity,
    version: Arc<()>,
    function: ProgramFunction,
    specification: FunctionSpecification,
    theorem: Theorem,
    path_origin: Theorem,
    path: SymbolicExecutionPath,
    return_seed: Arc<crate::kernel::proof::CheckedReturnSeed>,
    return_status: Option<(bool, Option<RuntimeError>)>,
    core: Option<OutcomeProofCore>,
}

impl std::fmt::Debug for PublishedFunctionOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublishedFunctionOutcome")
            .field("function", &self.function.name())
            .finish_non_exhaustive()
    }
}
impl PartialEq for PublishedFunctionOutcome {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.version, &other.version)
    }
}
impl Eq for PublishedFunctionOutcome {}

impl PublishedFunctionOutcome {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::kernel) fn from_execution(
        state: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        assumptions: &PureFactContext,
        facts: &ExecutionFacts,
        obligations: &[ProofObligation],
        outcome: &FunctionOutcome,
        candidate: &FunctionExecutionCandidate,
        path: &SymbolicExecutionPath,
        return_seed: Arc<crate::kernel::proof::CheckedReturnSeed>,
    ) -> Arc<Self> {
        let identity = OutcomeIdentity::fresh();
        let specification = FunctionSpecification::new(
            state.clone(),
            arguments.to_vec(),
            assumptions.pure_facts(),
            outcome.clone(),
        );
        let conclusion = Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: Box::new(function.clone()),
            specification: Box::new(specification.clone()),
        };
        // These premises are the theorem's explicit output, shared with the
        // path producer's inputs; no theorem is parsed or compared here.
        let conclusion = specification
            .requires()
            .iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise.clone()), Box::new(body))
            });
        let theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
            conclusion,
            assumptions,
            facts,
            obligations,
        ));
        let core = match candidate.outcome() {
            FunctionOutcome::Return { value, state } | FunctionOutcome::Throw { value, state } => {
                Some(OutcomeProofCore {
                    publication: None,
                    identity: identity.clone(),
                    result: value.clone(),
                    store_consequences_available: false,
                    state: (**state).clone().into(),
                    is_exceptional: matches!(candidate.outcome(), FunctionOutcome::Throw { .. }),
                    effect_facts: OutcomeExecutionFacts::merging(
                        candidate.facts().clone(),
                        candidate.effect_facts().clone(),
                    ),
                })
            }
            _ => None,
        };
        Arc::new(Self {
            identity,
            version: Arc::new(()),
            function: function.clone(),
            specification,
            theorem,
            path_origin: path.theorem.clone(),
            path: path.clone(),
            return_seed,
            return_status: None,
            core,
        })
    }

    pub(crate) fn path(&self) -> &SymbolicExecutionPath {
        &self.path
    }
    pub(in crate::kernel) fn return_seed(&self) -> &Arc<crate::kernel::proof::CheckedReturnSeed> {
        &self.return_seed
    }

    pub(in crate::kernel) fn with_return_path(
        self: &Arc<Self>,
        path: SymbolicExecutionPath,
        outcome: FunctionOutcome,
        deferred: bool,
        error: Option<RuntimeError>,
    ) -> Arc<Self> {
        let mut next = self.as_ref().clone();
        next.version = Arc::new(());
        next.specification = FunctionSpecification::new(
            self.specification.state().clone(),
            self.specification.arguments().to_vec(),
            self.specification.requires().to_vec(),
            outcome,
        );
        let conclusion = Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: Box::new(self.function.clone()),
            specification: Box::new(next.specification.clone()),
        };
        let conclusion = next
            .specification
            .requires()
            .iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise.clone()), Box::new(body))
            });
        next.theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
            conclusion,
            &path.assumptions,
            &path.facts,
            self.return_seed.obligations(),
        ));
        next.path_origin = path.theorem.clone();
        next.path = path;
        next.return_status = Some((deferred, error));
        Arc::new(next)
    }

    pub(in crate::kernel) fn return_status(&self) -> Option<&(bool, Option<RuntimeError>)> {
        self.return_status.as_ref()
    }

    pub(crate) fn specification(&self) -> &FunctionSpecification {
        &self.specification
    }
    pub(crate) fn theorem(&self) -> &Theorem {
        &self.theorem
    }

    pub(in crate::kernel) fn open_core(self: &Arc<Self>) -> Option<OutcomeProofCore> {
        self.core.clone().map(|mut core| {
            core.identity = OutcomeIdentity::fresh();
            core.publication = Some(self.clone());
            core
        })
    }

    pub(in crate::kernel) fn belongs_to(&self, original: &Self) -> bool {
        self.identity.same_as(&original.identity)
    }

    /// The ordinary claim goal already bound and checked this completion.
    pub(in crate::kernel) fn publish_claim(
        &self,
        completion: &crate::kernel::proof::CheckedProposition,
    ) -> CheckedFunctionProposition {
        CheckedFunctionProposition {
            path_origin: Some(self.path_origin.clone()),
            function: self.function.clone(),
            specification: self.specification.clone(),
            proposition: completion.proposition().clone(),
            claim: completion.claim().cloned(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::*;
    type Root =
        ProofObject<(), crate::kernel::proof::ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;

    fn fixture() -> (CheckedFunctionExecution, Root) {
        let (_, execution) =
            super::super::super::entry_authority_tests::checked_execution(0, None).unwrap();
        let mut goal = FunctionOutcomeObligation::new(
            0,
            Arc::new(OutcomeProofState::new(
                execution.open_outcome(0).unwrap(),
                (),
            )),
        );
        goal.claims = Some(OutcomeClaimGoals::open(
            [(
                FunctionContractClaimKey::Ensure(0),
                Some(FunctionContractClaimTarget::EnsureProposition(0)),
            )],
            false,
        ));
        let truth =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true);
        let root = Root::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::FunctionOutcome(goal),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(&[truth]),
                    execution: None,
                },
            ),
        );
        (execution, root)
    }

    fn publish_result(
        seed: &Arc<PublishedFunctionOutcome>,
        value: StoredExecutionValue,
        exceptional: bool,
    ) -> Arc<PublishedFunctionOutcome> {
        let state = ExecutionState::new();
        let function = ProgramFunction::new(
            value.program_type(),
            "retained_publication",
            vec![],
            ProgramStatement::Skip,
        );
        let outcome = if exceptional {
            FunctionOutcome::Throw {
                value,
                state: Box::new(state.clone()),
            }
        } else {
            FunctionOutcome::Return {
                value,
                state: Box::new(state.clone()),
            }
        };
        let candidates = program_function_execution_candidates_from_outcomes(
            state.clone(),
            function.clone(),
            vec![],
            vec![(outcome.clone(), vec![], vec![])],
        );
        PublishedFunctionOutcome::from_execution(
            &state,
            &function,
            &[],
            &PureFactContext::new(),
            &ExecutionFacts::default(),
            &[],
            &outcome,
            candidates.candidate_at(0).unwrap(),
            seed.path(),
            seed.return_seed().clone(),
        )
    }

    #[test]
    fn publication_keeps_return_and_exception_operands_and_storage_identity() {
        use crate::kernel::{ExecutionValue, KernelTerm, KernelTermImport, KernelType};
        let _session = crate::kernel::VerificationSession::enter();
        let (execution, _) = fixture();
        let seed = execution.published_outcome(0);
        let pointer = OldPointer::new(
            OldAddress::symbolic(Variable(996901)),
            ProgramType::Int32Pointer,
        );
        let roots = [
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(996906)),
            KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996902)),
            KernelTerm::variable(KernelType::Program(ProgramType::Float64), Variable(996903)),
            KernelTermImport::default().condition(&OldConditionTerm::Variable(Variable(996904))),
            KernelTerm::shared_pointer_value(crate::kernel::SharedPointer::import(&pointer)),
            KernelTerm::variable(
                KernelType::Algebraic(crate::kernel::AlgebraicType::parameter("T".into())),
                Variable(996905),
            ),
        ];
        for root in roots {
            let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let native = value.clone().into_native();
            for exceptional in [false, true] {
                if exceptional && value.program_type() != ProgramType::Int32 {
                    continue;
                }
                let publication = publish_result(seed, value.clone(), exceptional);
                let opened = publication.open_core().unwrap();
                assert_eq!(opened.result.shared(), Some(&root));
                assert_eq!(opened.is_exceptional, exceptional);
                assert_eq!(opened.result, value);
                assert!(opened.result.matches_native(&native));
                assert_eq!(opened.result.clone().into_native(), native);
                let distinct = StoredExecutionValue::from(crate::kernel::int32(42));
                assert_eq!(value == distinct, distinct.matches_native(&native));
                let reopened = publication.open_core().unwrap();
                assert_eq!(reopened.result.shared(), Some(&root));
                assert!(!opened.identity.same_as(&reopened.identity));
            }
        }
    }

    fn close_claim(root: &Root) -> Root {
        let claim = ContractClaimGoal {
            target: FunctionContractClaimTarget::EnsureProposition(0),
            proposition: Proposition::condition_is(
                crate::kernel::OldConditionTerm::Constant(true),
                true,
            ),
            facts: vec![],
            obligations: vec![],
        };
        let proof = root
            .focus_contract_claim(&claim, ())
            .unwrap()
            .apply_known(PropositionKnownContext::Exact)
            .unwrap_or_else(|_| panic!("the selected true claim closes"));
        let branch = root
            .state()
            .open_branches()
            .get(root.focused_branch())
            .unwrap();
        let crate::kernel::proof::ProofObligation::FunctionOutcome(goal) = &branch.obligation
        else {
            unreachable!()
        };
        let mut goal = goal.clone();
        goal.claims = Some(
            goal.claims
                .as_ref()
                .unwrap()
                .close(
                    &FunctionContractClaimKey::Ensure(0),
                    ClaimGoalEvidence::Proposition(proof.completed_proposition().unwrap()),
                    &goal.data.core.identity,
                )
                .unwrap(),
        );
        root.replace_focused_obligation(crate::kernel::proof::ProofObligation::FunctionOutcome(
            goal,
        ))
        .unwrap_or_else(|_| panic!("the owning outcome stays open"))
    }

    #[test]
    fn ordinary_goal_publishes_its_producers_specification_without_revalidation() {
        let (execution, root) = fixture();
        assert!(
            root.published_contract_claim(&FunctionContractClaimKey::Ensure(0))
                .is_none()
        );
        let closed = close_claim(&root);
        let published = closed
            .published_contract_claim(&FunctionContractClaimKey::Ensure(0))
            .unwrap();
        assert!(Arc::ptr_eq(
            &published.path_origin.as_ref().unwrap().proposition,
            &execution.paths()[0].theorem.proposition
        ));
        assert_eq!(
            &published.specification,
            execution.published_outcome(0).specification()
        );
        assert_eq!(
            published.claim,
            Some(FunctionContractClaimTarget::EnsureProposition(0))
        );
        assert!(
            closed
                .published_contract_claim(&FunctionContractClaimKey::Ensure(1))
                .is_none()
        );
        assert!(
            root.published_contract_claim(&FunctionContractClaimKey::Ensure(0))
                .is_none(),
            "an ancestor did not acquire the closed goal"
        );
    }

    #[test]
    fn an_unbound_frontier_completion_cannot_close_an_outcome_claim() {
        let (_, root) = fixture();
        let branch = root
            .state()
            .open_branches()
            .get(root.focused_branch())
            .unwrap();
        let frontier = Root::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::Frontier(FrontierObligation),
                branch.state.clone(),
            ),
        );
        let claim = ContractClaimGoal {
            target: FunctionContractClaimTarget::EnsureProposition(0),
            proposition: Proposition::condition_is(
                crate::kernel::OldConditionTerm::Constant(true),
                true,
            ),
            facts: vec![],
            obligations: vec![],
        };
        let proved = frontier
            .focus_contract_claim(&claim, ())
            .unwrap()
            .apply_known(PropositionKnownContext::Exact)
            .unwrap_or_else(|_| panic!("the true frontier goal closes"));
        let proof = proved.completed_proposition().unwrap();
        assert!(proof.outcome().is_none());
        let crate::kernel::proof::ProofObligation::FunctionOutcome(goal) = &branch.obligation
        else {
            unreachable!()
        };
        assert!(matches!(
            goal.claims.as_ref().unwrap().close(
                &FunctionContractClaimKey::Ensure(0),
                ClaimGoalEvidence::Proposition(proof),
                &goal.data.core.identity
            ),
            Err(ClaimGoalError::WrongOutcome)
        ));
    }

    #[test]
    fn producer_publication_preserves_the_original_path_theorem_premises() {
        for requirements in [0, 3, 16] {
            let (_, execution) =
                super::super::super::entry_authority_tests::checked_execution(requirements, None)
                    .unwrap();
            let publication = execution.published_outcome(0);
            let expected = prove_program_function_satisfies_specification_from_symbolic_path(
                execution.function.clone(),
                publication.specification().clone(),
                &execution.paths()[0],
            )
            .unwrap();
            assert_eq!(publication.theorem(), &expected);
        }
    }

    #[test]
    fn reopening_one_publication_keeps_ordinary_proof_owners_distinct() {
        let (execution, root) = fixture();
        let first = execution.open_outcome(0).unwrap();
        let second = execution.open_outcome(0).unwrap();
        assert!(!first.identity.same_as(&second.identity));
        assert!(Arc::ptr_eq(
            first.publication.as_ref().unwrap(),
            second.publication.as_ref().unwrap()
        ));
        let branch = root
            .state()
            .open_branches()
            .get(root.focused_branch())
            .unwrap();
        let crate::kernel::proof::ProofObligation::FunctionOutcome(goal) = &branch.obligation
        else {
            unreachable!()
        };
        assert!(!first.identity.same_as(&goal.data.core.identity));
    }

    #[test]
    fn equal_looking_foreign_publications_cannot_replace_an_outcome_binding() {
        let (execution, root) = fixture();
        let (foreign, _) = fixture();
        assert_eq!(
            execution.published_outcome(0).specification(),
            foreign.published_outcome(0).specification()
        );
        assert!(
            root.bind_outcome_publication(foreign.published_outcome(0).clone())
                .is_err()
        );
        assert!(
            root.bind_outcome_publication(execution.published_outcome(0).clone())
                .is_ok()
        );
        let closed = close_claim(&root);
        assert!(
            closed
                .published_contract_claim(&FunctionContractClaimKey::Ensure(0))
                .is_some()
        );
    }

    mod scaling_tests {
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/publication.rs"
        );
    }
}
