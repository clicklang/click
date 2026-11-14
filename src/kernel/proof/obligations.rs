//! Surface-independent proof obligations and checked capabilities.
//!
//! These values describe what a checked proof branch still owes. They carry
//! no Surface Click syntax, source selector, diagnostic data, or smart-plan
//! state.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use super::storage::SharedValue;
use crate::kernel::{
    ExecutionState, FunctionContractClaimKey, FunctionContractClaimTarget, ProgramValue,
    Proposition, ResourceFact,
};

/// Diagnostic evidence returned when an allocation-lifetime obligation could
/// not be discharged. The allocation is semantic evidence; the optional
/// holder is diagnostic provenance identifying the declared resource that
/// still accounts for it. This is deliberately distinct from the open proof
/// obligation below: a successful check has no leaked-allocation payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LiveAllocationObligation {
    allocation: ResourceFact,
    holder: Option<ResourceFact>,
}

impl LiveAllocationObligation {
    pub(crate) fn new(allocation: ResourceFact, holder: Option<ResourceFact>) -> Self {
        Self { allocation, holder }
    }

    pub(crate) fn allocation(&self) -> &ResourceFact {
        &self.allocation
    }

    pub(crate) fn holder(&self) -> Option<&ResourceFact> {
        self.holder.as_ref()
    }
}

/// One open C frontier judgment's remaining semantic obligation.
///
/// A frontier judgment carries no payload of its own: reaching the frontier
/// is the obligation, and every semantic detail lives in the branch state.
#[derive(Clone)]
pub(crate) struct FrontierObligation;

/// One proposition branch obligation with opaque presentation data.
#[derive(Clone)]
pub(crate) struct PropositionObligation<S, O> {
    proposition: Arc<Proposition>,
    pub(crate) presentation: S,
    pub(crate) outcome: Option<O>,
    /// The contract claim this obligation states, when it was opened from
    /// the kernel's goal for that claim.
    claim: Option<crate::kernel::FunctionContractClaimTarget>,
}

impl<S, O> PropositionObligation<S, O> {
    pub(crate) fn new(proposition: Proposition, presentation: S) -> Self {
        Self {
            proposition: Arc::new(proposition),
            presentation,
            outcome: None,
            claim: None,
        }
    }

    pub(crate) fn at_outcome(proposition: Proposition, presentation: S, outcome: O) -> Self {
        Self {
            proposition: Arc::new(proposition),
            presentation,
            outcome: Some(outcome),
            claim: None,
        }
    }

    /// The obligation to prove the kernel's goal for one contract claim. Its
    /// proposition is the goal's own, so the claim it records is the claim
    /// it states.
    pub(super) fn for_claim_goal(
        goal: &crate::kernel::ContractClaimGoal,
        presentation: S,
        outcome: Option<O>,
    ) -> Self {
        Self {
            proposition: Arc::new(goal.proposition().clone()),
            presentation,
            outcome,
            claim: Some(goal.target().clone()),
        }
    }

    pub(crate) fn claim(&self) -> Option<&crate::kernel::FunctionContractClaimTarget> {
        self.claim.as_ref()
    }

    /// The same obligation under another presentation: what is to be proved,
    /// and for which claim, is unchanged.
    pub(crate) fn with_presentation(&self, presentation: S) -> Self
    where
        O: Clone,
    {
        Self {
            proposition: self.proposition.clone(),
            presentation,
            outcome: self.outcome.clone(),
            claim: self.claim.clone(),
        }
    }

    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

impl<S, O> Deref for PropositionObligation<S, O> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S, O> DerefMut for PropositionObligation<S, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

/// Identity of one producer-owned execution outcome. Proposition scopes
/// retain it even when they allocate their own local proof branch IDs.
#[derive(Clone)]
pub(crate) struct OutcomeIdentity(Arc<()>);
impl OutcomeIdentity {
    pub(crate) fn fresh() -> Self {
        Self(Arc::new(()))
    }
    pub(crate) fn same_as(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Surface-independent payload-aware state for one checked function outcome.
#[derive(Clone)]
pub(crate) struct OutcomeProofCore {
    pub(crate) identity: OutcomeIdentity,
    pub(crate) result: Arc<ProgramValue>,
    pub(crate) store_consequences_available: bool,
    pub(crate) state: SharedValue<ExecutionState>,
    pub(crate) is_exceptional: bool,
    pub(crate) effect_facts: OutcomeExecutionFacts,
}

/// A checked outcome's facts and then the effects they do not repeat, as one
/// stream. Publishing an outcome keeps the path's two shared streams; most
/// outcome goals never read the merged stream, and merging it for every
/// published path costs each path its whole history.
#[derive(Clone)]
pub(crate) struct OutcomeExecutionFacts {
    facts: crate::kernel::ExecutionFacts,
    effects: crate::kernel::ExecutionFacts,
    merged: Arc<std::sync::OnceLock<crate::kernel::ExecutionFacts>>,
}

impl OutcomeExecutionFacts {
    pub(crate) fn merging(
        facts: crate::kernel::ExecutionFacts,
        effects: crate::kernel::ExecutionFacts,
    ) -> Self {
        Self {
            facts,
            effects,
            merged: Arc::default(),
        }
    }
}

impl From<crate::kernel::ExecutionFacts> for OutcomeExecutionFacts {
    fn from(facts: crate::kernel::ExecutionFacts) -> Self {
        Self::merging(facts, crate::kernel::ExecutionFacts::new())
    }
}

impl Deref for OutcomeExecutionFacts {
    type Target = crate::kernel::ExecutionFacts;

    fn deref(&self) -> &Self::Target {
        self.merged.get_or_init(|| {
            if self.effects.is_empty() {
                return self.facts.clone();
            }
            #[cfg(test)]
            crate::kernel::assumptions::count_materialized_execution_facts(
                self.facts.len() + self.effects.len(),
            );
            let mut merged = self.facts.clone();
            let effects = self.effects.filtered(|fact| !merged.contains(fact));
            merged.extend_shared(&effects);
            merged
        })
    }
}

impl AsRef<crate::kernel::ExecutionFacts> for OutcomeExecutionFacts {
    fn as_ref(&self) -> &crate::kernel::ExecutionFacts {
        self
    }
}

/// Durable kernel evidence that one exact proposition judgment was closed.
///
/// The proposition, the root assumptions it was closed under, and the optional
/// function outcome all come from the root semantic obligation retained by
/// [`ProofObject`](super::ProofObject); surface provenance cannot manufacture
/// or retarget this value after completion. Retaining the root facts lets a
/// theorem constructor check which assumptions the proof actually stood on
/// instead of re-proving its conclusion. The fact store is persistent, so
/// keeping it costs a shared reference, not a copy of the context.
#[derive(Clone)]
pub(crate) struct CheckedProposition {
    proposition: Arc<Proposition>,
    root_assumptions: super::ProofFacts,
    outcome: Option<OutcomeProofCore>,
    claim: Option<crate::kernel::FunctionContractClaimTarget>,
}

impl CheckedProposition {
    pub(super) fn new(
        proposition: Proposition,
        root_assumptions: super::ProofFacts,
        outcome: Option<OutcomeProofCore>,
        claim: Option<crate::kernel::FunctionContractClaimTarget>,
    ) -> Self {
        Self {
            proposition: Arc::new(proposition),
            root_assumptions,
            outcome,
            claim,
        }
    }

    /// The contract claim whose kernel-issued goal this proof closed.
    pub(crate) fn claim(&self) -> Option<&crate::kernel::FunctionContractClaimTarget> {
        self.claim.as_ref()
    }

    /// Whether the completed proof stood on no root assumption at all.
    pub(crate) fn is_closed(&self) -> bool {
        self.root_assumptions.is_empty()
    }

    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// From a checked P, derive A1 implies ... implies P under the same
    /// root assumptions and outcome. The caller supplies the prefix length,
    /// so checking visits that prefix and compares the terminal body once.
    /// This does not discharge or replace any assumption of the original proof.
    pub(crate) fn with_implication_prefix(
        &self,
        goal: &Proposition,
        prefix_len: usize,
    ) -> Option<Self> {
        let mut body = goal;
        for _ in 0..prefix_len {
            let Proposition::Implies(_, consequent) = body else {
                return None;
            };
            body = consequent;
        }
        if body != self.proposition() {
            return None;
        }
        Some(Self {
            proposition: Arc::new(goal.clone()),
            root_assumptions: self.root_assumptions.clone(),
            outcome: self.outcome.clone(),
            // The derived implication is not the claim's own goal.
            claim: None,
        })
    }

    /// The exact facts the root branch assumed. A constructor that turns this
    /// completion into an implication must check them against its own
    /// explicit premises.
    pub(crate) fn root_assumptions(&self) -> &super::ProofFacts {
        &self.root_assumptions
    }

    pub(crate) fn outcome(&self) -> Option<&OutcomeProofCore> {
        self.outcome.as_ref()
    }
}

/// One checked function outcome paired with opaque language presentation.
#[derive(Clone)]
pub(crate) struct OutcomeProofState<S> {
    pub(crate) core: OutcomeProofCore,
    pub(crate) presentation: S,
}

impl<S> OutcomeProofState<S> {
    pub(crate) fn new(core: OutcomeProofCore, presentation: S) -> Self {
        Self { core, presentation }
    }
}

impl<S> Deref for OutcomeProofState<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S> DerefMut for OutcomeProofState<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

/// The contract closer's distinct ordinary obligations, in proof order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ContractClosingGoal {
    ReturnedResources,
    AllocationLifetime,
    WriteFootprint,
}

impl ContractClosingGoal {
    const ORDER: [Self; 3] = [
        Self::ReturnedResources,
        Self::AllocationLifetime,
        Self::WriteFootprint,
    ];

    pub(crate) const COUNT: usize = Self::ORDER.len();

    pub(crate) fn description(self) -> &'static str {
        match self {
            Self::ReturnedResources => "joint returned resources",
            Self::AllocationLifetime => "allocation lifetime",
            Self::WriteFootprint => "write footprint",
        }
    }

    fn bit(self) -> u8 {
        1 << self as u8
    }
}

/// Persistent fixed-size goal state; closing one goal never visits claims or facts.
#[derive(Clone, Copy)]
pub(crate) struct ContractClosingGoals {
    open: u8,
}

impl ContractClosingGoals {
    pub(in crate::kernel) fn open() -> Self {
        Self { open: 0b111 }
    }

    pub(crate) fn first_open(self) -> Option<ContractClosingGoal> {
        crate::instrumentation::record_deterministic_work(1);
        ContractClosingGoal::ORDER
            .into_iter()
            .find(|goal| !self.is_closed(*goal))
    }

    pub(crate) fn is_closed(self, goal: ContractClosingGoal) -> bool {
        self.open & goal.bit() == 0
    }

    pub(in crate::kernel) fn close(self, goal: ContractClosingGoal) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self {
            open: self.open & !goal.bit(),
        }
    }

    pub(in crate::kernel) fn reopen(self, goal: ContractClosingGoal) -> Self {
        Self {
            open: self.open | goal.bit(),
        }
    }
}

/// One selector for source clauses and obligations introduced by contract closing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OutcomeGoal {
    Claim {
        position: usize,
        key: FunctionContractClaimKey,
    },
    Closing(ContractClosingGoal),
}

/// The remaining obligation for one checked returning path, paired with
/// opaque result-presentation data.
#[derive(Clone)]
pub(crate) struct FunctionOutcomeObligation<S> {
    pub(crate) path_index: usize,
    pub(crate) data: S,
    /// The contract claims this path owes, once opened at function exit.
    pub(crate) claims: Option<OutcomeClaimGoals>,
    /// Joint resource/lifetime and write-footprint goals generated by closing.
    pub(crate) closing: Option<crate::kernel::ContractExitObligations>,
}

impl<S> FunctionOutcomeObligation<S> {
    pub(crate) fn new(path_index: usize, data: S) -> Self {
        Self {
            path_index,
            data,
            claims: None,
            closing: None,
        }
    }
}

impl<S> FunctionOutcomeObligation<S> {
    /// Unopened contracts cannot be mistaken for completed contracts.
    pub(crate) fn first_open_goal(&self) -> Result<Option<OutcomeGoal>, &'static str> {
        let claims = self
            .claims
            .as_ref()
            .ok_or("contract claim obligations have not been opened")?;
        let closing = self
            .closing
            .as_ref()
            .ok_or("contract closing obligations have not been opened")?;
        if let Some((position, key)) = claims.first_open_goal() {
            return Ok(Some(OutcomeGoal::Claim {
                position,
                key: key.clone(),
            }));
        }
        Ok(closing.first_open_goal().map(OutcomeGoal::Closing))
    }
}

/// Why a claim goal of an outcome path could not be closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ClaimGoalError {
    /// The path owes no such claim.
    Unknown,
    /// The claim is already closed on this path.
    AlreadyClosed,
    /// The completion names a different claim.
    WrongClaim,
    /// The completion was proved about a different outcome.
    WrongOutcome,
}

/// The kernel evidence that closed one claim goal of an outcome path.
#[derive(Clone)]
pub(crate) enum ClaimGoalEvidence {
    /// A checked completion of the claim's proposition.
    Proposition(CheckedProposition),
    /// A resource claim checked against the path's outcome, with the
    /// resources it accounts for in what the path returns.
    Resource(ClaimResourceReceipt),
}

/// What a checked resource claim accounts for in a path's returned
/// resources.
#[derive(Clone)]
pub(crate) struct ClaimResourceReceipt {
    pub(crate) returned_resources: crate::kernel::ResourceContext,
    /// Whether the receipt is a new returned owner rather than a borrow or a
    /// guarded transition still to come.
    pub(crate) contributes_returned_resources: bool,
    /// Whether the contract's resource transition is deferred to a guard.
    pub(crate) defers_resource_transition: bool,
}

/// The contract claims one outcome path owes, in the order the contract
/// writes them, each open or closed. A closer acts on the first open claim;
/// the path is finished when every claim is closed, and each closed claim
/// keeps the evidence that closed it.
///
/// A claim about the other kind of outcome (an `ensures` on a throwing path,
/// an exceptional `ensures` on a returning one) holds vacuously and opens
/// closed.
#[derive(Clone)]
pub(crate) struct OutcomeClaimGoals {
    claims: crate::persistent::PersistentMap<FunctionContractClaimKey, OutcomeClaimGoal>,
    open: crate::persistent::PersistentMap<usize, FunctionContractClaimKey>,
}

struct OutcomeClaimGoal {
    position: usize,
    /// The kernel claim the goal stands for. A clause the kernel files no
    /// claim for (a `consumes` transition) has none.
    target: Option<FunctionContractClaimTarget>,
    state: ClaimGoalState,
}

impl Clone for OutcomeClaimGoal {
    fn clone(&self) -> Self {
        // Charge copied entries, including if storage ever regresses to a
        // whole-collection copy. Persistent updates copy only this entry.
        crate::instrumentation::record_deterministic_work(1);
        Self {
            position: self.position,
            target: self.target.clone(),
            state: self.state.clone(),
        }
    }
}

#[derive(Clone)]
enum ClaimGoalState {
    Open,
    Vacuous,
    Closed(ClaimGoalEvidence),
}

impl OutcomeClaimGoals {
    pub(crate) fn open(
        claims: impl IntoIterator<
            Item = (
                FunctionContractClaimKey,
                Option<FunctionContractClaimTarget>,
            ),
        >,
        is_exceptional: bool,
    ) -> Self {
        let mut result = Self {
            claims: Default::default(),
            open: Default::default(),
        };
        for (position, (key, target)) in claims.into_iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            let vacuous = matches!(
                (&key, is_exceptional),
                (FunctionContractClaimKey::Ensure(_), true)
                    | (FunctionContractClaimKey::ExceptionalEnsure(_), false)
            );
            if !vacuous {
                result.open.insert(position, key.clone());
            }
            result.claims.insert(
                key,
                OutcomeClaimGoal {
                    position,
                    target,
                    state: if vacuous {
                        ClaimGoalState::Vacuous
                    } else {
                        ClaimGoalState::Open
                    },
                },
            );
        }
        result
    }

    fn first_open_goal(&self) -> Option<(usize, &FunctionContractClaimKey)> {
        crate::instrumentation::record_deterministic_work(1);
        self.open
            .iter()
            .next()
            .map(|(position, key)| (*position, key))
    }

    /// The claim a closer acts on, retaining the contract's input order.
    #[cfg(test)]
    pub(crate) fn first_open(&self) -> Option<&FunctionContractClaimKey> {
        crate::instrumentation::record_deterministic_work(1);
        self.open.iter().next().map(|(_, key)| key)
    }

    #[cfg(test)]
    pub(crate) fn first_open_position(&self) -> Option<usize> {
        crate::instrumentation::record_deterministic_work(1);
        self.open.iter().next().map(|(position, _)| *position)
    }

    pub(crate) fn target(
        &self,
        key: &FunctionContractClaimKey,
    ) -> Option<&FunctionContractClaimTarget> {
        crate::instrumentation::record_deterministic_work(1);
        self.claims.get(key)?.target.as_ref()
    }

    /// The evidence that closed `key`. A vacuous or open claim has none.
    pub(crate) fn evidence(&self, key: &FunctionContractClaimKey) -> Option<&ClaimGoalEvidence> {
        crate::instrumentation::record_deterministic_work(1);
        match &self.claims.get(key)?.state {
            ClaimGoalState::Closed(evidence) => Some(evidence),
            _ => None,
        }
    }

    /// Closes `key` with `evidence`. A checked completion must have been
    /// proved about `outcome`. A proposition postcondition requires the
    /// completion of its own kernel-created contract obligation.
    pub(crate) fn close(
        &self,
        key: &FunctionContractClaimKey,
        evidence: ClaimGoalEvidence,
        outcome: &OutcomeIdentity,
    ) -> Result<Self, ClaimGoalError> {
        crate::instrumentation::record_deterministic_work(1);
        let goal = self.claims.get(key).ok_or(ClaimGoalError::Unknown)?;
        if !matches!(goal.state, ClaimGoalState::Open) {
            return Err(ClaimGoalError::AlreadyClosed);
        }
        let proposition_claim = matches!(
            goal.target,
            Some(
                FunctionContractClaimTarget::EnsureProposition(_)
                    | FunctionContractClaimTarget::ExceptionalEnsureProposition(_)
            )
        );
        if proposition_claim && matches!(evidence, ClaimGoalEvidence::Resource(_)) {
            return Err(ClaimGoalError::WrongClaim);
        }
        if let ClaimGoalEvidence::Proposition(completion) = &evidence {
            if completion
                .outcome()
                .is_some_and(|core| !core.identity.same_as(outcome))
            {
                return Err(ClaimGoalError::WrongOutcome);
            }
            if (proposition_claim && completion.claim() != goal.target.as_ref())
                || completion
                    .claim()
                    .is_some_and(|target| goal.target.as_ref() != Some(target))
            {
                return Err(ClaimGoalError::WrongClaim);
            }
        }
        let mut closed = goal.clone();
        closed.state = ClaimGoalState::Closed(evidence);
        Ok(Self {
            claims: self.claims.with_inserted(key.clone(), closed),
            open: self.open.without_key(&goal.position),
        })
    }
}

/// What one open proof branch currently has to establish.
///
/// `P` and `O` are untrusted presentation attachments. Variant identity and
/// every semantic payload remain kernel-owned.
#[derive(Clone)]
pub(crate) enum ProofObligation<P, O> {
    Proposition(PropositionObligation<P, O>),
    Frontier(FrontierObligation),
    FunctionOutcome(FunctionOutcomeObligation<O>),
}

#[cfg(test)]
mod outcome_claim_goal_tests {
    use super::*;
    use crate::kernel::FunctionContractClaimTarget as Target;
    use crate::kernel::{ExecutionFacts, ResourceContext, api::int32};

    fn outcome() -> OutcomeProofCore {
        OutcomeProofCore {
            identity: OutcomeIdentity::fresh(),
            result: Arc::new(int32(0)),
            state: ExecutionState::new().into(),
            store_consequences_available: false,
            is_exceptional: false,
            effect_facts: ExecutionFacts::new().into(),
        }
    }

    fn completion(outcome: &OutcomeProofCore, claim: Option<Target>) -> ClaimGoalEvidence {
        ClaimGoalEvidence::Proposition(CheckedProposition::new(
            Proposition::Predicate {
                name: "done".into(),
                arguments: Vec::new(),
            },
            super::super::ProofFacts::default(),
            Some(outcome.clone()),
            claim,
        ))
    }

    fn receipt() -> ClaimGoalEvidence {
        ClaimGoalEvidence::Resource(ClaimResourceReceipt {
            returned_resources: ResourceContext::new(),
            contributes_returned_resources: true,
            defers_resource_transition: false,
        })
    }

    fn goals(is_exceptional: bool) -> OutcomeClaimGoals {
        OutcomeClaimGoals::open(
            [
                (
                    FunctionContractClaimKey::Ensure(0),
                    Some(Target::EnsureProposition(0)),
                ),
                (
                    FunctionContractClaimKey::Ensure(1),
                    Some(Target::EnsureResource(0)),
                ),
                (
                    FunctionContractClaimKey::ExceptionalEnsure(0),
                    Some(Target::ExceptionalEnsureProposition(0)),
                ),
                (FunctionContractClaimKey::Ensure(2), None),
            ],
            is_exceptional,
        )
    }

    /// Claims open in contract order, a claim about the other kind of
    /// outcome opens closed, closing the first open claim advances the focus
    /// to the next one, and each closed claim keeps its evidence.
    #[test]
    fn claim_goals_open_in_contract_order_and_keep_their_evidence() {
        let outcome = outcome();
        let returning = goals(false);
        assert_eq!(
            returning.first_open(),
            Some(&FunctionContractClaimKey::Ensure(0))
        );
        let returning = returning
            .close(
                &FunctionContractClaimKey::Ensure(0),
                completion(&outcome, Some(Target::EnsureProposition(0))),
                &outcome.identity,
            )
            .unwrap();
        assert_eq!(
            returning.first_open(),
            Some(&FunctionContractClaimKey::Ensure(1))
        );
        let returning = returning
            .close(
                &FunctionContractClaimKey::Ensure(1),
                receipt(),
                &outcome.identity,
            )
            .and_then(|goals| {
                goals.close(
                    &FunctionContractClaimKey::Ensure(2),
                    completion(&outcome, None),
                    &outcome.identity,
                )
            })
            .unwrap();
        assert_eq!(returning.first_open(), None);
        assert!(matches!(
            returning.evidence(&FunctionContractClaimKey::Ensure(0)),
            Some(ClaimGoalEvidence::Proposition(_))
        ));
        assert!(matches!(
            returning.evidence(&FunctionContractClaimKey::Ensure(1)),
            Some(ClaimGoalEvidence::Resource(_))
        ));
        assert!(
            returning
                .evidence(&FunctionContractClaimKey::ExceptionalEnsure(0))
                .is_none()
        );

        let throwing = goals(true);
        assert_eq!(
            throwing.first_open(),
            Some(&FunctionContractClaimKey::ExceptionalEnsure(0))
        );
    }

    /// A completion closes only the claim it was proved for, on the outcome
    /// it was proved about, and a claim closes once.
    #[test]
    fn a_claim_goal_refuses_the_wrong_completion() {
        let outcome = outcome();
        let sibling = self::outcome();
        let goals = goals(false);
        let key = FunctionContractClaimKey::Ensure(0);
        let refusal = |key: &FunctionContractClaimKey, evidence| {
            goals
                .close(key, evidence, &outcome.identity)
                .err()
                .expect("the close is refused")
        };
        assert_eq!(
            refusal(
                &key,
                completion(&outcome, Some(Target::EnsureProposition(1)))
            ),
            ClaimGoalError::WrongClaim
        );
        assert_eq!(
            refusal(
                &key,
                completion(&sibling, Some(Target::EnsureProposition(0)))
            ),
            ClaimGoalError::WrongOutcome
        );
        assert_eq!(
            refusal(
                &FunctionContractClaimKey::Ensure(2),
                completion(&outcome, Some(Target::EnsureProposition(0)))
            ),
            ClaimGoalError::WrongClaim
        );
        assert_eq!(
            refusal(&FunctionContractClaimKey::ExceptionalEnsure(0), receipt()),
            ClaimGoalError::AlreadyClosed
        );
        assert_eq!(
            refusal(&FunctionContractClaimKey::Ensure(9), receipt()),
            ClaimGoalError::Unknown
        );
        assert_eq!(
            refusal(&key, completion(&outcome, None)),
            ClaimGoalError::WrongClaim
        );
        assert_eq!(refusal(&key, receipt()), ClaimGoalError::WrongClaim);
        let closed = goals
            .close(
                &key,
                completion(&outcome, Some(Target::EnsureProposition(0))),
                &outcome.identity,
            )
            .unwrap();
        assert_eq!(
            closed
                .close(&key, receipt(), &outcome.identity)
                .err()
                .expect("a closed claim does not close again"),
            ClaimGoalError::AlreadyClosed
        );
    }
    fn closing_execution() -> crate::kernel::CheckedFunctionExecution {
        use crate::kernel::*;
        prove_checked_program_function_execution_with_environment(
            ExecutionState::new(),
            program_function(
                ProgramType::Int32,
                "closing_goals",
                vec![],
                program_return(crate::kernel::program_expression::int32_literal(0)),
            ),
            vec![],
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        )
    }

    fn outcome_root(
        goal: FunctionOutcomeObligation<Arc<OutcomeProofState<()>>>,
    ) -> super::super::ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> {
        super::super::ProofObject::root(
            (),
            super::super::ProofBranch::new(
                ProofObligation::FunctionOutcome(goal),
                super::super::ProofBranchState {
                    facts: super::super::ProofFacts::from_ordered(&[]),
                    unfolded_predicates: super::super::PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        )
    }

    #[test]
    fn outcome_completion_requires_opened_claims_and_all_closing_goals() {
        let execution = closing_execution();
        let core = outcome();
        let data = Arc::new(OutcomeProofState::new(core.clone(), ()));
        let mut goal = FunctionOutcomeObligation::new(0, data);
        assert!(
            outcome_root(goal.clone())
                .complete_function_outcome()
                .is_err()
        );
        goal.claims = Some(OutcomeClaimGoals::open([], false));
        let context = crate::kernel::ContractClosingContext::new(&execution);
        let closing = context.open(0, &core);
        goal.closing = Some(closing.clone());
        assert_eq!(
            goal.first_open_goal(),
            Ok(Some(OutcomeGoal::Closing(
                ContractClosingGoal::ReturnedResources
            )))
        );
        let original = outcome_root(goal.clone());
        assert!(!original.is_complete());
        assert!(
            original
                .complete_function_outcome()
                .err()
                .unwrap()
                .contains("joint returned resources")
        );
        let (transitioned, _) = closing
            .apply_resource_transition(
                &crate::kernel::ExecutionState::new(),
                crate::kernel::FunctionOutcome::Return {
                    value: crate::kernel::api::int32(0).into(),
                    state: Box::new(crate::kernel::ExecutionState::new()),
                },
                &crate::kernel::PureFactContext::new(),
            )
            .unwrap();
        assert_eq!(
            transitioned.first_open_goal(),
            Some(ContractClosingGoal::ReturnedResources)
        );
        let path = &execution.paths()[0];
        let specification =
            crate::kernel::CheckedPathSpecification::new(execution.function(), path).unwrap();
        let transitioned = transitioned
            .prove_goal(
                ContractClosingGoal::ReturnedResources,
                &execution,
                path,
                &specification,
                &core,
                goal.claims.as_ref().unwrap(),
                &super::super::ProofFacts::from_ordered(&[]),
            )
            .unwrap();
        goal.closing = Some(transitioned.clone());
        assert_eq!(
            goal.first_open_goal(),
            Ok(Some(OutcomeGoal::Closing(
                ContractClosingGoal::AllocationLifetime
            )))
        );
        assert!(
            outcome_root(goal.clone())
                .complete_function_outcome()
                .is_err()
        );
        let path = &execution.paths()[0];
        let specification =
            crate::kernel::CheckedPathSpecification::new(execution.function(), path).unwrap();
        let mut closed = transitioned;
        while let Some(kind) = closed.first_open_goal() {
            closed = closed
                .prove_goal(
                    kind,
                    &execution,
                    path,
                    &specification,
                    &core,
                    goal.claims.as_ref().unwrap(),
                    &super::super::ProofFacts::from_ordered(&[]),
                )
                .unwrap();
        }
        assert!(closed.completion(path).unwrap().matches_path(path));
        goal.closing = Some(closed.clone());
        assert_eq!(goal.first_open_goal(), Ok(None));
        let completed = outcome_root(goal.clone())
            .complete_function_outcome()
            .unwrap();
        assert!(completed.is_complete());
        assert!(completed.completion().is_some());
        assert!(
            original.complete_function_outcome().is_err(),
            "completion cannot leak to a sibling"
        );
        goal.closing = Some(closed.after_resource_change());
        assert_eq!(
            goal.first_open_goal(),
            Ok(Some(OutcomeGoal::Closing(
                ContractClosingGoal::ReturnedResources
            )))
        );
        assert!(
            outcome_root(goal.clone())
                .complete_function_outcome()
                .is_err()
        );
        for missing in ContractClosingGoal::ORDER {
            let mut partial = context.open(0, &core);
            for kind in ContractClosingGoal::ORDER {
                if kind != missing {
                    partial = partial.fixture_close_goal(kind);
                }
            }
            goal.closing = Some(partial);
            let error = outcome_root(goal.clone())
                .complete_function_outcome()
                .err()
                .unwrap();
            assert!(error.contains(missing.description()), "{error}");
        }
    }

    #[test]
    fn closing_goal_identity_survives_out_of_order_closure_and_forks() {
        let initial = ContractClosingGoals::open();
        let last_closed = initial.close(ContractClosingGoal::WriteFootprint);
        assert_eq!(
            initial.first_open(),
            Some(ContractClosingGoal::ReturnedResources)
        );
        assert_eq!(
            last_closed.first_open(),
            Some(ContractClosingGoal::ReturnedResources)
        );
        let resources_closed = last_closed.close(ContractClosingGoal::ReturnedResources);
        assert_eq!(
            resources_closed.first_open(),
            Some(ContractClosingGoal::AllocationLifetime)
        );
        let complete = resources_closed.close(ContractClosingGoal::AllocationLifetime);
        assert_eq!(complete.first_open(), None);
        assert_eq!(
            last_closed.first_open(),
            Some(ContractClosingGoal::ReturnedResources)
        );
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/obligations/outcome_claim_goals.rs");
    }
}
