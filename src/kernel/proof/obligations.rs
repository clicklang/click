//! Surface-independent proof obligations and checked capabilities.
//!
//! These values describe what a checked proof branch still owes. They carry
//! no Surface Click syntax, source selector, diagnostic data, or smart-plan
//! state.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use super::storage::SharedValue;
use crate::kernel::{
    CFunctionContractClaimKey, CFunctionContractClaimTarget, CResourceFact, CState, CValue,
    Proposition,
};

/// Diagnostic evidence returned when an allocation-lifetime obligation could
/// not be discharged. The allocation is semantic evidence; the optional
/// holder is diagnostic provenance identifying the declared resource that
/// still accounts for it. This is deliberately distinct from the open proof
/// obligation below: a successful check has no leaked-allocation payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LiveAllocationObligation {
    allocation: CResourceFact,
    holder: Option<CResourceFact>,
}

impl LiveAllocationObligation {
    pub(crate) fn new(allocation: CResourceFact, holder: Option<CResourceFact>) -> Self {
        Self { allocation, holder }
    }

    pub(crate) fn allocation(&self) -> &CResourceFact {
        &self.allocation
    }

    pub(crate) fn holder(&self) -> Option<&CResourceFact> {
        self.holder.as_ref()
    }
}

/// The outcome-owned obligation to account for every live heap allocation at
/// function exit. Its path identity prevents a result-aware claim from
/// accidentally discharging the lifetime check for a sibling outcome.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AllocationLifetimeObligation {
    path_index: usize,
}

impl AllocationLifetimeObligation {
    pub(crate) fn new(path_index: usize) -> Self {
        Self { path_index }
    }

    pub(crate) fn path_index(&self) -> usize {
        self.path_index
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
    claim: Option<crate::kernel::CFunctionContractClaimTarget>,
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
    pub(crate) fn for_claim_goal(
        goal: &crate::kernel::CClaimGoal,
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

    pub(crate) fn claim(&self) -> Option<&crate::kernel::CFunctionContractClaimTarget> {
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
    pub(crate) result: Arc<CValue>,
    pub(crate) store_consequences_available: bool,
    pub(crate) state: SharedValue<CState>,
    pub(crate) is_exceptional: bool,
    pub(crate) effect_facts: Arc<crate::kernel::ExecutionFacts>,
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
    claim: Option<crate::kernel::CFunctionContractClaimTarget>,
}

impl CheckedProposition {
    pub(super) fn new(
        proposition: Proposition,
        root_assumptions: super::ProofFacts,
        outcome: Option<OutcomeProofCore>,
        claim: Option<crate::kernel::CFunctionContractClaimTarget>,
    ) -> Self {
        Self {
            proposition: Arc::new(proposition),
            root_assumptions,
            outcome,
            claim,
        }
    }

    /// The contract claim whose kernel-issued goal this proof closed.
    pub(crate) fn claim(&self) -> Option<&crate::kernel::CFunctionContractClaimTarget> {
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

/// The remaining obligation for one checked returning path, paired with
/// opaque result-presentation data.
#[derive(Clone)]
pub(crate) struct FunctionOutcomeObligation<S> {
    pub(crate) path_index: usize,
    pub(crate) data: S,
    pub(crate) allocation_lifetime: AllocationLifetimeObligation,
    /// The contract claims this path owes, once opened at function exit.
    pub(crate) claims: Option<OutcomeClaimGoals>,
}

impl<S> FunctionOutcomeObligation<S> {
    pub(crate) fn new(path_index: usize, data: S) -> Self {
        Self {
            path_index,
            data,
            allocation_lifetime: AllocationLifetimeObligation::new(path_index),
            claims: None,
        }
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

/// The contract claims one outcome path owes, in the order the contract
/// writes them, each open or closed. A closer acts on the first open claim;
/// the path is finished when every claim is closed.
///
/// A claim about the other kind of outcome (an `ensures` on a throwing path,
/// an exceptional `ensures` on a returning one) holds vacuously and opens
/// closed.
#[derive(Clone, Debug)]
pub(crate) struct OutcomeClaimGoals {
    claims: Arc<[OutcomeClaimGoal]>,
}

#[derive(Clone, Debug)]
struct OutcomeClaimGoal {
    key: CFunctionContractClaimKey,
    /// The kernel claim the goal stands for. A clause the kernel files no
    /// claim for (a `consumes` transition) has none.
    target: Option<CFunctionContractClaimTarget>,
    closed: bool,
}

impl OutcomeClaimGoals {
    pub(crate) fn open(
        claims: impl IntoIterator<
            Item = (
                CFunctionContractClaimKey,
                Option<CFunctionContractClaimTarget>,
            ),
        >,
        is_exceptional: bool,
    ) -> Self {
        Self {
            claims: claims
                .into_iter()
                .map(|(key, target)| OutcomeClaimGoal {
                    closed: matches!(
                        (&key, is_exceptional),
                        (CFunctionContractClaimKey::Ensure(_), true)
                            | (CFunctionContractClaimKey::ExceptionalEnsure(_), false)
                    ),
                    key,
                    target,
                })
                .collect(),
        }
    }

    /// The claim a closer acts on: the first open one.
    pub(crate) fn first_open(&self) -> Option<&CFunctionContractClaimKey> {
        self.claims
            .iter()
            .find_map(|goal| (!goal.closed).then_some(&goal.key))
    }

    /// Closes `key`. A checked completion offered as its evidence must have
    /// been proved about `outcome` and, when it names a claim, must name this
    /// one.
    pub(crate) fn close(
        &self,
        key: &CFunctionContractClaimKey,
        completion: Option<&CheckedProposition>,
        outcome: &OutcomeIdentity,
    ) -> Result<Self, ClaimGoalError> {
        let position = self
            .claims
            .iter()
            .position(|goal| goal.key == *key)
            .ok_or(ClaimGoalError::Unknown)?;
        let goal = &self.claims[position];
        if goal.closed {
            return Err(ClaimGoalError::AlreadyClosed);
        }
        if let Some(completion) = completion {
            if completion
                .outcome()
                .is_some_and(|core| !core.identity.same_as(outcome))
            {
                return Err(ClaimGoalError::WrongOutcome);
            }
            if completion
                .claim()
                .is_some_and(|target| goal.target.as_ref() != Some(target))
            {
                return Err(ClaimGoalError::WrongClaim);
            }
        }
        let mut claims = self.claims.to_vec();
        claims[position].closed = true;
        Ok(Self {
            claims: claims.into(),
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
    use crate::kernel::CFunctionContractClaimTarget as Target;
    use crate::kernel::{ExecutionFacts, api::int32};

    fn outcome() -> OutcomeProofCore {
        OutcomeProofCore {
            identity: OutcomeIdentity::fresh(),
            result: Arc::new(int32(0)),
            state: CState::new().into(),
            store_consequences_available: false,
            is_exceptional: false,
            effect_facts: Arc::new(ExecutionFacts::new()),
        }
    }

    fn completion(outcome: &OutcomeProofCore, claim: Option<Target>) -> CheckedProposition {
        CheckedProposition::new(
            Proposition::Predicate {
                name: "done".into(),
                arguments: Vec::new(),
            },
            super::super::ProofFacts::default(),
            Some(outcome.clone()),
            claim,
        )
    }

    fn goals(is_exceptional: bool) -> OutcomeClaimGoals {
        OutcomeClaimGoals::open(
            [
                (
                    CFunctionContractClaimKey::Ensure(0),
                    Some(Target::EnsureProposition(0)),
                ),
                (
                    CFunctionContractClaimKey::Ensure(1),
                    Some(Target::EnsureResource(0)),
                ),
                (
                    CFunctionContractClaimKey::ExceptionalEnsure(0),
                    Some(Target::ExceptionalEnsureProposition(0)),
                ),
                (CFunctionContractClaimKey::Ensure(2), None),
            ],
            is_exceptional,
        )
    }

    /// Claims open in contract order, a claim about the other kind of
    /// outcome opens closed, and closing the first open claim advances the
    /// focus to the next one.
    #[test]
    fn claim_goals_open_in_contract_order_and_advance_as_they_close() {
        let outcome = outcome();
        let returning = goals(false);
        assert_eq!(
            returning.first_open(),
            Some(&CFunctionContractClaimKey::Ensure(0))
        );
        let returning = returning
            .close(
                &CFunctionContractClaimKey::Ensure(0),
                Some(&completion(&outcome, Some(Target::EnsureProposition(0)))),
                &outcome.identity,
            )
            .unwrap();
        assert_eq!(
            returning.first_open(),
            Some(&CFunctionContractClaimKey::Ensure(1))
        );
        let returning = returning
            .close(
                &CFunctionContractClaimKey::Ensure(1),
                None,
                &outcome.identity,
            )
            .and_then(|goals| {
                goals.close(
                    &CFunctionContractClaimKey::Ensure(2),
                    None,
                    &outcome.identity,
                )
            })
            .unwrap();
        assert_eq!(returning.first_open(), None);

        let throwing = goals(true);
        assert_eq!(
            throwing.first_open(),
            Some(&CFunctionContractClaimKey::ExceptionalEnsure(0))
        );
    }

    /// A completion closes only the claim it was proved for, on the outcome
    /// it was proved about, and a claim closes once.
    #[test]
    fn a_claim_goal_refuses_the_wrong_completion() {
        let outcome = outcome();
        let sibling = self::outcome();
        let goals = goals(false);
        let key = CFunctionContractClaimKey::Ensure(0);
        assert_eq!(
            goals
                .close(
                    &key,
                    Some(&completion(&outcome, Some(Target::EnsureProposition(1)))),
                    &outcome.identity,
                )
                .unwrap_err(),
            ClaimGoalError::WrongClaim
        );
        assert_eq!(
            goals
                .close(
                    &key,
                    Some(&completion(&sibling, Some(Target::EnsureProposition(0)))),
                    &outcome.identity,
                )
                .unwrap_err(),
            ClaimGoalError::WrongOutcome
        );
        assert_eq!(
            goals
                .close(
                    &CFunctionContractClaimKey::Ensure(2),
                    Some(&completion(&outcome, Some(Target::EnsureProposition(0)))),
                    &outcome.identity,
                )
                .unwrap_err(),
            ClaimGoalError::WrongClaim
        );
        assert_eq!(
            goals
                .close(
                    &CFunctionContractClaimKey::ExceptionalEnsure(0),
                    None,
                    &outcome.identity,
                )
                .unwrap_err(),
            ClaimGoalError::AlreadyClosed
        );
        assert_eq!(
            goals
                .close(
                    &CFunctionContractClaimKey::Ensure(9),
                    None,
                    &outcome.identity
                )
                .unwrap_err(),
            ClaimGoalError::Unknown
        );
        let closed = goals.close(&key, None, &outcome.identity).unwrap();
        assert_eq!(
            closed.close(&key, None, &outcome.identity).unwrap_err(),
            ClaimGoalError::AlreadyClosed
        );
    }
}
