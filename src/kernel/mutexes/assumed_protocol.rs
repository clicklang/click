//! Opaque mutex protocols supplied by an independent contract input.
//!
//! This boundary deliberately exposes no protected assertion. It permits a
//! checked local acquisition and release while retaining the caller's lifetime
//! obligation. Runtime dispatch and contract effects must be wired separately.

use super::*;
use crate::kernel::loans::{
    CheckedLoanCallEvidence, CheckedLoanCallEvidenceSequence, CheckedLoanTransition, LoanRefusal,
    append_checked_loan_evidence, empty_checked_loan_evidence_sequence,
};

/// A description backed by one actual, rooted use input, not by its address.
/// It supplies neither lifecycle ownership nor protected memory ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AssumedMutexProtocol {
    usage: MutexUseBinding,
    holder: LoanParticipantId,
    use_fact: CResourceFact,
    lifetime: CResourceFact,
}

/// An exact acquisition receipt. The guard atom and its loan hold must also
/// remain in the state; copying this receipt never copies ownership.
pub(super) struct AssumedMutexGuard {
    protocol: AssumedMutexProtocol,
    fact: CResourceFact,
    hold: LoanHoldId,
}

pub(super) struct AssumedMutexTransition {
    pub(super) state: CState,
    pub(super) evidence: CheckedLoanCallEvidenceSequence,
}

impl AssumedMutexProtocol {
    pub(super) fn bind(
        state: &CState,
        usage: MutexUseBinding,
    ) -> Result<Self, MutexTransitionError> {
        if !state.preserves_mutex_protocols || state.mutex_ledger.is_some() {
            return Err("abstract mutex protocols require independent contract input state".into());
        }
        let holder = state
            .loan_participant
            .ok_or("missing mutex use participant")?;
        let loans = state.loan_ledger.as_ref().ok_or("missing mutex use loan")?;
        let use_fact = loans
            .mutex_use_resource(usage, holder)
            .map_err(|_| MutexTransitionError::Refusal("missing rooted mutex use input"))?;
        let CResource::MutexUse(identity) = use_fact.resource() else {
            unreachable!()
        };
        loans
            .check_assumed_mutex_use_return(usage, holder, &state.resources)
            .map_err(|_| MutexTransitionError::MissingUse(identity.mutex.clone()))?;
        let initialization = identity
            .initialization
            .ok_or_else(|| MutexTransitionError::MissingUse(identity.mutex.clone()))?;
        let lifetime = CResourceFact::own(CResource::MutexLive(super::super::MutexIdentity {
            epoch: Some(initialization),
            mutex: identity.mutex.clone(),
        }));
        Ok(Self {
            usage,
            holder,
            use_fact,
            lifetime,
        })
    }

    fn mutex(&self) -> &Pointer {
        let CResource::MutexUse(identity) = self.use_fact.resource() else {
            unreachable!()
        };
        &identity.mutex
    }

    fn loans<'a>(&self, state: &'a CState) -> Result<&'a LoanLedger, MutexTransitionError> {
        let missing = || MutexTransitionError::MissingUse(self.mutex().clone());
        if !state.preserves_mutex_protocols
            || state.mutex_ledger.is_some()
            || state.loan_participant != Some(self.holder)
            || state
                .resources
                .unique_owned_occurrence_for_fact(&self.use_fact)
                .is_none()
        {
            return Err(missing());
        }
        let ledger = state.loan_ledger.as_ref().ok_or_else(missing)?;
        if ledger
            .mutex_use_resource(self.usage, self.holder)
            .map_err(|_| missing())?
            != self.use_fact
        {
            return Err(missing());
        }
        Ok(ledger)
    }

    pub(super) fn acquire(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
    ) -> Result<(AssumedMutexTransition, AssumedMutexGuard), MutexTransitionError> {
        let loans = self.loans(state)?;
        // A hidden or removed guard still pins the scope. Do not decide local
        // heldness by merely searching the visible resource context.
        loans
            .check_assumed_mutex_use_return(self.usage, self.holder, &state.resources)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "mutex_use has an outstanding mutex_guard or reborrow",
                )
            })?;
        if state.resources.mutex_guard_at(self.mutex()).is_some() {
            return Err("mutex is already guarded".into());
        }
        let (next, hold, transition) = loans
            .hold_mutex_use_with_transition(self.usage, &self.lifetime, self.holder)
            .map_err(|_| MutexTransitionError::MissingUse(self.mutex().clone()))?;
        let fact = CResourceFact::own(CResource::MutexGuard(super::super::MutexIdentity {
            epoch: Some(fresh_acquisition_epoch()?),
            mutex: self.mutex().clone(),
        }));
        let resources = state
            .resources
            .clone()
            .try_compose_with_facts_delaying_normalization([fact.clone()], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal("mutex guard conflicts with current authority")
            })?;
        let evidence = self.evidence(loans, transition, &next)?;
        let mut state = state.clone();
        state.resources = resources;
        state.loan_ledger = Some(next);
        Ok((
            AssumedMutexTransition { state, evidence },
            AssumedMutexGuard {
                protocol: self.clone(),
                fact,
                hold,
            },
        ))
    }

    pub(super) fn release(
        &self,
        state: &CState,
        guard: &AssumedMutexGuard,
        assumptions: &PureFactContext,
    ) -> Result<AssumedMutexTransition, MutexTransitionError> {
        if guard.protocol != *self {
            return Err(MutexTransitionError::MissingGuard(self.mutex().clone()));
        }
        let loans = self.loans(state)?;
        if state
            .resources
            .unique_owned_occurrence_for_fact(&guard.fact)
            .is_none()
        {
            return Err(MutexTransitionError::MissingGuard(self.mutex().clone()));
        }
        let (next, transition) = loans
            .release_mutex_use_hold_with_transition(
                self.usage,
                &self.lifetime,
                guard.hold,
                self.holder,
            )
            .map_err(|_| MutexTransitionError::MissingGuard(self.mutex().clone()))?;
        let resources = state
            .resources
            .clone()
            .without_fact_delaying_normalization(&guard.fact, assumptions)
            .ok_or_else(|| MutexTransitionError::MissingGuard(self.mutex().clone()))?;
        let evidence = self.evidence(loans, transition, &next)?;
        let mut state = state.clone();
        state.resources = resources;
        state.loan_ledger = Some(next);
        Ok(AssumedMutexTransition { state, evidence })
    }

    pub(super) fn check_return(&self, state: &CState) -> Result<(), MutexTransitionError> {
        self.loans(state)?
            .check_assumed_mutex_use_return(self.usage, self.holder, &state.resources)
            .map_err(|_| MutexTransitionError::MissingUse(self.mutex().clone()))
    }

    fn evidence(
        &self,
        before: &LoanLedger,
        transition: CheckedLoanTransition,
        after: &LoanLedger,
    ) -> Result<CheckedLoanCallEvidenceSequence, MutexTransitionError> {
        let evidence = CheckedLoanCallEvidence::runtime_mutex_transition(
            before,
            self.holder,
            transition,
            after,
        )
        .map_err(|_: LoanRefusal| {
            MutexTransitionError::Refusal("invalid mutex lifetime transition")
        })?;
        Ok(append_checked_loan_evidence(
            &empty_checked_loan_evidence_sequence(),
            Some(Arc::new(evidence)),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MutexUseIdentity, ResourceContext, Variable};

    fn input() -> (CState, AssumedMutexProtocol) {
        let mutex = Pointer::symbolic(Variable(765));
        let description = CResourceFact::own(CResource::MutexUse(MutexUseIdentity {
            binding: None,
            initialization: None,
            mutex: mutex.clone(),
        }));
        let resources = ResourceContext::new().unchecked_with_fact(description.clone());
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(&description)
            .unwrap();
        let ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let (ledger, root) = ledger
            .borrowed_mutex_use_input(holder, support, mutex)
            .unwrap();
        let fact = ledger.mutex_use_resource(root.usage, holder).unwrap();
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        state.loan_ledger = Some(ledger);
        state.loan_participant = Some(holder);
        state.resources = ResourceContext::new().unchecked_with_fact(fact);
        let protocol = AssumedMutexProtocol::bind(&state, root.usage).unwrap();
        (state, protocol)
    }

    #[test]
    fn abstract_protocol_requires_actual_rooted_input_and_grants_no_payload_or_owner() {
        let (state, protocol) = input();
        assert_eq!(state.resources.facts().len(), 1);
        assert!(state.mutex_ledger.is_none());
        assert!(
            !state
                .resources
                .satisfies_fact(&protocol.lifetime, &PureFactContext::new())
        );
        let mut missing = state.clone();
        missing.resources = ResourceContext::new();
        assert!(AssumedMutexProtocol::bind(&missing, protocol.usage).is_err());
        assert!(protocol.acquire(&missing, &PureFactContext::new()).is_err());
        let mut concrete = state.clone();
        concrete.preserves_mutex_protocols = false;
        assert!(AssumedMutexProtocol::bind(&concrete, protocol.usage).is_err());
        let mut wrong = state.clone();
        wrong.loan_participant = Some(
            state
                .loan_ledger
                .as_ref()
                .unwrap()
                .fresh_participant()
                .unwrap(),
        );
        assert!(protocol.acquire(&wrong, &PureFactContext::new()).is_err());
        let (_, other) = input();
        assert!(other.acquire(&state, &PureFactContext::new()).is_err());
        // The ordinary C runtime entry remains frozen.
        assert!(
            MutexContext::new(state)
                .acquire_current(protocol.mutex(), &PureFactContext::new())
                .is_err()
        );
    }

    #[test]
    fn abstract_acquire_release_preserves_opaque_payload_and_retains_checked_evidence() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let (held, guard) = protocol.acquire(&state, &assumptions).unwrap();
        assert_eq!(held.state.memory, state.memory);
        assert!(held.state.mutex_ledger.is_none());
        assert_eq!(held.state.resources.facts().len(), 2);
        assert!(
            held.state
                .resources
                .satisfies_fact(&guard.fact, &assumptions)
        );
        assert!(
            held.state
                .resources
                .satisfies_fact(&protocol.use_fact, &assumptions)
        );
        assert!(
            !held
                .state
                .resources
                .satisfies_fact(&protocol.lifetime, &assumptions)
        );
        assert!(protocol.check_return(&held.state).is_err());
        assert!(protocol.acquire(&held.state, &assumptions).is_err());
        let released = protocol.release(&held.state, &guard, &assumptions).unwrap();
        assert_eq!(released.state.memory, state.memory);
        assert!(protocol.check_return(&released.state).is_ok());
        assert_eq!(released.state.resources.facts(), state.resources.facts());
        let evidence =
            crate::kernel::loans::concat_checked_loan_evidence(&held.evidence, &released.evidence);
        assert_eq!(evidence.len(), 2);
        assert!(evidence.is_valid());
        assert_eq!(
            evidence.recovered_ledger_for(
                state.loan_ledger.as_ref().unwrap(),
                protocol.holder,
                false
            ),
            released.state.loan_ledger
        );
        let (again, next_guard) = protocol.acquire(&released.state, &assumptions).unwrap();
        assert_ne!(guard.fact, next_guard.fact);
        assert!(
            protocol
                .release(&again.state, &guard, &assumptions)
                .is_err()
        );
        assert!(
            protocol
                .release(&again.state, &next_guard, &assumptions)
                .is_ok()
        );
    }

    #[test]
    fn hidden_guard_and_wrong_receipts_cannot_end_the_lifetime_hold() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let (held, mut guard) = protocol.acquire(&state, &assumptions).unwrap();
        let mut hidden = held.state.clone();
        hidden.resources = hidden
            .resources
            .without_fact(&guard.fact, &assumptions)
            .unwrap();
        assert!(protocol.acquire(&hidden, &assumptions).is_err());
        assert!(protocol.release(&hidden, &guard, &assumptions).is_err());
        assert!(protocol.check_return(&hidden).is_err());
        let (other_state, other) = input();
        let (_, other_guard) = other.acquire(&other_state, &assumptions).unwrap();
        assert!(
            protocol
                .release(&held.state, &other_guard, &assumptions)
                .is_err()
        );
        // Even a hostile receipt retaining the correct guard atom cannot
        // substitute another loan's hold and release its lifetime early.
        guard.hold = other_guard.hold;
        assert!(protocol.release(&held.state, &guard, &assumptions).is_err());
    }

    #[test]
    fn release_cannot_substitute_a_different_scope_hold_in_the_same_ledger() {
        let assumptions = PureFactContext::new();
        let (mut state, first) = input();
        let marker = CResourceFact::own(CResource::Token {
            name: "second input".into(),
            arguments: vec![].into(),
        });
        let resources = ResourceContext::new().unchecked_with_fact(marker.clone());
        let (support, _) = resources.unique_owned_occurrence_for_fact(&marker).unwrap();
        let (ledger, root) = state
            .loan_ledger
            .as_ref()
            .unwrap()
            .borrowed_mutex_use_input(first.holder, support, Pointer::symbolic(Variable(766)))
            .unwrap();
        let second_fact = ledger.mutex_use_resource(root.usage, first.holder).unwrap();
        state.resources = state.resources.unchecked_with_fact(second_fact);
        state.loan_ledger = Some(ledger);
        let second = AssumedMutexProtocol::bind(&state, root.usage).unwrap();
        let (held_first, mut first_guard) = first.acquire(&state, &assumptions).unwrap();
        let (held_both, second_guard) = second.acquire(&held_first.state, &assumptions).unwrap();
        let correct_hold = first_guard.hold;
        first_guard.hold = second_guard.hold;
        assert!(
            first
                .release(&held_both.state, &first_guard, &assumptions)
                .is_err()
        );
        assert!(second.check_return(&held_both.state).is_err());
        first_guard.hold = correct_hold;
        let released_first = first
            .release(&held_both.state, &first_guard, &assumptions)
            .unwrap();
        let released_both = second
            .release(&released_first.state, &second_guard, &assumptions)
            .unwrap();
        first.check_return(&released_both.state).unwrap();
        second.check_return(&released_both.state).unwrap();
    }

    #[test]
    fn abstract_protocol_transitions_ignore_unrelated_resource_frames() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let (mut state, protocol) = input();
            for index in 0..size {
                state.resources =
                    state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (held, guard) = protocol.acquire(&state, &assumptions).unwrap();
                    let released = protocol.release(&held.state, &guard, &assumptions).unwrap();
                    protocol.check_return(&released.state).unwrap();
                    released
                })
            });
            assert_eq!(returned.state.resources.facts().len(), size + 1);
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "abstract protocol scans unrelated resources: {samples:?}"
            );
        }
    }
}
