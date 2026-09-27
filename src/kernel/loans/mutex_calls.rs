//! Checked resource partition and restoration for one synchronous mutex-use
//! requirement. The contract planner selects the source occurrence. This
//! component never assumes missing authority and does not certify a C body.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MutexUseCallError {
    MissingResource(CResourceFact),
    Unavailable(&'static str),
    Loan(LoanRefusal),
    InvalidResources(crate::kernel::ResourceContextValidityError),
}

impl From<LoanRefusal> for MutexUseCallError {
    fn from(error: LoanRefusal) -> Self {
        Self::Loan(error)
    }
}

/// Retains the source, participants, and checked entry evidence, so return
/// cannot choose a different owner or parent with the same printed address.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseCallTransfer {
    pub(crate) caller_resources: ResourceContext,
    pub(crate) callee_resources: ResourceContext,
    pub(crate) ledger: LoanLedger,
    pub(crate) entry_transition: CheckedLoanTransition,
    pub(crate) usage: MutexUseBinding,
    source: CResourceFact,
    interface: Option<Arc<crate::kernel::mutexes::InitializedMutexInterface>>,
    loan: MutexUseLoan,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseCallReturn {
    pub(crate) ledger: LoanLedger,
    pub(crate) caller_resources: ResourceContext,
    /// The other returned clauses remain for the surrounding contract planner
    /// to check and transfer; this component neither grants nor discards them.
    pub(crate) remaining_resources: ResourceContext,
    pub(crate) exit_transitions: Vec<CheckedLoanTransition>,
}

impl MutexUseCallTransfer {
    pub(crate) fn prepare(
        ledger: &LoanLedger,
        caller: LoanParticipantId,
        callee: LoanParticipantId,
        resources: &ResourceContext,
        source: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexUseCallError> {
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(source)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?;
        let (ledger, loan, entry_transition) = match source.resource() {
            CResource::MutexLive(_) => {
                ledger.lend_mutex_use_with_transition(caller, callee, support, source.clone())?
            }
            CResource::MutexUse(identity) => {
                ledger.check_mutex_use_available(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                    resources,
                )?;
                if ledger.mutex_use_resource(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                )? != *source
                {
                    return Err(LoanRefusal::MissingLoanBinding.into());
                }
                ledger.reborrow_mutex_use_with_transition(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                    callee,
                )?
            }
            _ => return Err(LoanRefusal::UnsupportedResource.into()),
        };
        let caller_resources = resources
            .clone()
            .without_fact_delaying_normalization(source, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?;
        let use_fact = ledger.mutex_use_resource(loan.usage, callee)?;
        let callee_resources = ResourceContext::new()
            .try_compose_with_facts_delaying_normalization([use_fact], assumptions)
            .map_err(MutexUseCallError::InvalidResources)?;
        Ok(Self {
            caller_resources,
            callee_resources,
            ledger,
            usage: loan.usage,
            source: source.clone(),
            interface: None,
            loan,
            entry_transition,
            caller,
            callee,
        })
    }

    /// Attach only metadata authenticated by the selected concrete
    /// initialization. Preparing the transfer has already checked ownership
    /// and the callee's loan; a source declaration cannot supply this binding.
    pub(in crate::kernel) fn bind_interface(
        &mut self,
        protocols: &crate::kernel::mutexes::MutexLedger,
    ) -> Result<(), MutexUseCallError> {
        let fact = self.ledger.mutex_use_resource(self.usage, self.callee)?;
        protocols
            .check_use_acquisition(&fact)
            .map_err(|error| match error {
                crate::kernel::mutexes::MutexTransitionError::Refusal(message) => {
                    MutexUseCallError::Unavailable(message)
                }
                _ => MutexUseCallError::MissingResource(self.source.clone()),
            })?;
        let interface = protocols
            .interface_for_use(&fact)
            .map_err(|_| MutexUseCallError::MissingResource(self.source.clone()))?;
        // A repeated check must not erase or replace an established binding.
        if let Some(previous) = &self.interface
            && !interface
                .as_ref()
                .is_some_and(|next| Arc::ptr_eq(previous, next))
        {
            return Err(MutexUseCallError::MissingResource(self.source.clone()));
        }
        self.interface = interface;
        Ok(())
    }

    pub(crate) fn source_resource(&self) -> &CResourceFact {
        &self.source
    }

    #[cfg(test)]
    pub(crate) fn recheck_entry(&self, predecessor: &LoanLedger) -> Result<(), LoanRefusal> {
        let checked = predecessor.apply(&self.entry_transition)?;
        if checked != self.ledger {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }

    /// The body must already be certified. Its explicit loan deltas connect
    /// this exact entry to the returned ledger; a sibling ledger is insufficient.
    /// Assumed roots belong only to modular entry, never an executing call.
    #[cfg(test)]
    pub(crate) fn finish(
        &self,
        returned_ledger: &LoanLedger,
        returned_participant: LoanParticipantId,
        returned_resources: &ResourceContext,
        body_transitions: &[CheckedLoanTransition],
        assumptions: &PureFactContext,
    ) -> Result<MutexUseCallReturn, MutexUseCallError> {
        if returned_participant != self.callee {
            return Err(LoanRefusal::WrongHolder.into());
        }
        let mut ledger = self.ledger.clone();
        for transition in body_transitions {
            if matches!(
                transition.evidence,
                LoanTransitionEvidence::BorrowedMutexUseRoot { .. }
                    | LoanTransitionEvidence::BorrowedRoot { local: None, .. }
            ) {
                return Err(LoanRefusal::InvalidEvidence.into());
            }
            crate::instrumentation::record_deterministic_work(1);
            ledger = ledger.apply(transition)?;
        }
        if ledger != *returned_ledger {
            return Err(LoanRefusal::InvalidEvidence.into());
        }
        self.finish_checked_ledger(ledger, returned_resources, assumptions)
    }

    /// Used only inside the common planner's checked entry/recovery chain.
    pub(super) fn finish_checked_ledger(
        &self,
        mut ledger: LoanLedger,
        returned_resources: &ResourceContext,
        assumptions: &PureFactContext,
    ) -> Result<MutexUseCallReturn, MutexUseCallError> {
        let expected = ledger.mutex_use_resource(self.usage, self.callee)?;
        if self
            .interface
            .as_ref()
            .is_some_and(|binding| !binding.matches_use(&expected))
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        if returned_resources
            .unique_owned_occurrence_for_fact(&expected)
            .is_none()
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        let remaining_resources = returned_resources
            .clone()
            .without_fact_delaying_normalization(&expected, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(expected.clone()))?;
        let mut exit_transitions = Vec::new();
        let transfer = ledger.transfer(self.usage.0.share, self.callee, self.caller)?;
        ledger = ledger.apply(&transfer)?;
        exit_transitions.push(transfer);
        let end = ledger.end(self.loan.scope, self.caller)?;
        ledger = ledger.apply(&end)?;
        exit_transitions.push(end);
        let restored = match self.source.resource() {
            CResource::MutexLive(_) => {
                let (recovery, owner, _) = ledger.recover(self.loan.loan, self.caller)?;
                ledger = ledger.apply(&recovery)?;
                exit_transitions.push(recovery);
                owner
            }
            CResource::MutexUse(identity) => ledger.mutex_use_resource(
                identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                self.caller,
            )?,
            _ => return Err(LoanRefusal::UnsupportedResource.into()),
        };
        if restored != self.source {
            return Err(LoanRefusal::MissingLoanBinding.into());
        }
        let caller_resources = self
            .caller_resources
            .clone()
            .try_compose_with_facts_delaying_normalization([restored], assumptions)
            .map_err(MutexUseCallError::InvalidResources)?;
        Ok(MutexUseCallReturn {
            ledger,
            caller_resources,
            remaining_resources,
            exit_transitions,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MutexIdentity, Pointer, Variable};

    fn owner() -> CResourceFact {
        CResourceFact::own(CResource::MutexLive(MutexIdentity {
            epoch: Some(91),
            mutex: Pointer::symbolic(Variable(100)),
        }))
    }

    fn token(name: &str) -> CResourceFact {
        CResourceFact::own(CResource::Token {
            name: name.into(),
            arguments: Vec::new().into(),
        })
    }

    fn plan() -> (LoanLedger, MutexUseCallTransfer) {
        let before = LoanLedger::new();
        let caller = before.fresh_participant().unwrap();
        let callee = before.fresh_participant().unwrap();
        let resources = ResourceContext::new()
            .unchecked_with_fact(owner())
            .unchecked_with_fact(token("caller frame"));
        let plan = MutexUseCallTransfer::prepare(
            &before,
            caller,
            callee,
            &resources,
            &owner(),
            &PureFactContext::new(),
        )
        .unwrap();
        (before, plan)
    }

    #[test]
    fn use_call_lends_one_occurrence_and_restores_exact_owner_and_frame() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        plan.recheck_entry(&before).unwrap();
        assert!(!plan.caller_resources.satisfies_fact(&owner(), &assumptions));
        assert!(
            plan.caller_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert_eq!(plan.callee_resources.facts().len(), 1);
        assert!(!plan.callee_resources.satisfies_fact(&owner(), &assumptions));
        assert!(
            !plan
                .callee_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert!(
            plan.ledger
                .mutex_use_resource(plan.usage, plan.caller)
                .is_err()
        );
        let returned = plan
            .callee_resources
            .clone()
            .unchecked_with_fact(token("other returned clause"));
        let result = plan
            .finish(&plan.ledger, plan.callee, &returned, &[], &assumptions)
            .unwrap();
        assert!(
            result
                .caller_resources
                .satisfies_fact(&owner(), &assumptions)
        );
        assert!(
            result
                .caller_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert_eq!(
            result.remaining_resources.facts(),
            &[token("other returned clause")]
        );
        let mut recheck = plan.ledger.clone();
        for transition in &result.exit_transitions {
            recheck = recheck.apply(transition).unwrap();
        }
        assert_eq!(recheck, result.ledger);
        assert!(result.ledger.invariant_holds());
        assert!(
            result
                .ledger
                .mutex_use_resource(plan.usage, plan.callee)
                .is_err()
        );
        assert!(
            plan.finish(&result.ledger, plan.callee, &returned, &[], &assumptions)
                .is_err()
        );
    }

    #[test]
    fn use_call_reborrows_an_assumed_input_through_nested_helpers() {
        let before = LoanLedger::new();
        let caller = before.fresh_participant().unwrap();
        let callee = before.fresh_participant().unwrap();
        let helper = before.fresh_participant().unwrap();
        let support = ResourceContext::new()
            .unchecked_with_fact(token("clause"))
            .unique_owned_occurrence_for_fact(&token("clause"))
            .unwrap()
            .0;
        let (before, input) = before
            .borrowed_mutex_use_input(caller, support, Pointer::symbolic(Variable(100)))
            .unwrap();
        let source = before.mutex_use_resource(input.usage, caller).unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(source.clone());
        let assumptions = PureFactContext::new();
        let outer = MutexUseCallTransfer::prepare(
            &before,
            caller,
            callee,
            &resources,
            &source,
            &assumptions,
        )
        .unwrap();
        let supplied = outer
            .ledger
            .mutex_use_resource(outer.usage, callee)
            .unwrap();
        let inner = MutexUseCallTransfer::prepare(
            &outer.ledger,
            callee,
            helper,
            &outer.callee_resources,
            &supplied,
            &assumptions,
        )
        .unwrap();
        assert!(
            inner
                .ledger
                .mutex_use_resource(outer.usage, callee)
                .is_err()
        );
        let inner_return = inner
            .finish(
                &inner.ledger,
                helper,
                &inner.callee_resources,
                &[],
                &assumptions,
            )
            .unwrap();
        let body: Vec<_> = std::iter::once(inner.entry_transition.clone())
            .chain(inner_return.exit_transitions)
            .collect();
        let result = outer
            .finish(
                &inner_return.ledger,
                callee,
                &inner_return.caller_resources,
                &body,
                &assumptions,
            )
            .unwrap();
        result
            .ledger
            .check_mutex_use_input_return(&input, caller, &result.caller_resources)
            .unwrap();
        assert_eq!(result.caller_resources.facts(), &[source]);
        assert!(result.remaining_resources.facts().is_empty());
        assert!(result.ledger.recover(input.usage.0.loan, caller).is_err());
        assert!(result.ledger.invariant_holds());
    }

    #[test]
    fn use_call_refuses_missing_duplicate_or_invalid_source_ownership() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        let missing = MutexUseCallTransfer::prepare(
            &before,
            plan.caller,
            plan.callee,
            &ResourceContext::new(),
            &owner(),
            &assumptions,
        )
        .unwrap_err();
        assert_eq!(missing, MutexUseCallError::MissingResource(owner()));
        let duplicate = ResourceContext::new()
            .unchecked_with_fact(owner())
            .unchecked_with_fact(owner());
        assert!(
            MutexUseCallTransfer::prepare(
                &before,
                plan.caller,
                plan.callee,
                &duplicate,
                &owner(),
                &assumptions
            )
            .is_err()
        );
        for source in [
            CResourceFact::View(owner().resource().clone()),
            CResourceFact::Own(
                owner().resource().clone(),
                Box::new(Bitvector32Term::Constant(2)),
            ),
            token("unrelated"),
        ] {
            assert!(
                MutexUseCallTransfer::prepare(
                    &before,
                    plan.caller,
                    plan.callee,
                    &ResourceContext::new().unchecked_with_fact(source.clone()),
                    &source,
                    &assumptions
                )
                .is_err()
            );
        }
        let fact = plan
            .ledger
            .mutex_use_resource(plan.usage, plan.callee)
            .unwrap();
        assert!(
            MutexUseCallTransfer::prepare(
                &plan.ledger,
                plan.caller,
                plan.callee,
                &ResourceContext::new().unchecked_with_fact(fact.clone()),
                &fact,
                &assumptions
            )
            .is_err()
        );
        let helper = plan.ledger.fresh_participant().unwrap();
        let inner = MutexUseCallTransfer::prepare(
            &plan.ledger,
            plan.callee,
            helper,
            &plan.callee_resources,
            &fact,
            &assumptions,
        )
        .unwrap();
        assert!(
            MutexUseCallTransfer::prepare(
                &inner.ledger,
                plan.callee,
                helper,
                &plan.callee_resources,
                &fact,
                &assumptions
            )
            .is_err()
        );
    }

    #[test]
    fn use_call_return_requires_exact_resource_participant_and_checked_history() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        let missing = plan
            .finish(
                &plan.ledger,
                plan.callee,
                &ResourceContext::new(),
                &[],
                &assumptions,
            )
            .unwrap_err();
        assert_eq!(
            missing,
            MutexUseCallError::MissingResource(plan.callee_resources.facts()[0].clone())
        );
        assert!(
            plan.finish(
                &plan.ledger,
                plan.caller,
                &plan.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        let duplicate = plan
            .callee_resources
            .clone()
            .unchecked_with_fact(plan.callee_resources.facts()[0].clone());
        assert!(
            plan.finish(&plan.ledger, plan.callee, &duplicate, &[], &assumptions)
                .is_err()
        );
        let alternate = MutexUseCallTransfer::prepare(
            &before,
            plan.caller,
            plan.callee,
            &ResourceContext::new().unchecked_with_fact(owner()),
            &owner(),
            &assumptions,
        )
        .unwrap();
        assert!(
            plan.finish(
                &alternate.ledger,
                plan.callee,
                &alternate.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        assert!(plan.recheck_entry(&plan.ledger).is_err());
        let (held, hold, hold_step) = plan
            .ledger
            .hold_authority_with_transition(plan.usage.0, plan.callee)
            .unwrap();
        assert!(
            plan.finish(
                &held,
                plan.callee,
                &plan.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        assert_eq!(
            plan.finish(
                &held,
                plan.callee,
                &plan.callee_resources,
                std::slice::from_ref(&hold_step),
                &assumptions
            ),
            Err(MutexUseCallError::Loan(LoanRefusal::ActiveDependency))
        );
        let (released, release_step) = held.release_with_transition(hold, plan.callee).unwrap();
        let result = plan
            .finish(
                &released,
                plan.callee,
                &plan.callee_resources,
                &[hold_step, release_step],
                &assumptions,
            )
            .unwrap();
        assert!(
            result
                .caller_resources
                .satisfies_fact(&owner(), &assumptions)
        );
        assert!(
            plan.ledger
                .mutex_use_resource(plan.usage, plan.callee)
                .is_ok(),
            "failed returns never mutate entry"
        );
    }

    #[test]
    fn use_call_rejects_proof_entry_assumptions_in_body_evidence() {
        let (_, plan) = plan();
        let data = &plan.ledger.storage.data;
        let arena = data.arena;
        let support = plan.loan.usage.0.support;
        let transition = plan
            .ledger
            .issue(LoanTransitionEvidence::BorrowedMutexUseRoot {
                holder: plan.callee,
                support,
                mutex: Pointer::symbolic(Variable(200)),
                initialization: crate::kernel::mutexes::MutexInitializationId::fresh().unwrap(),
                scope: LoanScopeId {
                    arena,
                    ordinal: data.next_scope,
                },
                loan: LoanId {
                    arena,
                    ordinal: data.next_loan,
                },
                root: LoanShareId {
                    arena,
                    ordinal: data.next_share,
                },
            })
            .unwrap();
        let illicit = plan.ledger.apply(&transition).unwrap();
        assert_eq!(
            plan.finish(
                &illicit,
                plan.callee,
                &plan.callee_resources,
                &[transition],
                &PureFactContext::new()
            ),
            Err(MutexUseCallError::Loan(LoanRefusal::InvalidEvidence))
        );
    }

    #[test]
    fn use_call_partition_and_return_ignore_unrelated_resources() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let ledger = LoanLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let mut resources = ResourceContext::new().unchecked_with_fact(owner());
            for index in 0..size {
                resources = resources.unchecked_with_fact(token(&format!("frame {index}")));
            }
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let plan = MutexUseCallTransfer::prepare(
                        &ledger,
                        caller,
                        callee,
                        &resources,
                        &owner(),
                        &PureFactContext::new(),
                    )
                    .unwrap();
                    plan.recheck_entry(&ledger).unwrap();
                    plan.finish(
                        &plan.ledger,
                        callee,
                        &plan.callee_resources,
                        &[],
                        &PureFactContext::new(),
                    )
                    .unwrap()
                })
            });
            assert_eq!(returned.caller_resources.facts().len(), size + 1);
            samples.push((size, work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
                "call boundary scans unrelated frame: {samples:?}"
            );
        }
    }
    #[test]
    fn use_call_return_recheck_scales_with_explicit_certificate_delta() {
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let (_, plan) = plan();
            let mut ledger = plan.ledger.clone();
            let mut steps = Vec::new();
            for _ in 0..size {
                let (held, hold, step) = ledger
                    .hold_authority_with_transition(plan.usage.0, plan.callee)
                    .unwrap();
                steps.push(step);
                let (released, step) = held.release_with_transition(hold, plan.callee).unwrap();
                steps.push(step);
                ledger = released;
            }
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    plan.finish(
                        &ledger,
                        plan.callee,
                        &plan.callee_resources,
                        &steps,
                        &PureFactContext::new(),
                    )
                    .unwrap()
                })
            });
            assert!(returned.ledger.invariant_holds());
            samples.push((size, work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 3 && pair[1].2 <= pair[0].2 * 3,
                "return recheck exceeds explicit delta growth: {samples:?}"
            );
        }
    }
    #[test]
    fn integrated_use_planner_reserves_and_recovers_without_scanning_the_frame() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let ledger = LoanLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let mut resources = ResourceContext::new().unchecked_with_fact(owner());
            for index in 0..size {
                resources = resources.unchecked_with_fact(token(&format!("frame {index}")));
            }
            let required = CCheckedResourceFact {
                fact: CResourceFact::own(CResource::MutexUse(crate::kernel::MutexUseIdentity {
                    binding: None,
                    initialization: None,
                    mutex: Pointer::symbolic(Variable(100)),
                })),
                role: CResourceTransferRole::Borrow,
                snapshot: CResourceSnapshot::Entry,
                clause_position: None,
                section_index: Some(0),
            };
            let assumptions = PureFactContext::new();
            let ((recovered, work), persistent) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        let plan =
                            plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                                &resources,
                                std::slice::from_ref(&required),
                                &assumptions,
                                &ledger,
                                caller,
                                callee,
                                &LoanViewBindings::default(),
                                &BTreeMap::new(),
                                false,
                            )
                            .unwrap();
                        plan.recheck_entry(&ledger).unwrap();
                        let entry = plan.ledger.clone();
                        let recovered = plan
                            .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
                            .unwrap();
                        assert_eq!(
                            recovered.recheck_transitions(&entry, caller).unwrap(),
                            recovered.terminal_ledger
                        );
                        recovered
                    })
                });
            assert_eq!(recovered.ledger, ledger);
            assert!(recovered.resources.satisfies_fact(&owner(), &assumptions));
            assert_eq!(recovered.resources.facts().len(), size + 1);
            assert!(
                plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                    &resources,
                    &[required.clone(), required.clone()],
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                    &LoanViewBindings::default(),
                    &BTreeMap::new(),
                    false
                )
                .is_err()
            );
            assert!(
                plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                    &resources,
                    &[required],
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                    &LoanViewBindings::default(),
                    &BTreeMap::new(),
                    true
                )
                .is_err()
            );
            samples.push((size, work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
                "integrated use planner scans unrelated frame: {samples:?}"
            );
        }
    }
}
