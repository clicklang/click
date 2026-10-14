//! Exact identities for synchronous borrowed ownership. Memory authority and
//! updated values remain in the ordinary resource partition and call result.
//! This receipt tracks lifetime/dependency, and never mints an owned fact.

use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct ExclusiveCallId(u64);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ExclusiveCallBinding {
    id: ExclusiveCallId,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent: Option<ExclusiveCallId>,
    // Only this call's selected memory reservations, including every support
    // when the planner joined several fragments. Sharing avoids copying them
    // when a sibling or nested call changes the persistent ledger.
    pub(super) supports: Arc<[(CResourceFact, ResourceOccurrenceId)]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ExclusiveCallRecord {
    binding: ExclusiveCallBinding,
    active: bool,
    children: usize,
}

impl LoanLedger {
    #[cfg(test)]
    pub(super) fn exclusive_calls_invariant(&self) -> bool {
        let data = &self.storage.data;
        let mut counts = BTreeMap::<ExclusiveCallId, usize>::new();
        for (id, record) in data.exclusive_calls.iter() {
            if record.binding.id != *id
                || record.binding.caller.arena != data.arena
                || record.binding.callee.arena != data.arena
                || (!record.active && record.children != 0)
            {
                return false;
            }
            if record.active {
                if data.exclusive_holders.get(&record.binding.callee) != Some(id) {
                    return false;
                }
                if let Some(parent) = record.binding.parent {
                    if !data
                        .exclusive_calls
                        .get(&parent)
                        .is_some_and(|parent_record| {
                            parent_record.active
                                && parent_record.binding.callee == record.binding.caller
                        })
                    {
                        return false;
                    }
                    *counts.entry(parent).or_default() += 1;
                }
            }
        }
        data.exclusive_calls
            .iter()
            .all(|(id, record)| record.children == counts.get(id).copied().unwrap_or(0))
            && data.exclusive_holders.iter().all(|(holder, id)| {
                data.exclusive_calls
                    .get(id)
                    .is_some_and(|record| record.active && record.binding.callee == *holder)
            })
    }

    pub(super) fn open_exclusive_call(
        &self,
        caller: LoanParticipantId,
        callee: LoanParticipantId,
        supports: Vec<(CResourceFact, ResourceOccurrenceId)>,
    ) -> Result<(ExclusiveCallBinding, CheckedLoanTransition), LoanRefusal> {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = NEXT
            .fetch_update(
                std::sync::atomic::Ordering::Relaxed,
                std::sync::atomic::Ordering::Relaxed,
                |value| value.checked_add(1),
            )
            .map(ExclusiveCallId)
            .map_err(|_| LoanRefusal::IdentitySpaceExhausted)?;
        let binding = ExclusiveCallBinding {
            id,
            caller,
            callee,
            parent: self.storage.data.exclusive_holders.get(&caller).copied(),
            supports: supports.into(),
        };
        let transition = self.issue(LoanTransitionEvidence::OpenExclusiveCall(binding.clone()))?;
        Ok((binding, transition))
    }

    pub(super) fn validate_exclusive_call(
        &self,
        binding: &ExclusiveCallBinding,
        holder: LoanParticipantId,
    ) -> Result<(), LoanRefusal> {
        self.require_participant(holder)?;
        if holder != binding.callee {
            return Err(LoanRefusal::WrongHolder);
        }
        let record = self
            .storage
            .data
            .exclusive_calls
            .get(&binding.id)
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if !record.active {
            return Err(LoanRefusal::AlreadyRecovered);
        }
        if record.binding != *binding
            || self.storage.data.exclusive_holders.get(&holder) != Some(&binding.id)
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }

    pub(super) fn return_exclusive_call(
        &self,
        binding: &ExclusiveCallBinding,
        holder: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.issue(LoanTransitionEvidence::ReturnExclusiveCall {
            binding: binding.clone(),
            holder,
        })
    }

    pub(super) fn validate_returned_exclusive_call(
        &self,
        binding: &ExclusiveCallBinding,
    ) -> Result<(), LoanRefusal> {
        let record = self
            .storage
            .data
            .exclusive_calls
            .get(&binding.id)
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if record.binding != *binding {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if record.active || record.children != 0 {
            return Err(LoanRefusal::ScopeStillActive);
        }
        Ok(())
    }

    pub(super) fn apply_exclusive_open(
        &self,
        data: &mut LoanLedgerData,
        binding: &ExclusiveCallBinding,
    ) -> Result<(), LoanRefusal> {
        self.require_participant(binding.caller)?;
        self.require_participant(binding.callee)?;
        if binding.caller == binding.callee
            || binding.supports.is_empty()
            || binding
                .supports
                .iter()
                .any(|(fact, _)| fact.memory_own_range().is_none())
            || data.exclusive_calls.contains_key(&binding.id)
            || data.exclusive_holders.contains_key(&binding.callee)
            || data.exclusive_holders.get(&binding.caller).copied() != binding.parent
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if let Some(parent) = binding.parent {
            let mut record = data
                .exclusive_calls
                .get(&parent)
                .cloned()
                .ok_or(LoanRefusal::MissingLoanBinding)?;
            if !record.active || record.binding.callee != binding.caller {
                return Err(LoanRefusal::InvalidEvidence);
            }
            record.children = record
                .children
                .checked_add(1)
                .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
            data.exclusive_calls = data.exclusive_calls.with_inserted(parent, record);
        }
        data.exclusive_calls = data.exclusive_calls.with_inserted(
            binding.id,
            ExclusiveCallRecord {
                binding: binding.clone(),
                active: true,
                children: 0,
            },
        );
        data.exclusive_holders = data
            .exclusive_holders
            .with_inserted(binding.callee, binding.id);
        Ok(())
    }

    pub(super) fn apply_exclusive_return(
        &self,
        data: &mut LoanLedgerData,
        binding: &ExclusiveCallBinding,
        holder: LoanParticipantId,
    ) -> Result<(), LoanRefusal> {
        self.require_participant(holder)?;
        if holder != binding.caller {
            return Err(LoanRefusal::WrongHolder);
        }
        self.validate_exclusive_call(binding, binding.callee)?;
        let mut record = data
            .exclusive_calls
            .get(&binding.id)
            .cloned()
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if record.children != 0 {
            return Err(LoanRefusal::ActiveDependency);
        }
        record.active = false;
        data.exclusive_calls = data.exclusive_calls.with_inserted(binding.id, record);
        data.exclusive_holders = data.exclusive_holders.without_key(&binding.callee);
        if let Some(parent) = binding.parent {
            let mut record = data
                .exclusive_calls
                .get(&parent)
                .cloned()
                .ok_or(LoanRefusal::MissingLoanBinding)?;
            record.children = record
                .children
                .checked_sub(1)
                .ok_or(LoanRefusal::InvalidEvidence)?;
            data.exclusive_calls = data.exclusive_calls.with_inserted(parent, record);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan(
        resources: &ResourceContext,
        ledger: &LoanLedger,
        caller: LoanParticipantId,
        callee: LoanParticipantId,
        fact: CResourceFact,
    ) -> StableViewTransferPlan {
        plan_stable_view_transfer(
            resources,
            &[super::super::tests::checked(fact)],
            &PureFactContext::new(),
            ledger,
            caller,
            callee,
        )
        .unwrap()
    }

    #[test]
    fn exclusive_call_tracks_nested_return_and_disjoint_parent_authority() {
        use super::super::tests::memory;
        let facts = PureFactContext::new();
        let resources = ResourceContext::new().unchecked_with_fact(memory(0, 8, true));
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let child = ledger.fresh_participant().unwrap();
        let grandchild = ledger.fresh_participant().unwrap();
        let first = plan(&resources, &ledger, owner, child, memory(0, 4, true));
        let binding = first.exclusive_call.clone().unwrap();
        assert!(
            first
                .caller_resources_after_requirements
                .satisfies_fact(&memory(4, 8, true), &facts)
        );
        assert!(
            !first
                .caller_resources_after_requirements
                .satisfies_fact(&memory(0, 1, false), &facts)
        );
        assert!(
            !first
                .caller_resources_after_requirements
                .satisfies_fact(&memory(0, 1, true), &facts)
        );
        first
            .ledger
            .validate_exclusive_call(&binding, child)
            .unwrap();
        assert_eq!(
            first.ledger.validate_exclusive_call(&binding, owner),
            Err(LoanRefusal::WrongHolder)
        );
        let nested = plan(
            &first.callee_resources,
            &first.ledger,
            child,
            grandchild,
            memory(0, 2, true),
        );
        assert!(nested.ledger.invariant_holds());
        assert!(
            nested
                .caller_resources_after_requirements
                .satisfies_fact(&memory(2, 4, true), &facts)
        );
        assert_eq!(
            nested.ledger.return_exclusive_call(&binding, owner),
            Err(LoanRefusal::ActiveDependency)
        );
        let nested_binding = nested.exclusive_call.clone().unwrap();
        let back = nested
            .ledger
            .return_exclusive_call(&nested_binding, child)
            .unwrap();
        let after = nested.ledger.apply(&back).unwrap();
        assert!(after.invariant_holds());
        assert_eq!(
            after.validate_exclusive_call(&nested_binding, grandchild),
            Err(LoanRefusal::AlreadyRecovered)
        );
        assert_eq!(
            after.return_exclusive_call(&nested_binding, child),
            Err(LoanRefusal::AlreadyRecovered)
        );
        let back = after.return_exclusive_call(&binding, owner).unwrap();
        after.apply(&back).unwrap();
        // Actual modular recovery also checks the history before restoring its
        // predecessor root; a receipt is not an additional owned resource.
        let recovery = nested
            .clone()
            .recover_stable_views(&facts, &BTreeMap::new(), &[])
            .unwrap();
        assert_eq!(recovery.ledger, first.ledger);
        recovery.recheck_transitions(&nested.ledger, child).unwrap();
    }

    #[test]
    fn exclusive_call_rejects_wrong_receipt_and_missing_recovery() {
        use super::super::tests::memory;
        let facts = PureFactContext::new();
        let resources = ResourceContext::new().unchecked_with_fact(memory(0, 4, true));
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let child = ledger.fresh_participant().unwrap();
        let first = plan(&resources, &ledger, owner, child, memory(0, 4, true));
        let binding = first.exclusive_call.clone().unwrap();
        assert_eq!(
            first.ledger.return_exclusive_call(&binding, child),
            Err(LoanRefusal::WrongHolder)
        );
        let second = plan(&resources, &ledger, owner, child, memory(0, 4, true));
        assert_ne!(second.exclusive_call.as_ref().unwrap().id, binding.id);
        assert!(
            second
                .ledger
                .return_exclusive_call(&binding, owner)
                .is_err()
        );
        let mut forged = binding.clone();
        forged.supports = Arc::from([]);
        assert_eq!(
            first.ledger.return_exclusive_call(&forged, owner),
            Err(LoanRefusal::InvalidEvidence)
        );
        let mut missing = first.clone();
        missing.exclusive_call = None;
        assert!(
            missing
                .recover_stable_views(&facts, &BTreeMap::new(), &[])
                .is_err()
        );
        let recovery = first
            .clone()
            .recover_stable_views(&facts, &BTreeMap::new(), &[])
            .unwrap();
        let mut evidence = CheckedLoanCallEvidence::new(
            first.clone(),
            recovery.ledger,
            recovery.terminal_ledger,
            recovery.transitions,
            recovery.hold_base_ledger,
            recovery.hold_transitions,
        );
        evidence
            .recheck(&ledger, Some(owner), &first.ledger, Some(child))
            .unwrap();
        evidence.recovery_transitions.clear();
        assert!(
            evidence
                .recheck(&ledger, Some(owner), &first.ledger, Some(child))
                .is_err()
        );
        // An alleged matching terminal root cannot replace child return.
        evidence.recovery_terminal_ledger = first.ledger.clone();
        assert_eq!(
            evidence.recheck(&ledger, Some(owner), &first.ledger, Some(child)),
            Err(LoanRefusal::ScopeStillActive)
        );
    }

    #[test]
    fn exclusive_call_selected_transition_ignores_unrelated_scopes() {
        use super::super::tests::memory;
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut ledger = LoanLedger::new();
            let owner = ledger.fresh_participant().unwrap();
            let support = ResourceContext::new()
                .unchecked_with_fact(memory(0, 4, true))
                .unique_owned_occurrence_for_fact(&memory(0, 4, true))
                .unwrap()
                .0;
            for _ in 0..size {
                let caller = ledger.fresh_participant().unwrap();
                let callee = ledger.fresh_participant().unwrap();
                let (_, transition) = ledger
                    .open_exclusive_call(caller, callee, vec![(memory(0, 4, true), support)])
                    .unwrap();
                ledger = ledger.apply(&transition).unwrap();
            }
            let child = ledger.fresh_participant().unwrap();
            let ((), work) = crate::persistent::measure_persistent_work(|| {
                let (binding, enter) = ledger
                    .open_exclusive_call(owner, child, vec![(memory(0, 4, true), support)])
                    .unwrap();
                let entered = ledger.apply(&enter).unwrap();
                entered.validate_exclusive_call(&binding, child).unwrap();
                let leave = entered.return_exclusive_call(&binding, owner).unwrap();
                entered.apply(&leave).unwrap();
            });
            samples.push((size, work));
            assert!(
                work < 1200,
                "selected transition scanned unrelated scopes: {samples:?}"
            );
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 + 32,
                "selected lookup grew with ambient scopes: {samples:?}"
            );
        }
    }

    #[test]
    fn exclusive_call_preserves_joined_fragment_supports_and_move_roles() {
        use super::super::tests::{checked, memory};
        let facts = PureFactContext::new();
        let resources =
            ResourceContext::new().unchecked_with_facts([memory(0, 2, true), memory(2, 4, true)]);
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let child = ledger.fresh_participant().unwrap();
        let borrowed = plan(&resources, &ledger, owner, child, memory(0, 4, true));
        let binding = borrowed.exclusive_call.as_ref().unwrap();
        assert_eq!(binding.supports.len(), 2);
        assert_ne!(binding.supports[0].1, binding.supports[1].1);
        borrowed.recheck_entry(&ledger).unwrap();
        borrowed
            .recover_stable_views(&facts, &BTreeMap::new(), &[])
            .unwrap();
        let mut moved = checked(memory(0, 4, true));
        moved.role = CResourceTransferRole::Consume;
        let move_plan =
            plan_stable_view_transfer(&resources, &[moved], &facts, &ledger, owner, child).unwrap();
        assert!(move_plan.exclusive_call.is_none());
        assert!(move_plan.ledger.is_pristine());
    }
}
