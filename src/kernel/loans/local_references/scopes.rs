//! A checked local-only transaction restores its exact entry ledger after
//! every new reference has ended. Fresh IDs live outside rollback state.
use super::*;
use crate::kernel::ScalarReferenceScopeKey;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel::loans) struct LocalReferenceScope {
    base: LoanLedger,
    holder: LoanParticipantId,
    key: ScalarReferenceScopeKey,
    issued: PersistentSet<LocalReferenceId>,
    active: usize,
    restored: PersistentMap<ResourceOccurrenceId, CResourceFact>,
}
impl LoanLedger {
    pub(in crate::kernel) fn begin_local_reference_scope(
        &self,
        holder: LoanParticipantId,
        key: ScalarReferenceScopeKey,
    ) -> Result<Self, LoanRefusal> {
        self.require_participant(holder)?;
        if self
            .storage
            .data
            .local_reference_scope
            .as_ref()
            .is_some_and(|scope| scope.holder != holder)
        {
            return Err(LoanRefusal::WrongHolder);
        }
        let mut data = self.storage.data.clone();
        data.local_reference_scope = Some(Arc::new(LocalReferenceScope {
            base: self.clone(),
            holder,
            key,
            issued: PersistentSet::default(),
            active: 0,
            restored: PersistentMap::default(),
        }));
        Ok(Self {
            storage: Arc::new(LoanLedgerStorage {
                state: LoanLedgerStateId::fresh(),
                data,
            }),
        })
    }
    pub(in crate::kernel) fn close_local_reference_scope(
        &self,
        holder: LoanParticipantId,
        key: &ScalarReferenceScopeKey,
        resources: &ResourceContext,
    ) -> Result<Self, LoanRefusal> {
        let scope = self
            .storage
            .data
            .local_reference_scope
            .as_ref()
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if scope.holder != holder {
            return Err(LoanRefusal::WrongHolder);
        }
        if &scope.key != key {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if scope.active != 0 {
            return Err(LoanRefusal::ActiveDependency);
        }
        for (support, owned) in scope.restored.iter() {
            if resources.owned_fact_for_occurrence(*support) != Some(owned) {
                return Err(LoanRefusal::MissingBacking);
            }
        }
        // Only the four checked local transitions can advance this frame.
        // They cannot end an entry reference. Each new registration/borrow
        // adds one active ID and its matching recovery/retirement removes one.
        // At zero, entry parents and all original support are restored.
        Ok(scope.base.clone())
    }
    pub(in crate::kernel::loans) fn advance_local_reference_scope(
        &self,
        data: &mut LoanLedgerData,
        evidence: &LoanTransitionEvidence,
    ) -> Result<(), LoanRefusal> {
        let Some(frame) = &data.local_reference_scope else {
            return Ok(());
        };
        let mut frame = frame.as_ref().clone();
        match evidence {
            LoanTransitionEvidence::RegisterLocalReference(binding)
            | LoanTransitionEvidence::BorrowLocalReference(binding) => {
                if binding.backing.holder != frame.holder {
                    return Err(LoanRefusal::WrongHolder);
                }
                if frame.issued.contains(&binding.id) {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                if binding.parent.is_none() {
                    let support = binding.backing.support;
                    if frame
                        .restored
                        .get(&support)
                        .is_some_and(|old| old != &binding.backing.owned)
                    {
                        return Err(LoanRefusal::InvalidEvidence);
                    }
                    frame.restored = frame
                        .restored
                        .with_inserted(support, binding.backing.owned.clone());
                }
                frame.issued = frame.issued.with_value(binding.id);
                frame.active = frame
                    .active
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
            }
            LoanTransitionEvidence::RecoverLocalReference(binding)
            | LoanTransitionEvidence::RetireLocalReferenceRoot(binding) => {
                if binding.backing.holder != frame.holder {
                    return Err(LoanRefusal::WrongHolder);
                }
                if !frame.issued.contains(&binding.id) {
                    return Err(LoanRefusal::ActiveDependency);
                }
                frame.active = frame
                    .active
                    .checked_sub(1)
                    .ok_or(LoanRefusal::InvalidEvidence)?;
            }
            _ => return Err(LoanRefusal::UnsupportedResource),
        }
        data.local_reference_scope = Some(Arc::new(frame));
        Ok(())
    }
}
