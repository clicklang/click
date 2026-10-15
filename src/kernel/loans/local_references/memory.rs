//! Private scalar-reference adapter for the ordinary memory producers.
//!
//! Source observations cannot construct these leases. Checked source plans
//! issue births and bind endings to actual executed lvalue custody.

use super::*;
use crate::kernel::primitives::ReservedLocalScalarOwner;
use crate::kernel::{CPointerValue, CState};

/// Opaque custody carried by pointer values, including local copies and casts.
/// The current ledger retains the backing; values carry only a fresh identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct LocalScalarReference(LocalReferenceId);

impl LocalScalarReference {
    pub(in crate::kernel) fn id(&self) -> LocalReferenceId {
        self.0
    }
}

impl LoanLedger {
    pub(in crate::kernel) fn holder_has_local_references(&self, holder: LoanParticipantId) -> bool {
        self.storage
            .data
            .local_reference_holders
            .contains_key(&holder)
    }

    fn local_scalar_reference(
        &self,
        reference: &LocalScalarReference,
    ) -> Result<
        (
            &LocalReferenceBinding,
            &ReservedLocalScalarOwner,
            LocalReferenceId,
        ),
        LoanRefusal,
    > {
        let record = self
            .storage
            .data
            .local_references
            .get(&reference.0)
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        self.local_reference_record(&record.binding)?;
        let binding = &record.binding;
        let reservation = binding
            .backing
            .reservation
            .as_deref()
            .ok_or(LoanRefusal::MissingBacking)?;
        let root = *self
            .storage
            .data
            .local_reference_roots
            .get(&binding.backing.support)
            .ok_or(LoanRefusal::MissingBacking)?;
        Ok((binding, reservation, root))
    }
}

impl CState {
    pub(in crate::kernel) fn has_local_scalar_references(&self) -> bool {
        self.loan_ledger()
            .is_some_and(|ledger| match self.loan_participant() {
                Some(holder) => ledger.holder_has_local_references(holder),
                None => !ledger.storage.data.local_reference_roots.is_empty(),
            })
    }

    /// Temporarily expose this lease's owner to one ordinary load/store. The
    /// caller must discard that selected occurrence before publishing a state.
    pub(in crate::kernel) fn local_scalar_access_resources(
        &self,
        reference: &LocalScalarReference,
        pointer: &Pointer,
        value_type: CType,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, ResourceOccurrenceId), LoanRefusal> {
        let ledger = self.loan_ledger().ok_or(LoanRefusal::MissingLoanBinding)?;
        let holder = self.loan_participant().ok_or(LoanRefusal::WrongHolder)?;
        let (binding, reservation, _) = ledger.local_scalar_reference(reference)?;
        ledger.validate_local_reference_access(
            binding,
            holder,
            &reservation.resources(assumptions),
            pointer,
            value_type,
        )?;
        let (resources, mut inserted) = self
            .resources()
            .clone()
            .try_compose_into_valid_context_with_occurrences(
                [binding.backing.owned.clone()],
                assumptions,
            )
            .map_err(|_| LoanRefusal::InvalidEvidence)?;
        Ok((
            resources,
            inserted.pop().ok_or(LoanRefusal::MissingBacking)?.1,
        ))
    }
}

// Source plans and kernel tests use these private constructors. Observation
// labels never supply custody, ownership, or a recovery right.
#[cfg_attr(not(test), allow(dead_code))]
impl CState {
    pub(in crate::kernel) fn begin_local_scalar_reference(
        &self,
        parent: &CPointerValue,
        support: Option<ResourceOccurrenceId>,
        value_type: CType,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CPointerValue), LoanRefusal> {
        self.begin_scalar_reference(parent, support, value_type, assumptions, None)
    }
    pub(in crate::kernel) fn begin_source_scalar_reference(
        &self,
        parent: &CPointerValue,
        support: ResourceOccurrenceId,
        value_type: CType,
        assumptions: &PureFactContext,
        key: crate::kernel::ScalarReferencePlanKey,
    ) -> Result<(Self, CPointerValue), LoanRefusal> {
        self.begin_scalar_reference(parent, Some(support), value_type, assumptions, Some(key))
    }
    fn begin_scalar_reference(
        &self,
        parent: &CPointerValue,
        support: Option<ResourceOccurrenceId>,
        value_type: CType,
        assumptions: &PureFactContext,
        source_plan: Option<crate::kernel::ScalarReferencePlanKey>,
    ) -> Result<(Self, CPointerValue), LoanRefusal> {
        let holder = self.loan_participant().ok_or(LoanRefusal::WrongHolder)?;
        let ledger = self.loan_ledger().ok_or(LoanRefusal::MissingLoanBinding)?;
        let (ledger, resources, parent_binding) = if let Some(reference) = parent.local_reference()
        {
            if support.is_some() {
                return Err(LoanRefusal::InvalidEvidence);
            }
            let (binding, reservation, _) = ledger.local_scalar_reference(reference)?;
            ledger.validate_local_reference_access(
                binding,
                holder,
                &reservation.resources(assumptions),
                parent.pointer(),
                value_type,
            )?;
            (ledger.clone(), self.resources().clone(), binding.clone())
        } else {
            let support = support.ok_or(LoanRefusal::MissingBacking)?;
            let owned = self
                .resources()
                .owned_fact_for_occurrence(support)
                .ok_or(LoanRefusal::MissingBacking)?;
            let range = owned
                .memory_own_range()
                .ok_or(LoanRefusal::MissingBacking)?;
            if range.start_pointer() != *parent.pointer()
                || parent.c_type().pointee_type() != Some(value_type)
                || (!crate::kernel::eval::is_external_memory_pointer(parent.pointer())
                    && !self
                        .memory
                        .requires_explicit_scalar_ownership(parent.pointer()))
            {
                return Err(LoanRefusal::UnsupportedResource);
            }
            // Existing mutex/shared-loan restrictions still apply at birth.
            if crate::kernel::eval::memory_write_permission_outcome(
                self,
                parent.pointer(),
                value_type.byte_width(),
                assumptions,
            )
            .is_some()
            {
                return Err(LoanRefusal::ActiveDependency);
            }
            let (resources, reservation) = self
                .resources()
                .clone()
                .reserve_local_scalar_owner(support)
                .ok_or(LoanRefusal::MissingBacking)?;
            let root = LocalReferenceBinding {
                id: LocalReferenceId::fresh()?,
                parent: None,
                backing: Arc::new(LocalReferenceBacking {
                    holder,
                    support,
                    owned: owned.clone(),
                    value_type,
                    reservation: Some(Arc::new(reservation)),
                    source_plan,
                }),
            };
            let birth =
                ledger.issue(LoanTransitionEvidence::RegisterLocalReference(root.clone()))?;
            (ledger.apply(&birth)?, resources, root)
        };
        let reserved = parent_binding
            .backing
            .reservation
            .as_ref()
            .ok_or(LoanRefusal::MissingBacking)?
            .resources(assumptions);
        let (binding, birth) = ledger.borrow_local_reference(&parent_binding, holder, &reserved)?;
        let ledger = ledger.apply(&birth)?;
        let pointer = parent
            .clone()
            .with_local_reference(LocalScalarReference(binding.id));
        Ok((
            self.clone()
                .with_resource_context(resources)
                .with_loan_ledger(Some(ledger)),
            pointer,
        ))
    }

    pub(in crate::kernel) fn validate_source_scalar_reference(
        &self,
        reference: &LocalScalarReference,
        key: &crate::kernel::ScalarReferencePlanKey,
    ) -> Result<(), LoanRefusal> {
        let ledger = self.loan_ledger().ok_or(LoanRefusal::MissingLoanBinding)?;
        let (binding, _, _) = ledger.local_scalar_reference(reference)?;
        if binding.backing.source_plan.as_ref() != Some(key) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }

    pub(in crate::kernel) fn end_local_scalar_reference(
        &self,
        pointer: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Result<Self, LoanRefusal> {
        let reference = pointer
            .local_reference()
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        let holder = self.loan_participant().ok_or(LoanRefusal::WrongHolder)?;
        let ledger = self.loan_ledger().ok_or(LoanRefusal::MissingLoanBinding)?;
        let (binding, reservation, root_id) = ledger.local_scalar_reference(reference)?;
        let reserved = reservation.resources(assumptions);
        ledger.validate_local_reference_access(
            binding,
            holder,
            &reserved,
            pointer.pointer(),
            binding.backing.value_type,
        )?;
        let ending = ledger.recover_local_reference(binding, holder, &reserved)?;
        let mut recovered = ledger.apply(&ending)?;
        let mut resources = self.resources().clone();
        if binding.parent == Some(root_id) {
            let root = &recovered
                .storage
                .data
                .local_references
                .get(&root_id)
                .ok_or(LoanRefusal::MissingLoanBinding)?
                .binding;
            let ending = recovered.retire_local_reference_root(root, holder, &reserved)?;
            recovered = recovered.apply(&ending)?;
            resources = reservation
                .restore_into(resources, assumptions)
                .ok_or(LoanRefusal::InvalidEvidence)?;
        }
        // Only authority changes. In particular, never restore birth memory.
        Ok(self
            .clone()
            .with_resource_context(resources)
            .with_loan_ledger(Some(recovered)))
    }
}

#[cfg(test)]
mod tests;
