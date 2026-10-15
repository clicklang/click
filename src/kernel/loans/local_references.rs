//! Checked lifecycle for one exclusive scalar reference and its reborrows.
//!
//! Registration checks an existing owned occurrence; no lifecycle transition
//! creates or returns an owned fact. The private memory adapter reserves that
//! occurrence and checks leases at ordinary scalar loads/stores. Checked source
//! plans bind supported births and endings to actual executed custody.

use super::*;
use crate::kernel::{CType, Pointer};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct LocalReferenceId(u64);

#[derive(Clone, Debug, Eq, PartialEq)]
struct LocalReferenceBacking {
    holder: LoanParticipantId,
    support: ResourceOccurrenceId,
    owned: CResourceFact,
    value_type: CType,
    reservation: Option<Arc<crate::kernel::primitives::ReservedLocalScalarOwner>>,
}

/// A reference instance, rather than a variable name or raw pointer value.
/// Copies retain this identity; a new borrow always receives a fresh one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LocalReferenceBinding {
    id: LocalReferenceId,
    parent: Option<LocalReferenceId>,
    source_plan: Option<crate::kernel::ScalarReferencePlanKey>,
    backing: Arc<LocalReferenceBacking>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LocalReferenceRecord {
    binding: LocalReferenceBinding,
    active: bool,
    child: Option<LocalReferenceId>,
}

impl LocalReferenceId {
    fn fresh() -> Result<Self, LoanRefusal> {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        NEXT.fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |value| value.checked_add(1),
        )
        .map(Self)
        .map_err(|_| LoanRefusal::IdentitySpaceExhausted)
    }
}

#[cfg(test)]
impl LoanLedger {
    pub(super) fn local_references_invariant(&self) -> bool {
        let data = &self.storage.data;
        let expected = data
            .local_references
            .iter()
            .filter(|(_, record)| record.active && record.binding.source_plan.is_some())
            .count();
        if data.source_local_references.len() != expected
            || !data
                .source_local_references
                .iter()
                .all(|((holder, key), id)| {
                    data.local_references.get(id).is_some_and(|record| {
                        record.active
                            && record.binding.backing.holder == *holder
                            && record.binding.source_plan.as_ref() == Some(key)
                    })
                })
        {
            return false;
        }
        let mut holders = BTreeMap::<LoanParticipantId, u64>::new();
        for (_, id) in data.local_reference_roots.iter() {
            let Some(record) = data.local_references.get(id) else {
                return false;
            };
            *holders.entry(record.binding.backing.holder).or_default() += 1;
        }
        if holders.len() != data.local_reference_holders.len()
            || holders
                .iter()
                .any(|(holder, count)| data.local_reference_holders.get(holder) != Some(count))
        {
            return false;
        }
        data.local_references.iter().all(|(id, record)| {
            let binding = &record.binding;
            if binding.id != *id
                || binding.backing.holder.arena != data.arena
                || (!record.active && record.child.is_some())
            {
                return false;
            }
            if let Some(child) = record.child
                && !data.local_references.get(&child).is_some_and(|child| {
                    child.active
                        && child.binding.parent == Some(*id)
                        && Arc::ptr_eq(&binding.backing, &child.binding.backing)
                })
            {
                return false;
            }
            !record.active
                || match binding.parent {
                    Some(parent) => data.local_references.get(&parent).is_some_and(|parent| {
                        parent.active
                            && parent.child == Some(*id)
                            && Arc::ptr_eq(&binding.backing, &parent.binding.backing)
                    }),
                    None => data.local_reference_roots.get(&binding.backing.support) == Some(id),
                }
        }) && data.local_reference_roots.iter().all(|(support, id)| {
            data.local_references.get(id).is_some_and(|record| {
                record.active
                    && record.binding.parent.is_none()
                    && record.binding.backing.support == *support
            })
        })
    }
}

// The checked protocol is staged before source birth/end integration. Keep
// the constructors private to the kernel until that consumer is connected.
#[cfg_attr(not(test), allow(dead_code))]
impl LoanLedger {
    pub(super) fn register_local_reference(
        &self,
        holder: LoanParticipantId,
        resources: &ResourceContext,
        support: ResourceOccurrenceId,
        value_type: CType,
    ) -> Result<(LocalReferenceBinding, CheckedLoanTransition), LoanRefusal> {
        let owned = resources
            .owned_fact_for_occurrence(support)
            .ok_or(LoanRefusal::MissingBacking)?;
        let binding = LocalReferenceBinding {
            id: LocalReferenceId::fresh()?,
            parent: None,
            source_plan: None,
            backing: Arc::new(LocalReferenceBacking {
                holder,
                support,
                owned: owned.clone(),
                value_type,
                reservation: None,
            }),
        };
        let transition = self.issue(LoanTransitionEvidence::RegisterLocalReference(
            binding.clone(),
        ))?;
        Ok((binding, transition))
    }

    pub(super) fn borrow_local_reference(
        &self,
        parent: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<(LocalReferenceBinding, CheckedLoanTransition), LoanRefusal> {
        self.borrow_local_reference_with_source(parent, holder, resources, None)
    }
    pub(super) fn borrow_local_reference_with_source(
        &self,
        parent: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
        source_plan: Option<crate::kernel::ScalarReferencePlanKey>,
    ) -> Result<(LocalReferenceBinding, CheckedLoanTransition), LoanRefusal> {
        self.validate_local_reference(parent, holder, resources)?;
        if source_plan.as_ref().is_some_and(|key| {
            self.storage
                .data
                .source_local_references
                .contains_key(&(holder, key.clone()))
        }) {
            return Err(LoanRefusal::ActiveDependency);
        }
        let child = LocalReferenceBinding {
            id: LocalReferenceId::fresh()?,
            parent: Some(parent.id),
            source_plan,
            backing: parent.backing.clone(),
        };
        let transition = self.issue(LoanTransitionEvidence::BorrowLocalReference(child.clone()))?;
        Ok((child, transition))
    }

    /// Lifecycle custody is necessary but never sufficient for a load/store.
    /// The normal memory producer must independently check memory authority.
    pub(super) fn validate_local_reference_access(
        &self,
        binding: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
        pointer: &Pointer,
        value_type: CType,
    ) -> Result<(), LoanRefusal> {
        self.validate_local_reference(binding, holder, resources)?;
        if binding.backing.value_type != value_type
            || binding
                .backing
                .owned
                .memory_own_range()
                .unwrap()
                .start_pointer()
                != *pointer
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }

    pub(super) fn recover_local_reference(
        &self,
        child: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.validate_local_reference(child, holder, resources)?;
        self.issue(LoanTransitionEvidence::RecoverLocalReference(child.clone()))
    }

    pub(super) fn retire_local_reference_root(
        &self,
        root: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.validate_local_reference(root, holder, resources)?;
        self.issue(LoanTransitionEvidence::RetireLocalReferenceRoot(
            root.clone(),
        ))
    }

    fn local_reference_record(
        &self,
        binding: &LocalReferenceBinding,
    ) -> Result<&LocalReferenceRecord, LoanRefusal> {
        self.require_participant(binding.backing.holder)?;
        let record = self
            .storage
            .data
            .local_references
            .get(&binding.id)
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if record.binding != *binding {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if !record.active {
            return Err(LoanRefusal::AlreadyRecovered);
        }
        if record.child.is_some() {
            return Err(LoanRefusal::ActiveDependency);
        }
        Ok(record)
    }

    fn validate_local_reference(
        &self,
        binding: &LocalReferenceBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<(), LoanRefusal> {
        self.require_participant(holder)?;
        if holder != binding.backing.holder {
            return Err(LoanRefusal::WrongHolder);
        }
        self.local_reference_record(binding)?;
        if !resources.owned_occurrence_matches(binding.backing.support, &binding.backing.owned) {
            return Err(LoanRefusal::MissingBacking);
        }
        Ok(())
    }

    pub(super) fn apply_local_reference_registration(
        &self,
        data: &mut LoanLedgerData,
        binding: &LocalReferenceBinding,
    ) -> Result<(), LoanRefusal> {
        self.require_participant(binding.backing.holder)?;
        let backing = &binding.backing;
        // Start with a single exactly owned scalar. Aggregate/fragment
        // partitioning and differently typed subviews are separate operations.
        if binding.parent.is_some()
            || data.local_references.contains_key(&binding.id)
            || data.local_reference_roots.contains_key(&backing.support)
            || backing.support == ResourceOccurrenceId::default()
            || backing
                .reservation
                .as_ref()
                .is_some_and(|reservation| !reservation.matches(backing.support, &backing.owned))
            || !matches!(
                backing.value_type,
                CType::Int32 | CType::UInt8 | CType::UInt16 | CType::UInt32
            )
            || backing
                .owned
                .owned_quantity_term()
                .and_then(|q| q.as_const())
                != Some(1)
            || !backing.owned.memory_own_range().is_some_and(|range| {
                range
                    .signed_constant_end()
                    .zip(range.signed_constant_start())
                    .is_some_and(|(end, start)| {
                        end.checked_sub(start)
                            .and_then(|count| count.checked_mul(i64::from(range.element_width())))
                            == Some(i64::from(backing.value_type.byte_width()))
                    })
            })
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        data.local_references = data.local_references.with_inserted(
            binding.id,
            LocalReferenceRecord {
                binding: binding.clone(),
                active: true,
                child: None,
            },
        );
        data.local_reference_roots = data
            .local_reference_roots
            .with_inserted(backing.support, binding.id);
        let count = data
            .local_reference_holders
            .get(&backing.holder)
            .copied()
            .unwrap_or(0);
        data.local_reference_holders = data.local_reference_holders.with_inserted(
            backing.holder,
            count
                .checked_add(1)
                .ok_or(LoanRefusal::IdentitySpaceExhausted)?,
        );
        Ok(())
    }

    pub(super) fn apply_local_reference_borrow(
        &self,
        data: &mut LoanLedgerData,
        child: &LocalReferenceBinding,
    ) -> Result<(), LoanRefusal> {
        let parent_id = child.parent.ok_or(LoanRefusal::InvalidEvidence)?;
        if data.local_references.contains_key(&child.id) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let mut parent = data
            .local_references
            .get(&parent_id)
            .cloned()
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        self.local_reference_record(&parent.binding)?;
        if !Arc::ptr_eq(&parent.binding.backing, &child.backing) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if let Some(key) = &child.source_plan {
            let key = (child.backing.holder, key.clone());
            if data.source_local_references.contains_key(&key) {
                return Err(LoanRefusal::ActiveDependency);
            }
            data.source_local_references =
                data.source_local_references.with_inserted(key, child.id);
        }
        parent.child = Some(child.id);
        data.local_references = data
            .local_references
            .with_inserted(parent_id, parent)
            .with_inserted(
                child.id,
                LocalReferenceRecord {
                    binding: child.clone(),
                    active: true,
                    child: None,
                },
            );
        Ok(())
    }

    pub(super) fn apply_local_reference_recovery(
        &self,
        data: &mut LoanLedgerData,
        child: &LocalReferenceBinding,
    ) -> Result<(), LoanRefusal> {
        let mut ended = self.local_reference_record(child)?.clone();
        let parent_id = child.parent.ok_or(LoanRefusal::InvalidEvidence)?;
        let mut parent = data
            .local_references
            .get(&parent_id)
            .cloned()
            .ok_or(LoanRefusal::MissingLoanBinding)?;
        if !parent.active
            || parent.child != Some(child.id)
            || !Arc::ptr_eq(&parent.binding.backing, &child.backing)
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if let Some(key) = &child.source_plan {
            let key = (child.backing.holder, key.clone());
            if data.source_local_references.get(&key) != Some(&child.id) {
                return Err(LoanRefusal::InvalidEvidence);
            }
            data.source_local_references = data.source_local_references.without_key(&key);
        }
        parent.child = None;
        ended.active = false;
        data.local_references = data
            .local_references
            .with_inserted(parent_id, parent)
            .with_inserted(child.id, ended);
        Ok(())
    }

    pub(super) fn apply_local_reference_retirement(
        &self,
        data: &mut LoanLedgerData,
        root: &LocalReferenceBinding,
    ) -> Result<(), LoanRefusal> {
        let mut record = self.local_reference_record(root)?.clone();
        if root.parent.is_some()
            || data.local_reference_roots.get(&root.backing.support) != Some(&root.id)
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        record.active = false;
        data.local_references = data.local_references.with_inserted(root.id, record);
        data.local_reference_roots = data
            .local_reference_roots
            .without_key(&root.backing.support);
        let count = data
            .local_reference_holders
            .get(&root.backing.holder)
            .copied()
            .ok_or(LoanRefusal::InvalidEvidence)?;
        data.local_reference_holders = if count == 1 {
            data.local_reference_holders
                .without_key(&root.backing.holder)
        } else {
            data.local_reference_holders
                .with_inserted(root.backing.holder, count - 1)
        };
        Ok(())
    }
}

mod memory;
pub(in crate::kernel) use memory::LocalScalarReference;

#[cfg(test)]
mod tests;
