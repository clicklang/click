//! Indexed resource admission. Unsupported coverage is returned, never searched.
use super::*;
use crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap;

/// A successor is available only after every new resource has been admitted.
#[must_use]
pub(crate) enum OwnershipAdmission<'a> {
    Admitted {
        context: ResourceContext,
        inserted: Vec<(ResourceFact, ResourceOccurrenceId)>,
    },
    Conflict(ResourceContextValidityError),
    Unsupported(PendingOwnershipAdmission<'a>),
}

/// An opaque, incomplete admission. Its candidate context is not a valid
/// successor yet. Only the legacy operation may finish the deferred checks.
/// Keep the original assumptions and progress so resumption neither changes
/// the checked namespace nor retries insertion or completed validity checks.
pub(crate) struct PendingOwnershipAdmission<'a> {
    pub(super) context: ResourceContext,
    pub(super) inserted: Vec<(ResourceFact, ResourceOccurrenceId)>,
    pub(super) indexed_checked: Vec<bool>,
    pub(super) first_new: ResourceEntryId,
    // Exclusive validity has already been checked for this entry; its
    // overlap check and all later entries remain to be processed.
    pub(super) first_unresolved: ResourceEntryId,
    pub(super) assumptions: &'a PureFactContext,
}

/// The only new obligation for a constructed flat composite body is its
/// boundary with the retained caller frame. Unsupported geometry stays on
/// the compatibility path; it never counts as established separation.
pub(crate) enum FlatBodyAdmission {
    Admitted,
    Conflict {
        piece: Box<ResourceFact>,
        held: Box<ResourceFact>,
    },
    Unsupported,
}

impl ResourceContext {
    /// Admit a returned composite's already-constructed flat body against
    /// this frame. The body producer established its own composition; query
    /// only cross-boundary memory overlap, without inserting temporary child
    /// owners or validating either side again. Tokens add and views duplicate.
    pub(in crate::kernel) fn admit_returned_flat_body(
        &self,
        body: &crate::kernel::functions::ConstructedReturnBody,
        assumptions: &PureFactContext,
    ) -> FlatBodyAdmission {
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("returned flat body admission");
        for piece in body.owned_memory_frontier() {
            let _checking = crate::instrumentation::CheckingWorkScope::new(
                "admit returned flat memory leaf",
                1,
            );
            crate::instrumentation::record_deterministic_work(1);
            match self.constant_owned_overlap(piece, assumptions) {
                ConstantOwnedOverlap::Clear => {}
                ConstantOwnedOverlap::Overlap(entry) => {
                    return FlatBodyAdmission::Conflict {
                        piece: Box::new(piece.clone()),
                        held: Box::new(self.fact(entry).clone()),
                    };
                }
                ConstantOwnedOverlap::Unsupported => return FlatBodyAdmission::Unsupported,
            }
        }
        FlatBodyAdmission::Admitted
    }

    /// Admit explicit resources using maintained indexes only. This operation
    /// never invokes discovery when the index cannot decide an overlap.
    pub(crate) fn admit_without_discovery(
        mut self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> OwnershipAdmission<'_> {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("admit_without_discovery");
        if self.storage.facts.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        let first_new = self.storage.next_entry_id;
        let mut inserted = Vec::new();
        let mut indexed_checked = Vec::new();
        for fact in facts {
            // Check the new footprint against the maintained caller frame
            // before insertion, so the query never has to skip its own entry.
            let checked = match self.constant_owned_overlap(&fact, assumptions) {
                ConstantOwnedOverlap::Unsupported => false,
                ConstantOwnedOverlap::Clear => true,
                ConstantOwnedOverlap::Overlap(entry) => {
                    return OwnershipAdmission::Conflict(
                        ResourceContextValidityError::OverlappingOwnedMemoryResources {
                            left: self
                                .fact(entry)
                                .memory_own_range()
                                .expect("indexed owner")
                                .clone(),
                            right: fact.memory_own_range().expect("queried owner").clone(),
                        },
                    );
                }
            };
            let entry = self.storage.next_entry_id;
            self.insert_fact(fact.clone());
            inserted.push((fact, self.occurrence(entry)));
            indexed_checked.push(checked);
        }
        for right_entry in first_new..self.storage.next_entry_id {
            let right = self.fact(right_entry);
            if let Some(error) = self.exclusive_validity_error(right) {
                return OwnershipAdmission::Conflict(error);
            }
            if indexed_checked[(right_entry - first_new) as usize] {
                continue;
            }
            let Some(right_range) = right.memory_own_range() else {
                continue;
            };
            if constant_memory_coordinates(right_range).is_some_and(|(_, start, end)| start >= end)
            {
                continue;
            }
            return OwnershipAdmission::Unsupported(PendingOwnershipAdmission {
                context: self,
                inserted,
                indexed_checked,
                first_new,
                first_unresolved: right_entry,
                assumptions,
            });
        }
        self.advance_prepared_memory_equalities(assumptions);
        OwnershipAdmission::Admitted {
            context: self,
            inserted,
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/resource_algebra/ownership_admission.rs");
}
