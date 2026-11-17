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
/// boundary with the retained caller frame. Unsupported geometry is an
/// explicit bounded refusal; it never counts as established separation.
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
    /// A finite recursive body's folded child stays opaque; this query checks
    /// its explicitly exposed memory frontier and does not unfold that child.
    pub(in crate::kernel) fn admit_returned_flat_body(
        &self,
        body: &crate::kernel::functions::ConstructedReturnBody,
        assumptions: &PureFactContext,
    ) -> FlatBodyAdmission {
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("returned flat body admission");
        self.admit_returned_frontier(body.boundary(), assumptions)
    }

    /// Check just the boundary against this retained partition. This operation
    /// does not insert the frontier or compare its already checked leaves.
    pub(in crate::kernel) fn admit_returned_frontier(
        &self,
        frontier: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> FlatBodyAdmission {
        for piece in frontier {
            let _checking =
                crate::instrumentation::CheckingWorkScope::new("admit returned ownership leaf", 1);
            crate::instrumentation::record_deterministic_work(1);
            match self.admit_ownership_boundary(piece, assumptions) {
                FlatBodyAdmission::Admitted => {}
                refusal => return refusal,
            }
        }
        FlatBodyAdmission::Admitted
    }

    fn admit_ownership_boundary(
        &self,
        piece: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> FlatBodyAdmission {
        if let Some(entry) = self.exclusive_boundary_owner(piece) {
            return FlatBodyAdmission::Conflict {
                piece: Box::new(piece.clone()),
                held: Box::new(self.fact(entry).clone()),
            };
        }
        if piece.memory_own_range().is_none() {
            return FlatBodyAdmission::Admitted;
        }
        match self.constant_owned_overlap(piece, assumptions) {
            ConstantOwnedOverlap::Clear => FlatBodyAdmission::Admitted,
            ConstantOwnedOverlap::Overlap(entry) => FlatBodyAdmission::Conflict {
                piece: Box::new(piece.clone()),
                held: Box::new(self.fact(entry).clone()),
            },
            ConstantOwnedOverlap::Unsupported => FlatBodyAdmission::Unsupported,
        }
    }

    /// Construct a valid output partition using bounded indexed admission.
    pub(in crate::kernel) fn try_compose_without_discovery_and_occurrences(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        match self.admit_without_discovery(facts, assumptions) {
            OwnershipAdmission::Admitted { context, inserted } => Ok((context, inserted)),
            OwnershipAdmission::Conflict(error) => Err(error),
            OwnershipAdmission::Unsupported(_) => {
                Err(ResourceContextValidityError::UnsupportedOwnershipBoundary)
            }
        }
    }

    /// Consume the producer's partition. Only relationships with the original
    /// frame are new; checking against progressively inserted outputs would
    /// unnecessarily replay their internal separation obligations.
    pub(in crate::kernel) fn admit_returned_partition(
        transfer: crate::kernel::functions::ReturnedOwnershipPartition,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("returned output partition");
        let (retained, mut frame, outputs) = transfer.into_parts();
        if frame.storage.facts.is_empty() {
            frame.synchronize_memory_equalities(assumptions);
        }
        for piece in outputs.facts() {
            let _checking =
                crate::instrumentation::CheckingWorkScope::new("returned output boundary", 1);
            crate::instrumentation::record_deterministic_work(1);
            match retained.admit_ownership_boundary(piece, assumptions) {
                FlatBodyAdmission::Admitted => {}
                FlatBodyAdmission::Unsupported => {
                    return Err(ResourceContextValidityError::UnsupportedOwnershipBoundary);
                }
                FlatBodyAdmission::Conflict { piece, held } => {
                    return Err(match (held.memory_own_range(), piece.memory_own_range()) {
                        (Some(left), Some(right)) => {
                            ResourceContextValidityError::OverlappingOwnedMemoryResources {
                                left: left.clone(),
                                right: right.clone(),
                            }
                        }
                        _ => ResourceContextValidityError::DuplicateOwnedResourceFact(*piece),
                    });
                }
            }
        }
        let mut inserted = Vec::with_capacity(outputs.facts().len());
        for fact in outputs.facts() {
            let entry = frame.storage.next_entry_id;
            frame.insert_fact(fact.clone());
            inserted.push((fact.clone(), frame.occurrence(entry)));
        }
        frame.advance_prepared_memory_equalities(assumptions);
        Ok((frame, inserted))
    }

    /// Select one retained exclusive owner by the explicit resource identity.
    pub(super) fn exclusive_boundary_owner(&self, piece: &ResourceFact) -> Option<ResourceEntryId> {
        let entries = match piece.resource() {
            Resource::Instance(instance) => self.storage.index.instances.get(&instance.identity),
            Resource::PopulationAuthority(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_) => self.storage.index.by_resource.get(piece.resource()),
            _ => None,
        }?;
        entries.iter().next().copied()
    }

    /// Admit explicit resources using maintained indexes only. This operation
    /// never invokes discovery when the index cannot decide an overlap.
    pub(crate) fn admit_without_discovery(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> OwnershipAdmission<'_> {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("admit_without_discovery");
        self.admit_selected_occurrences_without_discovery(
            facts.into_iter().map(|fact| (fact, None)),
            assumptions,
        )
    }

    /// Build the admitted successor with the producer's selected identities.
    /// No temporary successor is checked and discarded before publication.
    pub(super) fn admit_selected_occurrences_without_discovery(
        mut self,
        facts: impl IntoIterator<Item = (ResourceFact, Option<ResourceOccurrenceId>)>,
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
        for (fact, occurrence) in facts {
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
            self.insert_fact_with_support_occurrence_and_metadata_at(
                fact.clone(),
                None,
                None,
                None,
                occurrence,
            );
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

impl ResourceContext {
    /// Apply a checked loan's restoration recipe. Old separation comes from
    /// the entry partition and the ledger; return-delta checks happen once at
    /// the recovery boundary, never by re-admitting this old footprint.
    pub(in crate::kernel) fn restore_checked_escrow(
        mut self,
        member: &crate::kernel::loans::RecoveredEscrow,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("restore checked escrow");
        if self
            .storage
            .entry_by_occurrence
            .contains_key(&member.occurrence())
        {
            return Err(ResourceContextValidityError::DuplicateOwnedResourceFact(
                member.fact().clone(),
            ));
        }
        if self.storage.facts.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        self.insert_fact_with_support_occurrence_and_metadata_at(
            member.fact().clone(),
            None,
            None,
            None,
            Some(member.occurrence()),
        );
        if let Some(binding) = member.binding() {
            self = self.with_loan_dependency(member.occurrence(), binding.clone());
        }
        self.advance_prepared_memory_equalities(assumptions);
        Ok(self)
    }
}

impl ResourceContext {
    /// Select only newly changed owned occurrences from the retained parent
    /// lineage. Persistent differences skip shared frame/history nodes.
    pub(in crate::kernel) fn new_owned_occurrences_from(
        &self,
        before: &Self,
    ) -> Option<Vec<(ResourceFact, ResourceOccurrenceId)>> {
        if !std::sync::Arc::ptr_eq(&self.storage.origin, &before.storage.origin) {
            return None;
        }
        Some(
            before
                .storage
                .facts
                .diff(&self.storage.facts)
                .filter_map(|(entry, _, new)| {
                    crate::instrumentation::record_deterministic_work(1);
                    let fact = new?;
                    let occurrence = self.occurrence(*entry);
                    if before.owned_fact_for_occurrence(occurrence) == Some(fact) {
                        return None;
                    }
                    fact.is_own().then(|| (fact.clone(), occurrence))
                })
                .collect(),
        )
    }
}
