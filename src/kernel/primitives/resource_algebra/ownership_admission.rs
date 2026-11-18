//! Indexed resource admission. Unsupported coverage is returned, never searched.
use super::*;
use crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap;

/// A successor is available only after every new resource has been admitted.
#[must_use]
pub(crate) enum OwnershipAdmission {
    Admitted {
        context: ResourceContext,
        inserted: Vec<(ResourceFact, ResourceOccurrenceId)>,
    },
    Conflict(ResourceContextValidityError),
    /// No successor is published until this explicit boundary is established.
    Unsupported(Box<Proposition>),
}

/// The only new obligation for a constructed flat composite body is its
/// boundary with the retained caller frame. Unsupported geometry retains
/// an explicit separation goal; it never counts as established separation.
pub(crate) enum FlatBodyAdmission {
    Admitted,
    Conflict {
        piece: Box<ResourceFact>,
        held: Box<ResourceFact>,
    },
    Unestablished(Box<Proposition>),
    Unsupported,
}

impl ResourceContext {
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
    ) -> OwnershipAdmission {
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
    ) -> OwnershipAdmission {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("admit_without_discovery");
        if self.storage.facts.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        let mut inserted = Vec::new();
        for (fact, occurrence) in facts {
            match self.owned_boundary_overlap(&fact, assumptions) {
                ConstantOwnedOverlap::Unsupported => {
                    return OwnershipAdmission::Unsupported(
                        self.missing_ownership_boundary(&fact)
                            .expect("only an owned memory boundary can be unsupported"),
                    );
                }
                ConstantOwnedOverlap::Clear => {}
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
            }
            let entry = self.storage.next_entry_id;
            self.insert_fact_with_support_occurrence_and_metadata_at(
                fact.clone(),
                None,
                None,
                None,
                occurrence,
            );
            if let Some(error) = self.exclusive_validity_error(&fact) {
                return OwnershipAdmission::Conflict(error);
            }
            inserted.push((fact, self.occurrence(entry)));
        }
        self.advance_prepared_memory_equalities(assumptions);
        OwnershipAdmission::Admitted {
            context: self,
            inserted,
        }
    }
}

impl ResourceContext {
    /// Construct a valid successor by bounded checks or return the exact
    /// missing separation premise. There is no automatic discovery fallback.
    pub(crate) fn try_compose_checked_ownership_and_occurrences(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        match self.admit_without_discovery(facts, assumptions) {
            OwnershipAdmission::Admitted { context, inserted } => Ok((context, inserted)),
            OwnershipAdmission::Conflict(error) => Err(error),
            OwnershipAdmission::Unsupported(required) => Err(
                ResourceContextValidityError::UnestablishedOwnedBoundary(required),
            ),
        }
    }
}

impl ResourceContext {
    /// Check a definition-checked frontier against an existing partition.
    /// Unsupported geometry returns its explicit separation requirement.
    pub(in crate::kernel) fn checked_frontier_boundary_conflict(
        &self,
        frontier: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Result<Option<(ResourceFact, ResourceFact)>, ResourceContextValidityError> {
        for piece in frontier {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entry) = self.exclusive_boundary_owner(piece) {
                return Ok(Some((piece.clone(), self.fact(entry).clone())));
            }
            let held = match self.owned_boundary_overlap(piece, assumptions) {
                ConstantOwnedOverlap::Clear => None,
                ConstantOwnedOverlap::Overlap(entry) => Some(self.fact(entry).clone()),
                ConstantOwnedOverlap::Unsupported => {
                    return Err(ResourceContextValidityError::UnestablishedOwnedBoundary(
                        self.missing_ownership_boundary(piece)
                            .expect("owned memory boundary"),
                    ));
                }
            };
            if let Some(held) = held {
                return Ok(Some((piece.clone(), held)));
            }
        }
        Ok(None)
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

impl ResourceContext {
    pub(in crate::kernel) fn admit_returned_frontier(
        &self,
        frontier: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> FlatBodyAdmission {
        match self.checked_frontier_boundary_conflict(frontier, assumptions) {
            Ok(None) => FlatBodyAdmission::Admitted,
            Ok(Some((piece, held))) => FlatBodyAdmission::Conflict {
                piece: Box::new(piece),
                held: Box::new(held),
            },
            Err(ResourceContextValidityError::UnestablishedOwnedBoundary(required)) => {
                FlatBodyAdmission::Unestablished(required)
            }
            Err(_) => FlatBodyAdmission::Unsupported,
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
            match retained.admit_returned_frontier(std::slice::from_ref(piece), assumptions) {
                FlatBodyAdmission::Admitted => {}
                FlatBodyAdmission::Unestablished(required) => {
                    return Err(ResourceContextValidityError::UnestablishedOwnedBoundary(
                        required,
                    ));
                }
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
}
