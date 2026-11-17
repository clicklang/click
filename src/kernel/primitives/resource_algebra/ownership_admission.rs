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
        for piece in body.boundary() {
            let _checking =
                crate::instrumentation::CheckingWorkScope::new("admit returned ownership leaf", 1);
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entry) = self.exclusive_boundary_owner(piece) {
                return FlatBodyAdmission::Conflict {
                    piece: Box::new(piece.clone()),
                    held: Box::new(self.fact(entry).clone()),
                };
            }
            if piece.memory_own_range().is_none() {
                continue;
            }
            match self.owned_boundary_overlap(piece, assumptions) {
                ConstantOwnedOverlap::Clear => {}
                ConstantOwnedOverlap::Overlap(entry) => {
                    return FlatBodyAdmission::Conflict {
                        piece: Box::new(piece.clone()),
                        held: Box::new(self.fact(entry).clone()),
                    };
                }
                ConstantOwnedOverlap::Unsupported => {
                    return FlatBodyAdmission::Unestablished(
                        self.missing_ownership_boundary(piece)
                            .expect("owned memory boundary"),
                    );
                }
            }
        }
        FlatBodyAdmission::Admitted
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
    /// Check only the new boundary of an already constructed return body.
    /// Unsupported geometry returns its explicit separation requirement.
    pub(in crate::kernel) fn returned_boundary_conflict(
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
