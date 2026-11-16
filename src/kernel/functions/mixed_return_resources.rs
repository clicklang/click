//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

/// Identity captured by the producer of one evaluated return occurrence.
#[derive(Clone, Copy, Debug)]
pub(super) struct EvaluatedReturnOccurrence {
    pub(super) source: ResourceOccurrenceId,
    pub(super) entry_borrow: bool,
}

pub(super) struct EvaluatedReturnResources {
    pub(super) resources: ResourceContext,
    pub(super) occurrences: Vec<EvaluatedReturnOccurrence>,
}

/// One insertion's explicit source-to-destination relationship.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReturnResourceTransfer {
    pub(super) source: ResourceOccurrenceId,
    pub(super) destination: ResourceOccurrenceId,
}

pub(super) struct PreparedReturnComposition {
    pub(super) frame: ResourceContext,
    pub(super) pending: ResourceContext,
    pub(super) entry_borrow_outputs: ResourceContext,
    restored: Vec<(ResourceFact, ResourceOccurrenceId)>,
    occurrences: Vec<EvaluatedReturnOccurrence>,
}

impl EvaluatedReturnResources {
    pub(super) fn new(assumptions: &PureFactContext) -> Self {
        Self {
            resources: ResourceContext::new_with_equalities(assumptions),
            occurrences: Vec::new(),
        }
    }

    /// Capture the occurrence returned by admission, while its provenance is
    /// available. A deferred or unmatched description is never an entry borrow.
    pub(super) fn admit(
        mut self,
        fact: ResourceFact,
        entry_borrow: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        let (resources, mut inserted) = self
            .resources
            .try_compose_with_legacy_discovery_and_occurrences([fact], assumptions)?;
        let (_, source) = inserted.pop().expect("one admitted return occurrence");
        self.resources = resources;
        self.occurrences.push(EvaluatedReturnOccurrence {
            source,
            entry_borrow,
        });
        Ok(self)
    }

    pub(super) fn restore_entry_borrows(
        &self,
        frame: ResourceContext,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
    ) -> Result<PreparedReturnComposition, ResourceContextValidityError> {
        let occurrences = self
            .occurrences
            .iter()
            .map(|entry| EvaluatedReturnOccurrence {
                source: entry.source,
                entry_borrow: entry.entry_borrow
                    && matches!(composition, ReturnResourceComposition::RestoreEntryBorrows),
            })
            .collect::<Vec<_>>();
        if !occurrences.iter().any(|entry| entry.entry_borrow) {
            return Ok(PreparedReturnComposition {
                frame,
                pending: self.resources.clone(),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: Vec::new(),
                occurrences,
            });
        }
        let mut borrowed = ResourceContext::new_with_equalities(assumptions);
        let mut pending = ResourceContext::new_with_equalities(assumptions);
        for (fact, occurrence) in self.resources.facts().iter().zip(&occurrences) {
            if occurrence.entry_borrow {
                borrowed = borrowed.unchecked_with_fact(fact.clone());
            } else {
                pending = pending.unchecked_with_fact(fact.clone());
            }
        }
        let entry_borrow_outputs = borrowed.clone();
        let (frame, restored) = ResourceContext::restore_call_borrows(
            ReturnedCallBorrows {
                frame,
                outputs: borrowed,
            },
            assumptions,
        )?;
        Ok(PreparedReturnComposition {
            frame,
            pending,
            entry_borrow_outputs,
            restored,
            occurrences,
        })
    }
}

impl PreparedReturnComposition {
    pub(super) fn finish(
        self,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<ReturnResourceTransfer>), ResourceContextValidityError> {
        let (frame, inserted) = if self.pending.facts().is_empty() {
            (self.frame, Vec::new())
        } else {
            self.frame
                .try_compose_with_legacy_discovery_and_occurrences(
                    self.pending.facts().iter().cloned(),
                    assumptions,
                )?
        };
        // Both constructors retain one occurrence for each supplied fact.
        // Pair the original source identity with the insertion's destination,
        // retaining emitted order across the two partitions.
        let mut restored = self.restored.into_iter();
        let mut inserted = inserted.into_iter();
        let occurrences = self
            .occurrences
            .into_iter()
            .map(|source| {
                let (_, destination) = if source.entry_borrow {
                    restored.next().expect("restored entry occurrence")
                } else {
                    inserted.next().expect("admitted output occurrence")
                };
                ReturnResourceTransfer {
                    source: source.source,
                    destination,
                }
            })
            .collect();
        Ok((frame, occurrences))
    }
}

pub(super) struct ProjectedReturnResource {
    pub(super) support: ResourceFact,
    pub(super) destination: ResourceOccurrenceId,
    pub(super) expansion: Vec<ResourceFact>,
    pub(super) projected: Vec<ResourceFact>,
}

/// Read each owned output by its selected source identity. Equal descriptions
/// have independent transfers and never require an occurrence census or rank.
pub(super) fn project_return_resource_cores(
    source: &ResourceContext,
    transfers: &[ReturnResourceTransfer],
    definitions: &[CompositeResourceDefinition],
    post_state: &ExecutionState,
    assumptions: &PureFactContext,
    destination: &ResourceContext,
) -> Option<Vec<ProjectedReturnResource>> {
    let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(assumptions);
    transfers
        .iter()
        .filter_map(|transfer| {
            source
                .owned_fact_for_occurrence(transfer.source)
                .map(|support| (support, transfer.destination))
        })
        .map(|(support, destination_occurrence)| {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(support.clone());
            let projection_state = post_state.clone().with_resource_context(singleton.clone());
            let expanded = expand_all_composite_resource_facts_at_state(
                &singleton,
                definitions,
                &projection_state,
                assumptions,
            )?;
            let expansion = expanded.facts().to_vec();
            let projected = expansion
                .iter()
                .filter_map(|fact| fact.core_with_assumptions(assumptions))
                // Publish certified observations of this exact support. Suppress
                // only exact duplicates the destination already contains.
                .filter(|core| !destination.contains_exact_representation(core))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            Some(ProjectedReturnResource {
                support: support.clone(),
                destination: destination_occurrence,
                expansion,
                projected,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/mixed_return_resources.rs");
}
