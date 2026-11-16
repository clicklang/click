//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

/// A checked call consumed this selected flat owner and promises the same
/// scalar footprint on return. This is permission to move ownership back into
/// its residual frame, never permission to admit an arbitrary description.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConsumedCellReturn {
    input: ResourceOccurrenceId,
}

impl ConsumedCellReturn {
    pub(super) fn prepare(
        interface: &FunctionContractInterface,
        plan: &StableViewTransferPlan,
        caller: &ResourceContext,
    ) -> Option<Self> {
        use crate::kernel::program_expression::int32_literal;
        let [input] = interface.resource_requires() else {
            return None;
        };
        let [output] = interface.resource_ensures() else {
            return None;
        };
        let [parameter] = interface.parameters() else {
            return None;
        };
        let [checked] = plan.transferred_ownership.as_slice() else {
            return None;
        };
        let [(_, occurrence)] = plan.reserved_ownership_supports.as_slice() else {
            return None;
        };
        let (ResourceTerm::Memory(before), ResourceTerm::Memory(after)) =
            (input.term(), output.term())
        else {
            return None;
        };
        if input.role() != ResourceTransferRole::Consume
            || output.role() != ResourceTransferRole::Produce
            || checked.role != ResourceTransferRole::Consume
            || checked.section_index != Some(0)
            || input.access() != ResourceAccessMode::Own
            || output.access() != ResourceAccessMode::Own
            || input.quantity() != &ResourceQuantity::One
            || output.quantity() != &ResourceQuantity::One
            || input.guard().is_some()
            || output.guard().is_some()
            || before.guard().is_some()
            || after.guard().is_some()
            || output.state_source() != ResourceStateSource::Post
            || parameter.program_type() != ProgramType::Int32Pointer
            || before.base != ProgramExpression::Variable(parameter.name().into())
            || after.base != before.base
            || before.start != int32_literal(0)
            || after.start != before.start
            || before.end != int32_literal(1)
            || after.end != before.end
            || before.element_width() != 4
            || after.element_width() != 4
        {
            return None;
        }
        // One indexed read excludes ownership materialized from a composite.
        // Reservation already checked coverage and separated the residual;
        // neither pointer aliases nor the retained frame are inspected here.
        caller
            .owned_fact_for_occurrence(*occurrence)?
            .memory_own_range()?;
        Some(Self { input: *occurrence })
    }
}

pub(in crate::kernel) struct ReturnedConsumedCell {
    frame: ResourceContext,
    output: ResourceFact,
    source: ResourceOccurrenceId,
    consumed: ConsumedCellReturn,
}

impl ReturnedConsumedCell {
    pub(in crate::kernel) fn into_parts(
        self,
    ) -> (
        ResourceContext,
        ResourceFact,
        ResourceOccurrenceId,
        ResourceOccurrenceId,
    ) {
        (self.frame, self.output, self.source, self.consumed.input)
    }
}

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
pub(in crate::kernel) struct ReturnResourceTransfer {
    pub(in crate::kernel) source: ResourceOccurrenceId,
    pub(in crate::kernel) destination: ResourceOccurrenceId,
    pub(in crate::kernel) consumed_input: Option<ResourceOccurrenceId>,
}

pub(super) struct PreparedReturnComposition {
    pub(super) frame: ResourceContext,
    pub(super) pending: ResourceContext,
    pub(super) entry_borrow_outputs: ResourceContext,
    restored: Vec<(ResourceFact, ResourceOccurrenceId)>,
    consumed_cell: Option<ReturnResourceTransfer>,
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
        if let ReturnResourceComposition::RestoreConsumedCell(transfer) = composition {
            // The producer selected a single unguarded output and its consumed
            // entry support. No other output can overlap this transfer.
            let output = self.occurrences[0].source;
            let (frame, consumed_cell) = ResourceContext::return_consumed_cell(
                ReturnedConsumedCell {
                    frame,
                    output: self.resources.facts()[0].clone(),
                    source: output,
                    consumed: transfer,
                },
                assumptions,
            );
            return Ok(PreparedReturnComposition {
                frame,
                pending: ResourceContext::new_with_equalities(assumptions),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: Vec::new(),
                consumed_cell: Some(consumed_cell),
                occurrences: Vec::new(),
            });
        }
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
                consumed_cell: None,
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
            consumed_cell: None,
            occurrences,
        })
    }
}

impl PreparedReturnComposition {
    pub(super) fn finish(
        self,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<ReturnResourceTransfer>), ResourceContextValidityError> {
        if let Some(transfer) = self.consumed_cell {
            return Ok((self.frame, vec![transfer]));
        }
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
                    consumed_input: None,
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
