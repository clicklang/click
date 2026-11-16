//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

/// A checked call consumed this selected flat owner and promises the same
/// scalar footprint on return. This is permission to move ownership back into
/// its residual frame, never permission to admit an arbitrary description.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConsumedCellReturn {
    input: ResourceOccurrenceId,
}

/// Planned by source clause, then attached to the occurrence the evaluator
/// actually emits for that output clause. Each input clause is selected once.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct ConsumedCellReturns(BTreeMap<usize, ConsumedCellReturn>);

impl ConsumedCellReturns {
    pub(super) fn prepare(
        interface: &FunctionContractInterface,
        plan: &StableViewTransferPlan,
        caller: &ResourceContext,
    ) -> Self {
        let parameters = interface
            .parameters()
            .iter()
            .filter(|parameter| parameter.program_type() == ProgramType::Int32Pointer)
            .map(|parameter| parameter.binding_name())
            .collect::<BTreeSet<_>>();
        let mut inputs = BTreeMap::<BindingName, VecDeque<ConsumedCellReturn>>::new();
        for (checked, source) in plan
            .transferred_ownership
            .iter()
            .zip(&plan.transferred_ownership_sources)
        {
            if checked.role != ResourceTransferRole::Consume {
                continue;
            }
            let Some(input) = checked
                .section_index
                .and_then(|index| interface.resource_requires().get(index))
            else {
                continue;
            };
            let Some(parameter) =
                scalar_parameter(input, &parameters, ResourceTransferRole::Consume)
            else {
                continue;
            };
            let Some(source) = source else { continue };
            // One indexed read excludes sources materialized from composites.
            // Reservation already proved coverage and separated the residual.
            if caller
                .owned_fact_for_occurrence(*source)
                .and_then(ResourceFact::memory_own_range)
                .is_none()
            {
                continue;
            }
            inputs
                .entry(parameter.clone())
                .or_default()
                .push_back(ConsumedCellReturn { input: *source });
        }
        let mut outputs = BTreeMap::new();
        for (index, output) in interface.resource_ensures().iter().enumerate() {
            let Some(parameter) =
                scalar_parameter(output, &parameters, ResourceTransferRole::Produce)
            else {
                continue;
            };
            if output.state_source() != ResourceStateSource::Post {
                continue;
            }
            if let Some(input) = inputs.get_mut(parameter).and_then(VecDeque::pop_front) {
                outputs.insert(index, input);
            }
        }
        Self(outputs)
    }

    pub(super) fn get(&self, clause: usize) -> Option<ConsumedCellReturn> {
        self.0.get(&clause).copied()
    }
}

fn scalar_parameter<'a>(
    spec: &'a ResourceSpec,
    parameters: &BTreeSet<&BindingName>,
    role: ResourceTransferRole,
) -> Option<&'a BindingName> {
    use crate::kernel::program_expression::int32_literal;
    let ResourceTerm::Memory(segment) = spec.term() else {
        return None;
    };
    let ProgramExpression::Variable(parameter) = &segment.base else {
        return None;
    };
    (spec.role() == role
        && spec.access() == ResourceAccessMode::Own
        && spec.quantity() == &ResourceQuantity::One
        && spec.guard().is_none()
        && segment.guard().is_none()
        && segment.start == int32_literal(0)
        && segment.end == int32_literal(1)
        && segment.element_width() == 4
        && parameters.contains(parameter))
    .then_some(parameter)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReturnOwnershipOrigin {
    Description,
    EntryBorrow,
    ConsumedCell(ConsumedCellReturn),
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
    pub(super) origin: ReturnOwnershipOrigin,
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
    restored: BTreeMap<ResourceOccurrenceId, ReturnResourceTransfer>,
    pub(super) consumed_cell_outputs: ResourceContext,
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
        origin: ReturnOwnershipOrigin,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        let (resources, mut inserted) = self
            .resources
            .try_compose_with_legacy_discovery_and_occurrences([fact], assumptions)?;
        let (_, source) = inserted.pop().expect("one admitted return occurrence");
        self.resources = resources;
        self.occurrences
            .push(EvaluatedReturnOccurrence { source, origin });
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
                origin: if matches!(composition, ReturnResourceComposition::ValidateDescriptions) {
                    ReturnOwnershipOrigin::Description
                } else {
                    entry.origin
                },
            })
            .collect::<Vec<_>>();
        if occurrences
            .iter()
            .all(|entry| entry.origin == ReturnOwnershipOrigin::Description)
        {
            return Ok(PreparedReturnComposition {
                frame,
                pending: self.resources.clone(),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                consumed_cell_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: BTreeMap::new(),
                occurrences,
            });
        }
        let mut frame = frame;
        let mut borrowed = ResourceContext::new_with_equalities(assumptions);
        let mut borrowed_sources = Vec::new();
        let mut pending = ResourceContext::new_with_equalities(assumptions);
        let mut consumed_cell_outputs = ResourceContext::new_with_equalities(assumptions);
        let mut restored = BTreeMap::new();
        for (fact, occurrence) in self.resources.facts().iter().zip(&occurrences) {
            match occurrence.origin {
                ReturnOwnershipOrigin::EntryBorrow => {
                    borrowed = borrowed.unchecked_with_fact(fact.clone());
                    borrowed_sources.push(occurrence.source);
                }
                ReturnOwnershipOrigin::ConsumedCell(consumed) => {
                    let (next, transfer) = ResourceContext::return_consumed_cell(
                        ReturnedConsumedCell {
                            frame,
                            output: fact.clone(),
                            source: occurrence.source,
                            consumed,
                        },
                        assumptions,
                    );
                    frame = next;
                    restored.insert(occurrence.source, transfer);
                    consumed_cell_outputs = consumed_cell_outputs.unchecked_with_fact(fact.clone());
                }
                ReturnOwnershipOrigin::Description => {
                    pending = pending.unchecked_with_fact(fact.clone());
                }
            }
        }
        let entry_borrow_outputs = borrowed.clone();
        let (frame, borrowed_insertions) = ResourceContext::restore_call_borrows(
            ReturnedCallBorrows {
                frame,
                outputs: borrowed,
            },
            assumptions,
        )?;
        for (source, (_, destination)) in borrowed_sources.into_iter().zip(borrowed_insertions) {
            restored.insert(
                source,
                ReturnResourceTransfer {
                    source,
                    destination,
                    consumed_input: None,
                },
            );
        }
        Ok(PreparedReturnComposition {
            frame,
            pending,
            entry_borrow_outputs,
            consumed_cell_outputs,
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
        // Restore by the producer's selected identity. Ordinary insertions
        // retain pending order, so this preserves actual emitted order even
        // when guards or deferred clauses changed it from declaration order.
        let mut restored = self.restored;
        let mut inserted = inserted.into_iter();
        let occurrences = self
            .occurrences
            .into_iter()
            .map(|source| {
                if source.origin != ReturnOwnershipOrigin::Description {
                    restored
                        .remove(&source.source)
                        .expect("restored return occurrence")
                } else {
                    let (_, destination) = inserted.next().expect("admitted output occurrence");
                    ReturnResourceTransfer {
                        source: source.source,
                        destination,
                        consumed_input: None,
                    }
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
