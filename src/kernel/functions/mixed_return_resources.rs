//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

/// A checked call selected this input ownership component, directly or from
/// its finite projected frontier, to supply one returned footprint. This permits
/// moving custody back into its residual frame, never admitting an arbitrary description.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConsumedCellReturn {
    input: ResourceOccurrenceId,
}

/// Planned by source clause, then attached to the occurrence the evaluator
/// actually emits for that output clause. Each input clause is selected once.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct ConsumedCellReturns {
    frontier: Option<ResourceContext>,
    direct: BTreeMap<usize, ConsumedCellReturn>,
    children: BTreeMap<Vec<usize>, ConsumedCellReturn>,
    borrowed: BTreeMap<usize, ResourceOccurrenceId>,
    // Actual checked input footprints, bound once by the entry reservation.
    pub(super) constructed: BTreeMap<usize, ResourceFact>,
}

impl ConsumedCellReturns {
    // These are the finite ranges the checked entry transition already
    // projected, not ranges rediscovered from the returned descriptions.
    pub(super) fn retain_frontier(
        &mut self,
        ranges: impl IntoIterator<Item = MemoryRange>,
        assumptions: &PureFactContext,
    ) {
        self.frontier = Some(
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(
                ranges
                    .into_iter()
                    .map(|range| ResourceFact::own_memory(range.spatial_key())),
            ),
        );
    }

    pub(super) fn prepare(
        interface: &FunctionContractInterface,
        plan: &StableViewTransferPlan,
        caller: &ResourceContext,
    ) -> Self {
        let selected = plan
            .transferred_ownership
            .iter()
            .zip(&plan.transferred_ownership_sources)
            .filter_map(|(checked, source)| {
                let source = (*source)?;
                if checked.role != ResourceTransferRole::Consume
                    || caller
                        .owned_fact_for_occurrence(source)
                        .and_then(ResourceFact::memory_own_range)
                        .is_none()
                {
                    return None;
                }
                Some((checked.section_index?, (checked, source)))
            })
            .collect::<BTreeMap<_, _>>();
        let mut outputs = Self::default();
        let mut used = BTreeSet::new();
        for (&output, &input) in &interface.resource_transfer_rule.inputs_by_output {
            crate::instrumentation::record_deterministic_work(1);
            if let Some((checked, source)) = selected.get(&input) {
                outputs
                    .direct
                    .insert(output, ConsumedCellReturn { input: *source });
                outputs.constructed.insert(output, checked.fact.clone());
                used.insert(input);
            }
        }
        for (path, input) in &interface.resource_transfer_rule.inputs_by_child {
            crate::instrumentation::record_deterministic_work(1);
            if let Some((_, source)) = selected.get(input) {
                outputs
                    .children
                    .insert(path.clone(), ConsumedCellReturn { input: *source });
                used.insert(*input);
            }
        }
        let parameters = interface
            .parameters()
            .iter()
            .filter(|parameter| parameter.program_type().is_object_pointer())
            .map(|parameter| parameter.binding_name())
            .collect::<BTreeSet<_>>();
        let mut inputs = BTreeMap::<FixedMemoryKey, VecDeque<ConsumedCellReturn>>::new();
        let mut borrowed = BTreeMap::<BorrowedResourceKey, VecDeque<ResourceOccurrenceId>>::new();
        for (checked, source) in plan
            .transferred_ownership
            .iter()
            .zip(&plan.transferred_ownership_sources)
        {
            if checked
                .section_index
                .is_some_and(|index| used.contains(&index))
            {
                continue;
            }
            if !matches!(
                checked.role,
                ResourceTransferRole::Consume | ResourceTransferRole::Borrow
            ) {
                continue;
            }
            let Some(input) = checked
                .section_index
                .and_then(|index| interface.resource_requires().get(index))
            else {
                continue;
            };
            let Some(source) = source else { continue };
            let Some(owner) = caller.owned_fact_for_occurrence(*source) else {
                continue;
            };
            if checked.role == ResourceTransferRole::Borrow {
                // An entry-state return reuses the already evaluated input
                // clause itself. Its selected occurrence is the evidence;
                // its surface pointer spelling need not be a bare parameter.
                borrowed
                    .entry(borrowed_resource_key(input))
                    .or_default()
                    .push_back(*source);
                continue;
            }
            let Some(key) = fixed_memory_key(input, &parameters, checked.role) else {
                continue;
            };
            if owner.memory_own_range().is_none() {
                continue;
            }
            inputs
                .entry(key)
                .or_default()
                .push_back(ConsumedCellReturn { input: *source });
        }
        if inputs.is_empty() && borrowed.is_empty() {
            return outputs;
        }
        let bindings = parameters
            .iter()
            .map(|name| ((*name).clone(), (*name).clone()))
            .collect();
        for (index, output) in interface.resource_ensures().iter().enumerate() {
            if output.role() == ResourceTransferRole::Borrow
                && output.state_source() == ResourceStateSource::Entry
                && let Some(input) = borrowed
                    .get_mut(&borrowed_resource_key(output))
                    .and_then(VecDeque::pop_front)
            {
                outputs.borrowed.insert(index, input);
                continue;
            }
            if outputs.direct.contains_key(&index) {
                continue;
            }
            if output.role() != ResourceTransferRole::Produce
                || output.state_source() != ResourceStateSource::Post
                || output.guard().is_some()
            {
                continue;
            }
            outputs.plan_children(
                output,
                &bindings,
                &parameters,
                &mut vec![index],
                interface.composite_resource_definitions(),
                &mut inputs,
                &mut BTreeSet::new(),
            );
        }
        outputs
    }

    // The entry plan selects each input once. Bind definition formals to the
    // contract's literal parameter spelling here, before evaluating any output.
    // No evaluated pointer or alias class is used to discover a supplier.
    #[allow(clippy::too_many_arguments)]
    fn plan_children(
        &mut self,
        spec: &ResourceSpec,
        bindings: &BTreeMap<BindingName, BindingName>,
        parameters: &BTreeSet<&BindingName>,
        path: &mut Vec<usize>,
        definitions: &[CompositeResourceDefinition],
        inputs: &mut BTreeMap<FixedMemoryKey, VecDeque<ConsumedCellReturn>>,
        active: &mut BTreeSet<String>,
    ) {
        if self.children.contains_key(path) {
            return;
        }
        if spec.quantity() != &ResourceQuantity::One || spec.guard().is_some() {
            return;
        }
        if let Some(mut key) = fixed_memory_shape_without_parameter(spec) {
            let Some(parameter) = bindings.get(&key.0) else {
                return;
            };
            if !parameters.contains(parameter) {
                return;
            }
            key.0 = parameter.clone();
            if let Some(input) = inputs.get_mut(&key).and_then(VecDeque::pop_front) {
                if path.len() == 1 {
                    self.direct.insert(path[0], input);
                } else {
                    self.children.insert(path.clone(), input);
                }
            }
            return;
        }
        let term = match spec.term() {
            ResourceTerm::Instance { resource, .. } => resource.as_ref(),
            term => term,
        };
        let ResourceTerm::Composite {
            name, arguments, ..
        } = term
        else {
            return;
        };
        let Ok(index) = definitions.binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        }) else {
            return;
        };
        let definition = &definitions[index];
        if definition.is_recursive()
            || !definition.children.is_empty()
            || definition.matched.is_some()
            || !definition.witnesses.is_empty()
            || !active.insert(name.clone())
        {
            return;
        }
        let child_bindings = definition
            .parameters()
            .iter()
            .zip(arguments)
            .filter_map(|(parameter, argument)| {
                let ProgramExpression::Variable(argument) = argument else {
                    return None;
                };
                Some((
                    parameter.binding_name().clone(),
                    bindings.get(argument)?.clone(),
                ))
            })
            .collect();
        for (index, child) in definition.contains().iter().enumerate() {
            if child.is_view() {
                continue;
            }
            path.push(index);
            self.plan_children(
                child,
                &child_bindings,
                parameters,
                path,
                definitions,
                inputs,
                active,
            );
            path.pop();
        }
        active.remove(name);
    }

    pub(super) fn get(&self, clause: usize) -> Option<ConsumedCellReturn> {
        self.direct.get(&clause).copied()
    }
}

// Retain the bound's type as well as its literal value: byte-equivalent
// spellings and width conversions are not new transfer evidence.
type FixedMemoryKey = (BindingName, ProgramValue, ProgramValue, u32);

fn fixed_memory_key(
    spec: &ResourceSpec,
    parameters: &BTreeSet<&BindingName>,
    role: ResourceTransferRole,
) -> Option<FixedMemoryKey> {
    if spec.role() != role {
        return None;
    }
    fixed_memory_shape(spec, parameters)
}

fn fixed_memory_shape(
    spec: &ResourceSpec,
    parameters: &BTreeSet<&BindingName>,
) -> Option<FixedMemoryKey> {
    let key = fixed_memory_shape_without_parameter(spec)?;
    parameters.contains(&key.0).then_some(key)
}

fn fixed_memory_shape_without_parameter(spec: &ResourceSpec) -> Option<FixedMemoryKey> {
    let ResourceTerm::Memory(segment) = spec.term() else {
        return None;
    };
    let ProgramExpression::Variable(parameter) = &segment.base else {
        return None;
    };
    if spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || spec.guard().is_some()
        || segment.guard().is_some()
    {
        return None;
    }
    Some((
        parameter.clone(),
        fixed_memory_bound(&segment.start)?,
        fixed_memory_bound(&segment.end)?,
        segment.element_width(),
    ))
}

pub(super) fn fixed_memory_bound(expression: &ProgramExpression) -> Option<ProgramValue> {
    let ProgramExpression::Value(value) = expression else {
        return None;
    };
    match value {
        ProgramValue::Int32(bits32_constant!(_))
        | ProgramValue::Int64(int64_constant!(_))
        | ProgramValue::UInt64(uint64_constant!(_)) => Some(value.clone()),
        _ => None,
    }
}

/// Separation evidence from an actual allocation in this call's creator
/// scope. A contract allocation claim and a pending/retired allocation do not
/// establish this evidence. Body exit still checks actual returned custody.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FreshAllocationReturn {
    allocation: u64,
}

impl FreshAllocationReturn {
    pub(super) fn from_created_owner(
        fact: &ResourceFact,
        creator: &CreationEvents,
        events: &CreationEvents,
    ) -> Option<Self> {
        if fact.owned_quantity_term()?.as_const() != Some(1) {
            return None;
        }
        let base = fact
            .memory_own_range()
            .map(MemoryRange::base)
            .or_else(|| fact.allocation().map(|(base, _)| base))?;
        let AddressBase::Heap(allocation) = base.base else {
            return None;
        };
        events
            .storage_created_by(creator, &base.base)
            .then_some(Self { allocation })
    }
}

pub(in crate::kernel) struct ReturnedFreshAllocation {
    frame: ResourceContext,
    output: ResourceFact,
    source: ResourceOccurrenceId,
    fresh: FreshAllocationReturn,
}

impl ReturnedFreshAllocation {
    pub(in crate::kernel) fn into_parts(
        self,
    ) -> (ResourceContext, ResourceFact, ResourceOccurrenceId, u64) {
        (self.frame, self.output, self.source, self.fresh.allocation)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReturnOwnershipOrigin {
    Description,
    EntryBorrow,
    ConsumedCell(ConsumedCellReturn),
    FreshAllocation(FreshAllocationReturn),
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
    clause: Option<usize>,
}

pub(super) struct EvaluatedReturnResources {
    pub(super) resources: ResourceContext,
    pub(super) occurrences: Vec<EvaluatedReturnOccurrence>,
    // The unknown subset is itself a checked partition. Selected members of
    // the same checked call-input partition need only meet this new boundary.
    unclassified: ResourceContext,
    selected_inputs: BTreeSet<ResourceOccurrenceId>,
    checked_frontier: Option<ResourceContext>,
    body: Option<BodyReturnConstruction>,
}

/// Persistent custody left after the outputs already constructed. The frame
/// is captured by the executed call, not supplied by a later admission query.
struct BodyReturnConstruction {
    remaining: ResourceContext,
    frame: ResourceContext,
}

/// A group built by consuming the executed body's actual owners. The return
/// producer discharges composite-footprint obligations before installation;
/// installation never repeats consumption or raw group admission.
pub(in crate::kernel) struct ConstructedBodyReturn {
    frame: ResourceContext,
    outputs: ResourceContext,
}

impl ConstructedBodyReturn {
    pub(in crate::kernel) fn into_parts(self) -> (ResourceContext, ResourceContext) {
        (self.frame, self.outputs)
    }
}

/// One insertion's explicit source-to-destination relationship.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ReturnResourceTransfer {
    pub(in crate::kernel) source: ResourceOccurrenceId,
    pub(in crate::kernel) destination: ResourceOccurrenceId,
    pub(in crate::kernel) consumed_input: Option<ResourceOccurrenceId>,
    pub(in crate::kernel) fresh_allocation: Option<u64>,
}

pub(super) struct PreparedReturnComposition {
    retained: ResourceContext,
    pub(super) frame: ResourceContext,
    pub(super) pending: ResourceContext,
    pub(super) entry_borrow_outputs: ResourceContext,
    restored: BTreeMap<ResourceOccurrenceId, ReturnResourceTransfer>,
    pub(super) transferred_memory_outputs: ResourceContext,
    occurrences: Vec<EvaluatedReturnOccurrence>,
    body: Option<ConstructedBodyReturn>,
}

impl EvaluatedReturnResources {
    pub(super) fn new(assumptions: &PureFactContext) -> Self {
        Self {
            resources: ResourceContext::new_with_equalities(assumptions),
            occurrences: Vec::new(),
            unclassified: ResourceContext::new_with_equalities(assumptions),
            selected_inputs: BTreeSet::new(),
            checked_frontier: None,
            body: None,
        }
    }

    pub(super) fn for_composition(
        composition: ReturnResourceComposition<'_>,
        assumptions: &PureFactContext,
    ) -> Self {
        let mut output = Self::new(assumptions);
        output.checked_frontier = composition
            .consumed_children()
            .and_then(|plan| plan.frontier.clone());
        output.body = composition
            .body_return()
            .map(|(state, frame)| BodyReturnConstruction {
                remaining: state.resources().clone(),
                frame: frame.clone(),
            });
        output
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn construct_clause(
        mut self,
        fact: ResourceFact,
        origin: ReturnOwnershipOrigin,
        clause: Option<usize>,
        composition: ReturnResourceComposition<'_>,
        interface: &FunctionContractInterface,
        assumptions: &PureFactContext,
    ) -> Result<Self, RuntimeError> {
        let Some(body) = &mut self.body else {
            return self
                .admit_clause(
                    fact,
                    origin,
                    clause,
                    composition.consumed_children(),
                    assumptions,
                )
                .map_err(resource_context_runtime_error);
        };
        let (state, _) = composition
            .body_return()
            .expect("executed body construction");
        // A proof step can retain this same named authority in the captured
        // frame. Record its actual occurrence before consumption; equal
        // descriptions in independent contexts are not the same authority.
        let shared_instance = matches!(fact.resource(), Resource::Instance(_))
            .then(|| {
                body.remaining
                    .unique_owned_occurrence_for_fact(&fact)
                    .map(|(source, _)| source)
            })
            .flatten();
        body.remaining = consume_returned_resource_unit(
            body.remaining.clone(),
            &fact,
            state,
            interface,
            assumptions,
            &mut BTreeSet::new(),
        )
        .ok_or_else(|| {
            RuntimeError::FunctionContract(
                "function body does not yet establish its joint returned resource units".into(),
            )
        })?;
        if let Some(source) = shared_instance
            && body.frame.owned_fact_for_occurrence(source).is_some()
        {
            body.frame = body
                .frame
                .clone()
                .without_exact_representation_for_occurrence(source)
                .expect("captured shared instance occurrence");
        }
        let (resources, mut inserted) = self.resources.unchecked_with_facts_and_occurrences([fact]);
        self.resources = resources;
        self.occurrences.push(EvaluatedReturnOccurrence {
            source: inserted.pop().expect("one constructed return occurrence").1,
            origin,
            clause,
        });
        Ok(self)
    }

    /// Capture the occurrence returned by admission, while its origin is
    /// available. A deferred or unmatched description is never an entry borrow.
    #[cfg(test)]
    pub(super) fn admit(
        self,
        fact: ResourceFact,
        origin: ReturnOwnershipOrigin,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.admit_clause(fact, origin, None, None, assumptions)
    }

    pub(super) fn admit_clause(
        mut self,
        fact: ResourceFact,
        origin: ReturnOwnershipOrigin,
        clause: Option<usize>,
        input_partition: Option<&ConsumedCellReturns>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        let transferred = self
            .checked_frontier
            .as_mut()
            .and_then(|frontier| take_returned_footprint(frontier, &fact, assumptions));
        let origin = match (origin, transferred) {
            (ReturnOwnershipOrigin::ConsumedCell(_) | ReturnOwnershipOrigin::EntryBorrow, None)
                if self.checked_frontier.is_some() && fact.memory_own_range().is_some() =>
            {
                // A static recipe cannot reuse bytes already taken by a
                // dynamically selected output earlier in this partition.
                ReturnOwnershipOrigin::Description
            }
            (ReturnOwnershipOrigin::Description, Some(input)) => {
                ReturnOwnershipOrigin::ConsumedCell(input)
            }
            (origin, _) => origin,
        };
        let selected = clause
            .zip(input_partition)
            .and_then(|(clause, plan)| match origin {
                ReturnOwnershipOrigin::EntryBorrow => plan.borrowed.get(&clause).copied(),
                ReturnOwnershipOrigin::ConsumedCell(input)
                    if plan.direct.get(&clause) == Some(&input) =>
                {
                    Some(input.input)
                }
                _ => None,
            });
        let selected = selected.or_else(|| transferred.map(|input| input.input));
        let (resources, mut inserted) = if let Some(input) = selected {
            if !self.selected_inputs.insert(input) {
                return Err(ResourceContextValidityError::DuplicateOwnedResourceFact(
                    fact,
                ));
            }
            // The plan issued these distinct, fixed-footprint occurrences from
            // one checked input partition. Do not rediscover their pairwise
            // separation from the output pointer descriptions.
            ResourceContext::admit_returned_partition(
                ReturnedOwnershipPartition {
                    retained: self.unclassified.clone(),
                    frame: self.resources,
                    outputs: ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_fact(fact),
                },
                assumptions,
            )?
        } else {
            let (resources, inserted) = self
                .resources
                .try_compose_without_discovery_and_occurrences([fact.clone()], assumptions)?;
            self.unclassified = self.unclassified.unchecked_with_fact(fact);
            (resources, inserted)
        };
        let (_, source) = inserted.pop().expect("one admitted return occurrence");
        self.resources = resources;
        self.occurrences.push(EvaluatedReturnOccurrence {
            source,
            origin,
            clause,
        });
        Ok(self)
    }

    pub(super) fn restore_entry_borrows(
        &self,
        frame: ResourceContext,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
    ) -> Result<PreparedReturnComposition, ResourceContextValidityError> {
        if let Some(body) = &self.body {
            // Joint consumption established sibling separation. Only the
            // original captured caller frame is a new boundary.
            return Ok(PreparedReturnComposition {
                retained: body.frame.clone(),
                frame: body.frame.clone(),
                pending: ResourceContext::new_with_equalities(assumptions),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                transferred_memory_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: BTreeMap::new(),
                occurrences: self.occurrences.clone(),
                body: Some(ConstructedBodyReturn {
                    frame: body.frame.clone(),
                    outputs: self.resources.clone(),
                }),
            });
        }
        let occurrences = self
            .occurrences
            .iter()
            .map(|entry| EvaluatedReturnOccurrence {
                source: entry.source,
                clause: entry.clause,
                origin: match (composition, entry.origin) {
                    (ReturnResourceComposition::ValidateDescriptions, _) => {
                        ReturnOwnershipOrigin::Description
                    }
                    _ => entry.origin,
                },
            })
            .collect::<Vec<_>>();
        if occurrences
            .iter()
            .all(|entry| entry.origin == ReturnOwnershipOrigin::Description)
        {
            return Ok(PreparedReturnComposition {
                retained: frame.clone(),
                frame,
                pending: self.resources.clone(),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                transferred_memory_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: BTreeMap::new(),
                occurrences,
                body: None,
            });
        }
        let retained = frame.clone();
        let mut frame = frame;
        let mut borrowed = ResourceContext::new_with_equalities(assumptions);
        let mut borrowed_sources = Vec::new();
        let mut pending = ResourceContext::new_with_equalities(assumptions);
        let mut transferred_memory_outputs = ResourceContext::new_with_equalities(assumptions);
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
                    transferred_memory_outputs =
                        transferred_memory_outputs.unchecked_with_fact(fact.clone());
                }
                ReturnOwnershipOrigin::FreshAllocation(fresh) => {
                    let (next, transfer) = ResourceContext::return_fresh_allocation(
                        ReturnedFreshAllocation {
                            frame,
                            output: fact.clone(),
                            source: occurrence.source,
                            fresh,
                        },
                        assumptions,
                    );
                    frame = next;
                    restored.insert(occurrence.source, transfer);
                    transferred_memory_outputs =
                        transferred_memory_outputs.unchecked_with_fact(fact.clone());
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
                    fresh_allocation: None,
                },
            );
        }
        Ok(PreparedReturnComposition {
            retained,
            frame,
            pending,
            entry_borrow_outputs,
            transferred_memory_outputs,
            restored,
            occurrences,
            body: None,
        })
    }
}

/// Produced only from the checked output context or a subset of its occurrences.
/// The caller checks its boundary, never reconstructs its internal partition.
pub(in crate::kernel) struct ReturnedOwnershipPartition {
    retained: ResourceContext,
    frame: ResourceContext,
    outputs: ResourceContext,
}
impl ReturnedOwnershipPartition {
    pub(in crate::kernel) fn into_parts(
        self,
    ) -> (ResourceContext, ResourceContext, ResourceContext) {
        (self.retained, self.frame, self.outputs)
    }
}

impl PreparedReturnComposition {
    pub(super) fn finish(
        self,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<ReturnResourceTransfer>), ResourceContextValidityError> {
        if let Some(body) = self.body {
            let (frame, inserted) = ResourceContext::return_constructed_body(body, assumptions);
            let transfers = self
                .occurrences
                .into_iter()
                .zip(inserted)
                .map(|(source, (_, destination))| ReturnResourceTransfer {
                    source: source.source,
                    destination,
                    consumed_input: match source.origin {
                        ReturnOwnershipOrigin::ConsumedCell(consumed) => Some(consumed.input),
                        _ => None,
                    },
                    fresh_allocation: match source.origin {
                        ReturnOwnershipOrigin::FreshAllocation(fresh) => Some(fresh.allocation),
                        _ => None,
                    },
                })
                .collect();
            return Ok((frame, transfers));
        }
        // Description admission already established the pending group's
        // internal composition. Only its boundary with the restored frame
        // is missing; construct that successor without checking it twice.
        let (frame, inserted) = if self.pending.facts().is_empty() {
            (self.frame, Vec::new())
        } else {
            ResourceContext::admit_returned_partition(
                ReturnedOwnershipPartition {
                    retained: self.retained,
                    frame: self.frame,
                    outputs: self.pending,
                },
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
                        fresh_allocation: None,
                    }
                }
            })
            .collect();
        Ok((frame, occurrences))
    }
}

/// Ownership changes produced while opening one returned occurrence. Child
/// identities are allocated by the body evaluator, before normalization.
#[derive(Clone, Debug)]
struct CompositeChildTransfer {
    // Retained proof identities, not premises for a consumer to revalidate.
    #[allow(dead_code)]
    source: ResourceOccurrenceId,
    #[allow(dead_code)]
    parent: ResourceOccurrenceId,
    fact: ResourceFact,
    origin: ReturnOwnershipOrigin,
}

#[cfg_attr(test, derive(Default))]
pub(super) struct ConstructedReturnBodies(BTreeMap<ResourceOccurrenceId, ConstructedReturnBody>);

pub(super) struct ConstructedReturnBody {
    // Each binding belongs to the actual occurrence opened by the producer.
    // Projection and admission consume its expansion without rebinding it.
    #[allow(dead_code)]
    witnesses: BTreeMap<ResourceOccurrenceId, Vec<ProgramValue>>,
    #[allow(dead_code)]
    specialized: Option<specialized_returns::SpecializedReturnEvidence>,
    // Explicit cut points of this finite construction. A recursive child is
    // retained with its emitted identity, never followed through memory.
    #[allow(dead_code)]
    folded: Vec<(ResourceFact, ResourceOccurrenceId)>,
    pub(super) frontier: Vec<ResourceFact>,
    viewed_children: Vec<(ResourceFact, ResourceOccurrenceId)>,
    expansion: Vec<ResourceFact>,
    // Only these descriptions still need a new separation argument. The
    // transfer producer has already established separation for the others.
    boundary: Vec<ResourceFact>,
    // Retain the ownership derivation; consumers use its constructed boundary,
    // rather than rewalking these premises to validate the producer again.
    #[allow(dead_code)]
    transfers: Vec<CompositeChildTransfer>,
}

impl ConstructedReturnBody {
    fn opaque(support: &ResourceFact, source: ResourceOccurrenceId) -> Self {
        Self {
            witnesses: BTreeMap::new(),
            specialized: None,
            folded: vec![(support.clone(), source)],
            frontier: Vec::new(),
            viewed_children: Vec::new(),
            expansion: vec![support.clone()],
            boundary: Vec::new(),
            transfers: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(in crate::kernel) fn owned_memory_frontier(&self) -> impl Iterator<Item = &ResourceFact> {
        self.boundary
            .iter()
            .filter(|piece| piece.memory_own_range().is_some())
    }

    pub(super) fn escrow_boundary(&self) -> Vec<ResourceFact> {
        self.boundary
            .iter()
            .cloned()
            .chain(
                self.folded
                    .iter()
                    .filter(|(fact, _)| fact.is_own())
                    .map(|(fact, _)| fact.clone()),
            )
            .collect()
    }

    pub(super) fn boundary(&self) -> &[ResourceFact] {
        &self.boundary
    }
}

/// Select one indexed finite input piece and consume that exact occurrence.
/// The supplier selector is singleton-only; a failed coverage check is final.
fn take_returned_footprint(
    frontier: &mut ResourceContext,
    fact: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<ConsumedCellReturn> {
    if fact.owned_quantity_term().and_then(MachineTerm::as_const) != Some(1) {
        return None;
    }
    // Custody concerns bytes. Keep the returned carrier metadata on the
    // output, rather than requiring the input's carrier to describe it.
    let footprint = ResourceFact::own_memory(fact.memory_own_range()?.spatial_key());
    let selected =
        frontier.directly_supporting_owned_entry_ignoring_separation(&footprint, assumptions);
    let (input, _) = selected?;
    let next = frontier.clone().without_selected_fact_with_origins(
        input,
        &footprint,
        assumptions,
        &mut MemorySplitOrigins::default(),
    )?;
    *frontier = next;
    Some(ConsumedCellReturn { input })
}

pub(super) struct ReturnFrontierAdmission {
    remaining: ResourceContext,
    outputs: ResourceContext,
    unclassified: ResourceContext,
    executed_body: bool,
    group: ResourceContext,
    group_unclassified: ResourceContext,
    deferred_flats: ResourceContext,
}

impl ReturnFrontierAdmission {
    fn finish_group(&mut self, assumptions: &PureFactContext) {
        self.outputs = self
            .outputs
            .clone()
            .unchecked_with_facts(self.group.facts().iter().cloned());
        self.unclassified = self
            .unclassified
            .clone()
            .unchecked_with_facts(self.group_unclassified.facts().iter().cloned());
        self.group = ResourceContext::new_with_equalities(assumptions);
        self.group_unclassified = ResourceContext::new_with_equalities(assumptions);
    }

    pub(super) fn admit(
        &mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Option<ConsumedCellReturn>> {
        // Joint consumption constructed this body's entire output partition;
        // its held heads certify their children, including sibling separation.
        if self.executed_body {
            return Some(None);
        }
        let mut transferred = take_returned_footprint(&mut self.remaining, fact, assumptions);
        let previous = if transferred.is_some() {
            &self.unclassified
        } else {
            &self.outputs
        };
        match previous.admit_returned_frontier(std::slice::from_ref(fact), assumptions) {
            FlatBodyAdmission::Admitted => {}
            FlatBodyAdmission::Conflict { held, .. }
                if self.deferred_flats.contains_exact_representation(&held) =>
            {
                // Finalization checks this leaf against every returned flat
                // clause and emits ProducedCompositeOverlapsHeldResource.
                transferred = None;
            }
            _ => return None,
        }
        // One selected returned head certifies its own separating body. Keep
        // supported conflict detection, but an unsupported internal geometry
        // does not invalidate that certificate. Cross-head/flat boundaries
        // above still require a bounded check, and consume input pieces once.
        self.group = match self
            .group
            .clone()
            .admit_without_discovery([fact.clone()], assumptions)
        {
            OwnershipAdmission::Admitted { context, .. } => context,
            OwnershipAdmission::Conflict(_) => return None,
            OwnershipAdmission::Unsupported(_) => {
                self.group.clone().unchecked_with_fact(fact.clone())
            }
        };
        if transferred.is_none() {
            self.group_unclassified = self
                .group_unclassified
                .clone()
                .unchecked_with_fact(fact.clone());
        }
        Some(transferred)
    }
}

impl ConstructedReturnBodies {
    #[cfg(test)]
    pub(super) fn construct(
        evaluated: &EvaluatedReturnResources,
        definitions: &[CompositeResourceDefinition],
        state: &ExecutionState,
        assumptions: &PureFactContext,
    ) -> Self {
        Self::try_construct(
            evaluated,
            definitions,
            state,
            ReturnResourceComposition::ValidateDescriptions,
            assumptions,
        )
        .expect("return body construction")
    }

    pub(super) fn try_construct(
        evaluated: &EvaluatedReturnResources,
        definitions: &[CompositeResourceDefinition],
        state: &ExecutionState,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let mut admission = if evaluated.body.is_some() {
            Some(ReturnFrontierAdmission {
                remaining: ResourceContext::new_with_equalities(assumptions),
                outputs: evaluated.resources.clone(),
                unclassified: evaluated.unclassified.clone(),
                executed_body: true,
                group: ResourceContext::new_with_equalities(assumptions),
                group_unclassified: ResourceContext::new_with_equalities(assumptions),
                deferred_flats: ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_facts(
                        evaluated
                            .resources
                            .facts()
                            .iter()
                            .filter(|fact| fact.memory_own_range().is_some())
                            .cloned(),
                    ),
            })
        } else {
            evaluated
                .checked_frontier
                .clone()
                .map(|remaining| ReturnFrontierAdmission {
                    remaining,
                    outputs: evaluated.resources.clone(),
                    unclassified: evaluated.unclassified.clone(),
                    executed_body: false,
                    group: ResourceContext::new_with_equalities(assumptions),
                    group_unclassified: ResourceContext::new_with_equalities(assumptions),
                    deferred_flats: ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_facts(
                            evaluated
                                .resources
                                .facts()
                                .iter()
                                .filter(|fact| fact.memory_own_range().is_some())
                                .cloned(),
                        ),
                })
        };
        let mut bodies = BTreeMap::new();
        let mut supported = BTreeMap::new();
        for occurrence in &evaluated.occurrences {
            let Some(support) = evaluated
                .resources
                .owned_fact_for_occurrence(occurrence.source)
            else {
                continue;
            };
            let name = match support.resource() {
                Resource::Composite { name, .. } => name.as_str(),
                Resource::Instance(instance) => instance.name(),
                _ => continue,
            };
            let definition = &definitions[definitions
                .binary_search_by(|definition| {
                    crate::instrumentation::record_deterministic_work(1);
                    definition.name().cmp(name)
                })
                .ok()?];
            if let Some(family) = specialized_returns::classify(support, definitions) {
                match specialized_returns::construct(
                    family,
                    support,
                    occurrence.source,
                    occurrence.clause,
                    definitions,
                    state,
                    composition,
                    occurrence.origin == ReturnOwnershipOrigin::EntryBorrow
                        && composition.restores_entry_borrows(),
                    assumptions,
                    admission.as_mut(),
                )? {
                    specialized_returns::Construction::Body(body) => {
                        bodies.insert(occurrence.source, *body);
                    }
                }
                if let Some(admission) = admission.as_mut() {
                    admission.finish_group(assumptions);
                }
                continue;
            }
            // Generic composite expansion never opened field-bearing
            // instances. Preserve that opacity with the actual instance and
            // its bindings, without reconstructing any child descriptions.
            if matches!(support.resource(), Resource::Instance(_)) {
                let mut body = ConstructedReturnBody::opaque(support, occurrence.source);
                if support.owned_quantity_term() == Some(&MachineTerm::constant(1))
                    && let Resource::Instance(instance) = support.resource()
                    && let Some(bounds) = opaque_boundary::construct(
                        instance,
                        definition,
                        definitions,
                        state,
                        assumptions,
                    )
                {
                    body.folded.clear();
                    for bound in bounds {
                        let transferred = match admission.as_mut() {
                            Some(admission) => admission.admit(&bound, assumptions)?,
                            None => None,
                        };
                        if transferred.is_none() {
                            body.boundary.push(bound);
                        }
                    }
                    if let Some(admission) = admission.as_mut() {
                        admission.finish_group(assumptions);
                    }
                } else if definition.matched.is_none()
                    && definition.contains().is_empty()
                    && definition.children.is_empty()
                {
                    // Logical fields alone do not hide owned memory. Keep
                    // their exact head in expansion, but introduce no unknown
                    // ownership cut point into escrow recovery.
                    body.folded.clear();
                }
                bodies.insert(occurrence.source, body);
                continue;
            }
            // A family outside the finite constructor fragment is a bounded
            // refusal, never permission to rediscover a body in a consumer.
            if !Self::supports(name, definitions, &mut supported, &mut BTreeSet::new()) {
                return None;
            }
            let borrowed = composition.restores_entry_borrows()
                && occurrence.origin == ReturnOwnershipOrigin::EntryBorrow;
            bodies.insert(
                occurrence.source,
                Self::build(
                    support,
                    occurrence.source,
                    definitions,
                    state,
                    composition,
                    assumptions,
                    &mut occurrence.clause.into_iter().collect(),
                    occurrence.clause.is_some(),
                    borrowed,
                    &mut admission,
                )?,
            );
            if let Some(admission) = admission.as_mut() {
                admission.finish_group(assumptions);
            }
        }
        Some(Self(bodies))
    }

    // Classify definitions before producing any body. Existential migration
    // retains pointer witness bindings and nested child occurrences. Its binder
    // examines only this definition, never held children.
    // Direct recursion emits a finite frontier and retains its child
    // folded. Non-pointer witnesses and named child schemas refuse here;
    // specialized authority/matched fragments have their own constructor.
    fn supports(
        name: &str,
        definitions: &[CompositeResourceDefinition],
        supported: &mut BTreeMap<String, bool>,
        active: &mut BTreeSet<String>,
    ) -> bool {
        if let Some(supported) = supported.get(name) {
            return *supported;
        }
        let Ok(index) = definitions.binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        }) else {
            return false;
        };
        let definition = &definitions[index];
        if !active.insert(name.to_string()) {
            return false;
        }
        let explicit_witnesses = definition.witnesses.iter().all(|witness| {
            crate::instrumentation::record_deterministic_work(1);
            witness.program_type().is_pointer()
        });
        let valid = definition.instance_schema.is_none()
            && definition.matched.is_none()
            && explicit_witnesses
            && definition.children.is_empty()
            && definition.contains().iter().all(|child| {
                crate::instrumentation::record_deterministic_work(1);
                if child.guard().is_some() {
                    return false;
                }
                match child.term() {
                    ResourceTerm::Memory(_)
                    | ResourceTerm::Token { .. }
                    | ResourceTerm::Iterated(_) => true,
                    ResourceTerm::Composite { name, .. } => {
                        child.quantity() == &ResourceQuantity::One
                            && ((name == definition.name() && definition.is_recursive())
                                || Self::supports(name, definitions, supported, active))
                    }
                    _ => false,
                }
            });
        active.remove(name);
        supported.insert(name.to_string(), valid);
        valid
    }

    #[allow(clippy::too_many_arguments)]
    fn build(
        support: &ResourceFact,
        source: ResourceOccurrenceId,
        definitions: &[CompositeResourceDefinition],
        state: &ExecutionState,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
        path: &mut Vec<usize>,
        planned: bool,
        borrowed: bool,
        admission: &mut Option<ReturnFrontierAdmission>,
    ) -> Option<ConstructedReturnBody> {
        let (singleton, inserted) = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_facts_and_occurrences([support.clone()]);
        let mut transfers = Vec::new();
        let mut witnesses = BTreeMap::new();
        let mut folded = Vec::new();
        let (context, frontier, viewed_children) = Self::open(
            singleton,
            support,
            inserted[0].1,
            source,
            definitions,
            state,
            composition,
            assumptions,
            path,
            planned,
            borrowed,
            &mut transfers,
            &mut witnesses,
            &mut folded,
            admission,
        )?;
        // Normalize descriptions only after the transfer producer has finished.
        // Source/parent identities remain the actual pre-normalization IDs.
        let normalize =
            |context: ResourceContext| context.normalized_without_discovery(assumptions);
        let boundary = normalize(
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(
                transfers
                    .iter()
                    .filter(|transfer| {
                        transfer.origin == ReturnOwnershipOrigin::Description
                            && !matches!(transfer.fact.resource(), Resource::Composite { .. })
                    })
                    .map(|transfer| transfer.fact.clone()),
            ),
        )
        .facts()
        .to_vec();
        let expansion = normalize(context).facts().to_vec();
        Some(ConstructedReturnBody {
            specialized: None,
            witnesses,
            folded,
            frontier,
            viewed_children,
            expansion,
            boundary,
            transfers,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn open(
        context: ResourceContext,
        support: &ResourceFact,
        selected: ResourceOccurrenceId,
        parent: ResourceOccurrenceId,
        definitions: &[CompositeResourceDefinition],
        state: &ExecutionState,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
        path: &mut Vec<usize>,
        planned: bool,
        borrowed: bool,
        transfers: &mut Vec<CompositeChildTransfer>,
        witnesses: &mut BTreeMap<ResourceOccurrenceId, Vec<ProgramValue>>,
        folded: &mut Vec<(ResourceFact, ResourceOccurrenceId)>,
        admission: &mut Option<ReturnFrontierAdmission>,
    ) -> Option<(
        ResourceContext,
        Vec<ResourceFact>,
        Vec<(ResourceFact, ResourceOccurrenceId)>,
    )> {
        let Resource::Composite { name, .. } = support.resource() else {
            return None;
        };
        let definition = &definitions[definitions
            .binary_search_by(|definition| {
                crate::instrumentation::record_deterministic_work(1);
                definition.name().cmp(name)
            })
            .ok()?];
        let body = construct_composite_resource_body(
            &context,
            support,
            definitions,
            &state.program_point(),
            assumptions,
            Some(selected),
            admission.as_mut(),
        )?;
        if !body.opened {
            folded.push((support.clone(), parent));
            return Some((body.expanded, Vec::new(), Vec::new()));
        }
        if !body.witnesses.is_empty() {
            let _checking = crate::instrumentation::CheckingWorkScope::new(
                "retain returned existential witness",
                body.witnesses.len(),
            );
            crate::instrumentation::record_deterministic_work(body.witnesses.len());
            witnesses.insert(parent, body.witnesses);
        }
        let parameters = definition
            .parameters()
            .iter()
            .map(ProgramParameter::binding_name)
            .collect::<BTreeSet<_>>();
        let mut context = body.expanded;
        let mut viewed_children = Vec::new();
        for (index, (fact, child_source)) in body.occurrences.into_iter().enumerate() {
            let spec = &definition.contains()[index];
            path.push(index);
            if fact.is_view() {
                viewed_children.push((fact.clone(), child_source));
            }
            let fixed_borrow = fact.is_own()
                && borrowed
                && summary_transfer::invariant_body_condition(definition, &parameters)
                && (fixed_memory_shape(spec, &parameters).is_some()
                    || summary_transfer::invariant_memory_shape(spec, &parameters));
            // A view remains a view even when its definition contains owns.
            // Neither its declaration nor a fresh backing block grants custody.
            let origin = if fact.is_view() {
                ReturnOwnershipOrigin::Description
            } else if let Some(Some(input)) = body.transferred.get(index) {
                ReturnOwnershipOrigin::ConsumedCell(*input)
            } else if admission
                .as_ref()
                .is_some_and(|admission| !admission.executed_body)
                && fact.memory_own_range().is_some()
            {
                ReturnOwnershipOrigin::Description
            } else if fixed_borrow {
                ReturnOwnershipOrigin::EntryBorrow
            } else if let Some(plan) = composition.consumed_children()
                && planned
                && fact.memory_own_range().is_some()
                && let Some(transfer) = plan.children.get(path)
            {
                ReturnOwnershipOrigin::ConsumedCell(*transfer)
            } else if let Some((creator, events)) = composition.allocation_events() {
                FreshAllocationReturn::from_created_owner(&fact, creator, events)
                    .map(ReturnOwnershipOrigin::FreshAllocation)
                    .unwrap_or(ReturnOwnershipOrigin::Description)
            } else {
                ReturnOwnershipOrigin::Description
            };
            transfers.push(CompositeChildTransfer {
                source: child_source,
                parent,
                fact: fact.clone(),
                origin,
            });
            if let Resource::Composite {
                name: child_name, ..
            } = fact.resource()
            {
                if child_name == name && definition.is_recursive() {
                    let _checking = crate::instrumentation::CheckingWorkScope::new(
                        "retain recursive return frontier",
                        1,
                    );
                    crate::instrumentation::record_deterministic_work(1);
                    folded.push((fact, child_source));
                    path.pop();
                    continue;
                }
                let invariant_arguments = match spec.term() {
                    ResourceTerm::Composite { arguments, .. } => {
                        arguments.iter().all(|argument| match argument {
                            ProgramExpression::Variable(name) => parameters.contains(name),
                            ProgramExpression::Value(_) => true,
                            _ => false,
                        })
                    }
                    _ => false,
                };
                (context, _, _) = Self::open(
                    context,
                    &fact,
                    child_source,
                    child_source,
                    definitions,
                    state,
                    composition,
                    assumptions,
                    path,
                    planned,
                    borrowed && invariant_arguments && fact.is_own(),
                    transfers,
                    witnesses,
                    folded,
                    admission,
                )?;
            }
            path.pop();
        }
        Some((context, body.children, viewed_children))
    }

    pub(super) fn for_return(
        &self,
        source: ResourceOccurrenceId,
        fact: &ResourceFact,
    ) -> Option<&ConstructedReturnBody> {
        let body = self.0.get(&source);
        assert!(
            !matches!(
                fact.resource(),
                Resource::Composite { .. } | Resource::Instance(_)
            ) || body.is_some(),
            "returned composite must carry its constructed or opaque body"
        );
        body
    }

    #[cfg(test)]
    pub(super) fn get(&self, source: ResourceOccurrenceId) -> Option<&ConstructedReturnBody> {
        self.0.get(&source)
    }
}

impl PreparedReturnComposition {
    pub(super) fn frontier_sources<'a>(
        &'a self,
        source: &'a ResourceContext,
        borrowed: bool,
    ) -> impl Iterator<Item = (ResourceOccurrenceId, &'a ResourceFact)> + 'a {
        self.occurrences.iter().filter_map(move |entry| {
            let selected = if self.body.is_some() {
                !borrowed
            } else if borrowed {
                entry.origin == ReturnOwnershipOrigin::EntryBorrow
            } else {
                entry.origin == ReturnOwnershipOrigin::Description
            };
            selected
                .then(|| {
                    source
                        .owned_fact_for_occurrence(entry.source)
                        .map(|fact| (entry.source, fact))
                })
                .flatten()
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ProducedBorrowingPiece {
    pub(super) support: super::super::loans::EscapingComposite,
    pub(super) piece: ResourceFact,
    // Actual child identities issued by the producer, retained as one group.
    #[allow(dead_code)]
    pub(super) sources: Arc<Vec<ResourceOccurrenceId>>,
}

pub(super) struct ProjectedReturnResource {
    pub(super) source: ResourceOccurrenceId,
    pub(super) support: ResourceFact,
    pub(super) destination: ResourceOccurrenceId,
    pub(super) expansion: Vec<ResourceFact>,
    pub(super) projected: Vec<ResourceFact>,
    pub(super) frontier: Vec<ResourceFact>,
    pub(super) viewed_children: Vec<(ResourceFact, ResourceOccurrenceId)>,
}

impl ProjectedReturnResource {
    pub(super) fn constructed_borrowing_pieces(&self) -> Vec<ProducedBorrowingPiece> {
        let children = &self.viewed_children;
        // Normalization may merge adjacent or equal views. Keep the producer's
        // raw identities as one shared group, alongside its normalized views;
        // do not recover an individual source by matching descriptions.
        let sources = Arc::new(
            children
                .iter()
                .map(|(_, source)| *source)
                .collect::<Vec<_>>(),
        );
        let support = super::super::loans::EscapingComposite {
            head: self.support.clone(),
            occurrence: self.destination,
        };
        self.frontier
            .iter()
            .filter(|piece| piece.is_view())
            .map(|piece| ProducedBorrowingPiece {
                support: support.clone(),
                piece: piece.clone(),
                sources: sources.clone(),
            })
            .collect()
    }
}

/// Read each owned output by its selected source identity. Equal descriptions
/// have independent transfers and never require an occurrence census or rank.
pub(super) fn project_return_resource_cores(
    source: &ResourceContext,
    transfers: &[ReturnResourceTransfer],
    bodies: &ConstructedReturnBodies,
    assumptions: &PureFactContext,
    destination: &ResourceContext,
) -> Vec<ProjectedReturnResource> {
    let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(assumptions);
    transfers
        .iter()
        .filter_map(|transfer| {
            source
                .owned_fact_for_occurrence(transfer.source)
                .map(|support| (support, transfer.source, transfer.destination))
        })
        .map(|(support, source_occurrence, destination_occurrence)| {
            let body = bodies.for_return(source_occurrence, support);
            // Family dispatch already produced the finite frontier and all
            // child identities. Projection cannot inspect definitions or memory.
            let frontier = body.map(|body| body.frontier.clone()).unwrap_or_default();
            let expansion = body
                .map(|body| body.expansion.clone())
                .unwrap_or_else(|| vec![support.clone()]);
            let projected = expansion
                .iter()
                .filter_map(|fact| fact.core_with_assumptions(assumptions))
                // Publish certified observations of this exact support. Suppress
                // only exact duplicates the destination already contains.
                .filter(|core| !destination.contains_exact_representation(core))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            ProjectedReturnResource {
                source: source_occurrence,
                support: support.clone(),
                destination: destination_occurrence,
                expansion,
                projected,
                viewed_children: body
                    .map(|body| body.viewed_children.clone())
                    .unwrap_or_default(),
                frontier,
            }
        })
        .collect()
}

#[cfg(test)]
mod composite_transfer_tests;
#[cfg(test)]
mod existential_return_tests;
#[cfg(test)]
mod fallback_inventory_tests;
#[cfg(test)]
mod fresh_allocation_tests;
#[cfg(test)]
mod recursive_return_tests;
#[cfg(test)]
mod specialized_return_tests;
#[cfg(test)]
mod summary_transfer_tests;
#[cfg(test)]
pub(super) mod tests;

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/mixed_return_resources.rs");
}

mod opaque_boundary;
mod specialized_returns;

/// The producer's new ownership boundary, indexed by the actual returned
/// occurrence. Already checked input transfers do not enter this delta.
#[derive(Default)]
pub(in crate::kernel) struct EscrowRecoveryBoundary {
    entries: Vec<(ResourceOccurrenceId, Vec<ResourceFact>)>,
}

impl EscrowRecoveryBoundary {
    pub(in crate::kernel) fn from_raw_outputs(
        outputs: impl IntoIterator<Item = (ResourceFact, ResourceOccurrenceId)>,
    ) -> Self {
        Self {
            entries: outputs
                .into_iter()
                .filter(|(fact, _)| fact.is_own())
                .map(|(fact, occurrence)| (occurrence, vec![fact]))
                .collect(),
        }
    }

    pub(super) fn record(
        &mut self,
        output: ResourceOccurrenceId,
        mut raw: Vec<ResourceFact>,
        body: Vec<ResourceFact>,
    ) {
        raw.extend(body);
        if !raw.is_empty() {
            self.entries.push((output, raw));
        }
    }

    pub(in crate::kernel) fn admit(
        &self,
        protected: &ResourceContext,
        opaque: bool,
        live: &ResourceContext,
        assumptions: &PureFactContext,
    ) -> Result<(), RuntimeError> {
        for (occurrence, frontier) in &self.entries {
            // Protocol reconciliation can remove an emitted authority.
            let Some(support) = live.owned_fact_for_occurrence(*occurrence) else {
                continue;
            };
            let opaque_output = frontier.iter().any(|fact| {
                fact.is_own()
                    && matches!(
                        fact.resource(),
                        Resource::Composite { .. }
                            | Resource::Instance(_)
                            | Resource::Footprint(_)
                            | Resource::Parameter(_)
                            | Resource::Star(_)
                            | Resource::Iterated(_)
                    )
            });
            if opaque_output && !protected.facts().is_empty() {
                return Err(resource_context_runtime_error(
                    ResourceContextValidityError::UnsupportedOwnershipBoundary,
                ));
            }
            if opaque
                && frontier.iter().any(|fact| {
                    fact.is_own()
                        && !matches!(fact.resource(), Resource::Token { .. } | Resource::Emp)
                })
            {
                return Err(resource_context_runtime_error(
                    ResourceContextValidityError::UnsupportedOwnershipBoundary,
                ));
            }
            match protected.admit_returned_frontier(frontier, assumptions) {
                FlatBodyAdmission::Admitted => {}
                FlatBodyAdmission::Unsupported => {
                    return Err(resource_context_runtime_error(
                        ResourceContextValidityError::UnsupportedOwnershipBoundary,
                    ));
                }
                FlatBodyAdmission::Conflict { piece, held } => {
                    if matches!(
                        support.resource(),
                        Resource::Composite { .. } | Resource::Instance(_)
                    ) {
                        return Err(RuntimeError::ProducedCompositeOverlapsHeldResource {
                            produced: Box::new(support.clone()),
                            piece,
                            held,
                        });
                    }
                    return Err(resource_context_runtime_error(
                        match (held.memory_own_range(), piece.memory_own_range()) {
                            (Some(left), Some(right)) => {
                                ResourceContextValidityError::OverlappingOwnedMemoryResources {
                                    left: left.clone(),
                                    right: right.clone(),
                                }
                            }
                            _ => ResourceContextValidityError::DuplicateOwnedResourceFact(*piece),
                        },
                    ));
                }
            }
        }
        Ok(())
    }
}
