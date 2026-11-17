//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

/// A checked call consumed this selected flat owner and promises the same
/// fixed footprint on return. This is permission to move ownership back into
/// its residual frame, never permission to admit an arbitrary description.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConsumedCellReturn {
    input: ResourceOccurrenceId,
}

/// Planned by source clause, then attached to the occurrence the evaluator
/// actually emits for that output clause. Each input clause is selected once.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct ConsumedCellReturns {
    direct: BTreeMap<usize, ConsumedCellReturn>,
    children: BTreeMap<Vec<usize>, ConsumedCellReturn>,
    borrowed: BTreeMap<usize, ResourceOccurrenceId>,
    // Actual checked input footprints, bound once by the entry reservation.
    pub(super) constructed: BTreeMap<usize, ResourceFact>,
}

impl ConsumedCellReturns {
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
        let PointerBlock::Heap(allocation) = base.block else {
            return None;
        };
        events
            .storage_created_by(creator, &base.block)
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
            body: None,
        }
    }

    pub(super) fn for_composition(
        composition: ReturnResourceComposition<'_>,
        assumptions: &PureFactContext,
    ) -> Self {
        let mut output = Self::new(assumptions);
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

    /// Capture the occurrence returned by admission, while its provenance is
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
            // A folded head may read post-call memory. Preserve its existing
            // boundary rule against the caller frame and the flat siblings
            // constructed in this return, without readmitting those siblings.
            let has_heads = self.resources.iter().any(|fact| {
                matches!(
                    fact.resource(),
                    Resource::Composite { .. } | Resource::Instance(_)
                )
            });
            let frontier_frame = if has_heads {
                body.frame.clone().unchecked_with_facts(
                    self.resources
                        .iter()
                        .filter(|fact| {
                            !matches!(
                                fact.resource(),
                                Resource::Composite { .. } | Resource::Instance(_)
                            )
                        })
                        .cloned(),
                )
            } else {
                body.frame.clone()
            };
            return Ok(PreparedReturnComposition {
                retained: body.frame.clone(),
                frame: frontier_frame,
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
pub(super) struct ConstructedReturnBodies(
    BTreeMap<ResourceOccurrenceId, ConstructedReturnBody>,
    BTreeSet<ResourceOccurrenceId>,
);

pub(in crate::kernel) struct ConstructedReturnBody {
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

    pub(in crate::kernel) fn boundary(&self) -> &[ResourceFact] {
        &self.boundary
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
        let mut bodies = BTreeMap::new();
        let mut legacy = BTreeSet::new();
        let mut supported = BTreeMap::new();
        for occurrence in &evaluated.occurrences {
            let Some(support) = evaluated
                .resources
                .owned_fact_for_occurrence(occurrence.source)
            else {
                continue;
            };
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
                )? {
                    specialized_returns::Construction::Body(body) => {
                        bodies.insert(occurrence.source, *body);
                    }
                }
                continue;
            }
            if matches!(support.resource(), Resource::Instance(_)) {
                legacy.insert(occurrence.source);
                continue;
            }
            let Resource::Composite { name, .. } = support.resource() else {
                continue;
            };
            if support.owned_quantity_term() != Some(&MachineTerm::constant(1))
                || !Self::supports(name, definitions, &mut supported, &mut BTreeSet::new())
            {
                legacy.insert(occurrence.source);
                continue;
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
                )?,
            );
        }
        Some(Self(bodies, legacy))
    }

    // Classify definitions before producing any body. Existential migration
    // retains pointer witness bindings and nested child occurrences. Its binder
    // examines only this definition, never held children.
    // Guarded direct recursion emits a finite frontier and retains its child
    // folded. Non-pointer witnesses and named child schemas stay legacy;
    // specialized authority/matched fragments have their own classifier.
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
            && (!definition.is_recursive() || definition.condition.is_some())
            && explicit_witnesses
            && definition.children.is_empty()
            && definition.contains().iter().all(|child| {
                crate::instrumentation::record_deterministic_work(1);
                if child.guard().is_some() {
                    return false;
                }
                match child.term() {
                    ResourceTerm::Memory(_) | ResourceTerm::Token { .. } => true,
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
                && (fixed_memory_shape(spec, &parameters).is_some()
                    || definition.condition.is_none()
                        && summary_transfer::invariant_memory_shape(spec, &parameters));
            // A view remains a view even when its definition contains owns.
            // Neither its declaration nor a fresh backing block grants custody.
            let origin = if fact.is_view() {
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
            ) || body.is_some()
                || self.1.contains(&source),
            "returned composite must carry its construction or an explicit legacy route"
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
    // Legacy one-level expansion has no occurrence record. Constructed bodies
    // always carry the actual child identity, never a description-based rank.
    #[allow(dead_code)]
    pub(super) sources: Option<Arc<Vec<ResourceOccurrenceId>>>,
}

pub(super) struct ProjectedReturnResource {
    pub(super) source: ResourceOccurrenceId,
    pub(super) support: ResourceFact,
    pub(super) destination: ResourceOccurrenceId,
    pub(super) expansion: Vec<ResourceFact>,
    pub(super) projected: Vec<ResourceFact>,
    pub(super) frontier: Vec<ResourceFact>,
    pub(super) viewed_children: Option<Vec<(ResourceFact, ResourceOccurrenceId)>>,
}

impl ProjectedReturnResource {
    pub(super) fn constructed_borrowing_pieces(&self) -> Option<Vec<ProducedBorrowingPiece>> {
        let children = self.viewed_children.as_ref()?;
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
        Some(
            self.frontier
                .iter()
                .filter(|piece| piece.is_view())
                .map(|piece| ProducedBorrowingPiece {
                    support: support.clone(),
                    piece: piece.clone(),
                    sources: Some(sources.clone()),
                })
                .collect(),
        )
    }
}

/// Read each owned output by its selected source identity. Equal descriptions
/// have independent transfers and never require an occurrence census or rank.
#[allow(clippy::too_many_arguments)]
pub(super) fn project_return_resource_cores(
    source: &ResourceContext,
    transfers: &[ReturnResourceTransfer],
    bodies: &ConstructedReturnBodies,
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
                .map(|support| (support, transfer.source, transfer.destination))
        })
        .map(|(support, source_occurrence, destination_occurrence)| {
            let body = bodies.for_return(source_occurrence, support);
            // Every projection carries its finite one-level frontier. Legacy
            // families construct it here; loan recovery never reconstructs it.
            let frontier = if let Some(body) = body {
                body.frontier.clone()
            } else if matches!(support.resource(), Resource::Composite { .. }) {
                expand_composite_resource_fact_with_children(
                    &ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_fact(support.clone()),
                    support,
                    definitions,
                    &post_state.program_point(),
                    assumptions,
                )
                .map(|(_, children, _)| children)
                .unwrap_or_default()
            } else {
                Vec::new()
            };
            let expansion = if let Some(body) = body {
                body.expansion.clone()
            } else if matches!(
                support.resource(),
                Resource::Memory(_) | Resource::Token { .. }
            ) {
                vec![support.clone()]
            } else {
                let singleton = ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(support.clone());
                let projection_state = post_state.clone().with_resource_context(singleton.clone());
                let expanded = expand_all_composite_resource_facts_at_state(
                    &singleton,
                    definitions,
                    &projection_state,
                    assumptions,
                )?;
                expanded.facts().to_vec()
            };
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
                source: source_occurrence,
                support: support.clone(),
                destination: destination_occurrence,
                expansion,
                projected,
                viewed_children: body.map(|body| body.viewed_children.clone()),
                frontier,
            })
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
