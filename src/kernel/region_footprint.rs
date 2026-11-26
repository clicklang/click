//! Execution-produced region effects. References share the recorded collection;
//! constructing or selecting a region never reconstructs memory history.
use super::*;
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

static NEXT_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone)]
pub struct RegionFootprint {
    id: u64,
    pub(crate) source: String,
    pub(crate) before: SymbolicMemory,
    pub(crate) after: SymbolicMemory,
    pub(crate) before_point: ProgramPoint,
    pub(crate) after_point: ProgramPoint,
    pub(crate) before_resources: ResourceContext,
    pub(crate) after_resources: ResourceContext,
    pub(crate) members: imbl::Vector<Resource>,
    pub(crate) complete: bool,
    pub(crate) resource_bound: Option<Resource>,
    pub(crate) preserves_separate_viewability: bool,
    is_sequence: bool,
    ends_with_return: bool,
}
impl std::fmt::Debug for RegionFootprint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RegionFootprint").field(&self.id).finish()
    }
}
impl PartialEq for RegionFootprint {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for RegionFootprint {}
impl PartialOrd for RegionFootprint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for RegionFootprint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl std::hash::Hash for RegionFootprint {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.id.hash(h);
    }
}

impl RegionFootprint {
    pub(crate) fn transition(
        source: String,
        before: &ExecutionState,
        after: &ExecutionState,
        effects: &(impl ExecutionFactSource + ?Sized),
    ) -> Arc<Self> {
        Self::from_transition(source, before, after, effects, false, true, false)
    }

    pub(crate) fn statement_transition(
        source: String,
        statement: &ProgramStatement,
        before: &ExecutionState,
        after: &ExecutionState,
        effects: &(impl ExecutionFactSource + ?Sized),
    ) -> Arc<Self> {
        // Only a fresh uninitialized declaration creates storage without also
        // being able to retire an existing object. Re-entering a declaration
        // can retire the binding's previous local block.
        let uninitialized_local_declaration = matches!(
            statement,
            ProgramStatement::Declare {
                name,
                initializer: None,
                zero_fill: None,
                ..
            } if before.locals().slot(name).is_none_or(|slot| !slot.base.is_local_block())
        );
        Self::from_transition(
            source,
            before,
            after,
            effects,
            uninitialized_local_declaration,
            matches!(
                statement,
                ProgramStatement::Assign { .. } | ProgramStatement::Return(_)
            ),
            matches!(statement, ProgramStatement::Return(_)),
        )
    }

    fn from_transition(
        source: String,
        before: &ExecutionState,
        after: &ExecutionState,
        effects: &(impl ExecutionFactSource + ?Sized),
        uninitialized_local_declaration: bool,
        check_automatic_storage: bool,
        ends_with_return: bool,
    ) -> Arc<Self> {
        let mut members = imbl::Vector::new();
        let mut resource_bound = None;
        let mut bound_members = std::collections::BTreeSet::new();
        let mut effect_count = 0;
        let mut extra_effect = false;
        for fact in effects.fact_iter() {
            crate::instrumentation::record_deterministic_work(1);
            match fact.proposition() {
                Proposition::MemoryMutatesOnly { writes, .. } => {
                    extra_effect |= !writes.is_empty();
                    for (pointer, bytes) in writes {
                        members
                            .push_back(Resource::Memory(MemoryRange::of_access(pointer, *bytes)));
                    }
                }
                Proposition::MemoryEffectSummary { mutable_ranges, .. } => {
                    effect_count += 1;
                    resource_bound = fact.resource_effect_bound.as_deref().cloned();
                    if let Some(bound) = &resource_bound {
                        let mut pending = vec![bound];
                        while let Some(resource) = pending.pop() {
                            crate::instrumentation::record_deterministic_work(1);
                            match resource {
                                Resource::Star(pair) => {
                                    pending.push(&pair.0);
                                    pending.push(&pair.1);
                                }
                                other => {
                                    bound_members.insert(other.clone());
                                }
                            }
                        }
                    }
                    // Keep the recorded concrete projection for existing
                    // explicit memory framing. The abstract containment bound
                    // is a separate fact, not a replacement for these members.
                    members.extend(mutable_ranges.iter().cloned().map(Resource::Memory));
                }
                Proposition::HeapAllocationFreed {
                    allocation_base,
                    bytes,
                    ..
                } => {
                    extra_effect = true;
                    members.push_back(Resource::Memory(bytes.byte_range(allocation_base.clone())));
                }
                _ => {}
            }
        }
        // Storage creation and lifetime ending are effects too. The persistent
        // map diff visits changed paths, not the ambient block collection.
        for change in before.memory().blocks.diff(&after.memory().blocks) {
            crate::instrumentation::record_deterministic_work(1);
            let block = change.key();
            if block.is_havoc_block() || block.is_call_havoc_block() {
                continue;
            }
            for memory in [before.memory(), after.memory()] {
                if let Some(contents) = memory.blocks.get(block) {
                    // Zero-sized entries include execution bookkeeping markers;
                    // they name no program storage affected by the transition.
                    if contents.size().as_const() == Some(0) {
                        continue;
                    }
                    extra_effect = true;
                    members.push_back(Resource::Memory(
                        contents
                            .allocation_size()
                            .byte_range(Address::new(block.clone(), AddressOffset::constant(0))),
                    ));
                }
            }
        }
        let changed = after.resources().changed_facts_since(before.resources());
        let complete = changed.is_some();

        if let Some(changed) = changed {
            for fact in changed {
                crate::instrumentation::record_deterministic_work(1);
                if let ResourceFact::Own(resource, _) = &fact
                    && !matches!(resource, Resource::Memory(_) | Resource::Iterated(_))
                {
                    // A bounded call's produced output is new ownership made
                    // from its consumed inputs, not memory outside the bound.
                    let produced_output = resource_bound.is_some()
                        && after.resources().contains_exact_representation(&fact)
                        && !before.resources().contains_exact_representation(&fact);
                    // Spatial ownership may split or coalesce while a call
                    // lends and returns a cell; iterated ownership also updates
                    // its taken-out markers when a guard changes. Those map
                    // edits do not write bytes. Writes and lifetime effects are recorded
                    // above; retain changes to named resource observations.
                    // Lending and returning a recorded input is already
                    // included in the call's resource bound.
                    extra_effect |= !produced_output && !bound_members.contains(resource);
                    members.push_back(resource.clone());
                }
            }
        }
        if effect_count != 1 || extra_effect || !complete {
            resource_bound = None;
        }
        // Reuse the recorded effect members to certify an automatic-storage-only
        // transition. Heap retirement may be absent from a call's projected
        // writes, so a call summary or a changed retirement index refuses.
        let preserves_separate_viewability = complete
            && (uninitialized_local_declaration
                || (check_automatic_storage
                    && effect_count == 0
                    && before.memory().shares_heap_deallocations_with(after.memory())
                    && members.iter().all(|member| {
                        crate::instrumentation::record_deterministic_work(1);
                        matches!(member, Resource::Memory(range) if range.base().base.is_local_block())
                    })));
        Arc::new(Self {
            resource_bound,
            source,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            before: before.memory().clone(),
            after: after.memory().clone(),
            before_point: before.program_point(),
            after_point: after.program_point(),
            before_resources: before.resources().clone(),
            after_resources: after.resources().clone(),
            members,
            complete,
            preserves_separate_viewability,
            is_sequence: false,
            ends_with_return,
        })
    }

    /// Finish one statement's footprint with its automatic scope cleanup.
    /// Both deltas are supplied by the executing producer; this does not select
    /// or traverse earlier statements. Their effect descriptors are shared.
    pub(crate) fn with_scope_cleanup(statement: &Arc<Self>, cleanup: &Arc<Self>) -> Arc<Self> {
        let mut members = statement.members.clone();
        members.append(cleanup.members.clone());
        Arc::new(Self {
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            source: statement.source.clone(),
            before: statement.before.clone(),
            after: cleanup.after.clone(),
            before_point: statement.before_point.clone(),
            after_point: cleanup.after_point.clone(),
            before_resources: statement.before_resources.clone(),
            after_resources: cleanup.after_resources.clone(),
            members,
            complete: statement.complete && cleanup.complete,
            resource_bound: None,
            preserves_separate_viewability: statement.preserves_separate_viewability
                && cleanup.preserves_separate_viewability,
            is_sequence: false,
            ends_with_return: statement.ends_with_return,
        })
    }

    /// A return's published outcome can retire a local after the statement
    /// snapshot. Check that exact retirement edge and object, without walking
    /// earlier memory states or using an alias search.
    pub(crate) fn viewability_survives_return_cleanup(
        &self,
        outcome: &SymbolicMemory,
        selected: &Address,
    ) -> bool {
        if !self.ends_with_return || !self.preserves_separate_viewability {
            return false;
        }
        let Some(statement_exit) = interned_storage_of(&self.after) else {
            return false;
        };
        let retirement = interned_storage_of(outcome).and_then(|memory| memory.derivation());
        matches!(retirement.as_deref(), Some(MemoryDerivation::LocalLifetimeEnded { base, block })
            if base.arena_id() == statement_exit.arena_id() && selected.base.proven_distinct(block))
    }

    pub(crate) fn sequence(
        source: String,
        before: &ExecutionState,
        after: &ExecutionState,
        members: imbl::Vector<Resource>,
        complete: bool,
    ) -> Arc<Self> {
        Arc::new(Self {
            resource_bound: None,
            source,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            before: before.memory().clone(),
            after: after.memory().clone(),
            before_point: before.program_point(),
            after_point: after.program_point(),
            before_resources: before.resources().clone(),
            after_resources: after.resources().clone(),
            members,
            complete,
            preserves_separate_viewability: false,
            is_sequence: true,
            ends_with_return: false,
        })
    }

    /// Join two checked, single-write arms with the same effect. Matching
    /// endpoints prevents an arm's final statement from standing in for an
    /// earlier part of the branch. Resource-changing joins have no such
    /// footprint.
    pub(crate) fn shared_branch_write(
        source: String,
        before: &ExecutionState,
        after: &ExecutionState,
        arms: [(&ExecutionState, Option<&Arc<Self>>); 2],
    ) -> Option<Arc<Self>> {
        let [(left_exit, Some(left)), (right_exit, Some(right))] = arms else {
            return None;
        };
        crate::instrumentation::record_deterministic_work(1);
        let member = left.members.front()?;
        if !matches!(member, Resource::Memory(_))
            || !after.resources().shares_storage_with(before.resources())
            || !after
                .memory()
                .shares_heap_deallocations_with(before.memory())
        {
            return None;
        }
        for (exit, effect) in [(left_exit, left), (right_exit, right)] {
            if !effect.complete
                || effect.members.len() != 1
                || effect.members.front() != Some(member)
                || MemoryStateIdentity::of(&effect.before)
                    != MemoryStateIdentity::of(before.memory())
                || MemoryStateIdentity::of(&effect.after) != MemoryStateIdentity::of(exit.memory())
                || !effect
                    .before_resources
                    .shares_storage_with(before.resources())
                || !effect.after_resources.shares_storage_with(exit.resources())
                || !exit.resources().shares_storage_with(before.resources())
                || !exit
                    .memory()
                    .shares_heap_deallocations_with(before.memory())
            {
                return None;
            }
        }
        Some(Self::sequence(
            source,
            before,
            after,
            left.members.clone(),
            true,
        ))
    }
}

/// Establish collection separation from explicitly selected premises. Only the
/// named region's recorded members are visited; no execution history is read.
pub(crate) fn separate_using(left: &Resource, right: &Resource, facts: &PureFactContext) -> bool {
    separate_members(left, right, |fact| {
        byte_premise(fact).is_some_and(|bytes| facts.contains_known(&bytes))
    })
}

pub(crate) fn separate_members(
    left: &Resource,
    right: &Resource,
    available: impl Fn(&Proposition) -> bool,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    // Do not turn two effect collections into a Cartesian product.
    if matches!(
        (left, right),
        (Resource::Footprint(_), Resource::Footprint(_))
    ) {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        let empty = |resource: &Resource| {
            matches!(resource,
            Resource::Memory(range) if range.wide_bounds().is_none()
                && range.byte_footprint().1.as_const() == Some(0))
        };
        if empty(left) || empty(right) {
            continue;
        }
        match (left, right) {
            (Resource::Footprint(fp), other) | (other, Resource::Footprint(fp)) => {
                // A simple normalization never walks a region's execution
                // sequence. Longer transports spell each preservation edge.
                if !fp.complete || (fp.is_sequence && fp.members.len() > 1) {
                    return false;
                }
                pending.extend(fp.members.iter().map(|member| (member, other)));
            }
            // Primitive tokens contain no bytes. Releasing an allocation
            // still records its memory range separately above.
            (Resource::Token { .. }, Resource::Memory(_))
            | (Resource::Memory(_), Resource::Token { .. }) => {}
            (Resource::Memory(left), Resource::Memory(right))
                if left.base().blocks_proven_distinct(right.base())
                    // Distinct fields of one symbolic object, by its layout.
                    || crate::kernel::primitives::symbolic_ranges_disjoint(left, right) => {}
            _ if field_of_separate_object(left, right, &available)
                || field_of_separate_object(right, left, &available) => {}
            _ => {
                let forward = Proposition::ResourceSeparate {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let reverse = Proposition::ResourceSeparate {
                    left: Box::new(right.clone()),
                    right: Box::new(left.clone()),
                };
                if !available(&forward) && !available(&reverse) {
                    return false;
                }
            }
        }
    }
    true
}

/// Whether `field` is a whole field of a symbolic object known separate from
/// `other`: a field lies inside its object, so it is separate from what the
/// object is separate from.
fn field_of_separate_object(
    field: &Resource,
    other: &Resource,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let Resource::Memory(range) = field else {
        return false;
    };
    let Some((object, layout, _)) = range.symbolic_field() else {
        return false;
    };
    let object = Resource::Memory(
        MemoryRange::object(object, crate::kernel::LayoutSize::Of(layout)).with_carrier_of(range),
    );
    [
        Proposition::ResourceSeparate {
            left: Box::new(object.clone()),
            right: Box::new(other.clone()),
        },
        Proposition::ResourceSeparate {
            left: Box::new(other.clone()),
            right: Box::new(object),
        },
    ]
    .iter()
    .any(available)
}

/// Compare spatial resources in byte coordinates, independently of their C
/// element types. Unsupported wide intervals decline instead of narrowing.
pub(crate) fn byte_resource(resource: &Resource) -> Option<Resource> {
    match resource {
        // A whole symbolic object is already in bytes.
        Resource::Memory(range) if range.symbolic_object().is_some() => Some(resource.clone()),
        Resource::Memory(range) => {
            if range.wide_bounds().is_some() {
                return None;
            }
            let (base, bytes) = range.byte_footprint();
            Some(Resource::Memory(MemoryRange::new_with_element_width(
                base,
                0u32.into(),
                bytes,
                1,
            )))
        }
        _ => Some(resource.clone()),
    }
}

pub(crate) fn byte_premise(premise: &Proposition) -> Option<Proposition> {
    Some(match premise {
        Proposition::ResourceSeparate { left, right } => Proposition::ResourceSeparate {
            left: Box::new(byte_resource(left)?),
            right: Box::new(byte_resource(right)?),
        },
        Proposition::ResourceContains { parent, child } => Proposition::ResourceContains {
            parent: Box::new(byte_resource(parent)?),
            child: Box::new(byte_resource(child)?),
        },
        _ => premise.clone(),
    })
}
