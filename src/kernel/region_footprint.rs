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
    pub(crate) before: CMemory,
    pub(crate) after: CMemory,
    pub(crate) before_resources: ResourceContext,
    pub(crate) after_resources: ResourceContext,
    pub(crate) members: imbl::Vector<CResource>,
    pub(crate) complete: bool,
    is_sequence: bool,
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
        before: &CState,
        after: &CState,
        effects: &(impl ExecutionFactSource + ?Sized),
    ) -> Arc<Self> {
        let mut members = imbl::Vector::new();
        for fact in effects.fact_iter() {
            crate::instrumentation::record_deterministic_work(1);
            match fact.proposition() {
                Proposition::CMemoryMutatesOnly { writes, .. } => {
                    for (pointer, bytes) in writes {
                        members.push_back(CResource::Memory(CMemoryRange::new_with_element_width(
                            pointer.clone(),
                            0u32.into(),
                            (*bytes).into(),
                            1,
                        )));
                    }
                }
                Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                    members.extend(mutable_ranges.iter().cloned().map(CResource::Memory));
                }
                Proposition::CHeapAllocationFreed {
                    allocation_base,
                    bytes,
                    ..
                } => {
                    members.push_back(CResource::Memory(CMemoryRange::new_with_element_width(
                        allocation_base.clone(),
                        0u32.into(),
                        bytes.clone(),
                        1,
                    )));
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
                    if contents.size.as_const() == Some(0) {
                        continue;
                    }
                    members.push_back(CResource::Memory(CMemoryRange::new_with_element_width(
                        Pointer {
                            block: block.clone(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0u32.into(),
                        contents.size.clone(),
                        1,
                    )));
                }
            }
        }
        let changed = after.resources().changed_facts_since(before.resources());
        let complete = changed.is_some();
        if let Some(changed) = changed {
            for fact in changed {
                crate::instrumentation::record_deterministic_work(1);
                if let CResourceFact::Own(resource, _) = fact
                    && !matches!(resource, CResource::Memory(_))
                {
                    // Spatial ownership may split or coalesce while a call
                    // lends and returns a cell. Those map edits do not write
                    // bytes. Memory writes and lifetime effects are recorded
                    // above; retain changes to named resource observations.
                    members.push_back(resource);
                }
            }
        }
        Arc::new(Self {
            source,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            before: before.memory().clone(),
            after: after.memory().clone(),
            before_resources: before.resources().clone(),
            after_resources: after.resources().clone(),
            members,
            complete,
            is_sequence: false,
        })
    }

    pub(crate) fn sequence(
        source: String,
        before: &CState,
        after: &CState,
        members: imbl::Vector<CResource>,
        complete: bool,
    ) -> Arc<Self> {
        Arc::new(Self {
            source,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            before: before.memory().clone(),
            after: after.memory().clone(),
            before_resources: before.resources().clone(),
            after_resources: after.resources().clone(),
            members,
            complete,
            is_sequence: true,
        })
    }
}

/// Establish collection separation from explicitly selected premises. Only the
/// named region's recorded members are visited; no execution history is read.
pub(crate) fn separate_using(left: &CResource, right: &CResource, facts: &PureFactContext) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    // Do not turn two effect collections into a Cartesian product.
    if matches!(
        (left, right),
        (CResource::Footprint(_), CResource::Footprint(_))
    ) {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        let empty = |resource: &CResource| {
            matches!(resource,
            CResource::Memory(range) if range.wide_bounds().is_none()
                && range.byte_footprint().1.as_const() == Some(0))
        };
        if empty(left) || empty(right) {
            continue;
        }
        match (left, right) {
            (CResource::Footprint(fp), other) | (other, CResource::Footprint(fp)) => {
                // A simple normalization never walks a region's execution
                // sequence. Longer transports spell each preservation edge.
                if !fp.complete || (fp.is_sequence && fp.members.len() > 1) {
                    return false;
                }
                pending.extend(fp.members.iter().map(|member| (member, other)));
            }
            // Primitive tokens contain no bytes. Releasing an allocation
            // still records its memory extent separately above.
            (CResource::Token { .. }, CResource::Memory(_))
            | (CResource::Memory(_), CResource::Token { .. }) => {}
            (CResource::Memory(left), CResource::Memory(right))
                if left.base().blocks_proven_distinct(right.base()) => {}
            _ => {
                let (Some(left), Some(right)) = (byte_resource(left), byte_resource(right)) else {
                    return false;
                };
                let forward = Proposition::CResourceSeparate {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let reverse = Proposition::CResourceSeparate {
                    left: Box::new(right),
                    right: Box::new(left),
                };
                // Parent/child restriction and alias rewriting are explicit
                // preceding proof steps, not repeated searches per member.
                if !facts.contains_assumed_exact(&forward)
                    && !facts.contains_assumed_exact(&reverse)
                {
                    return false;
                }
            }
        }
    }
    true
}

/// Compare spatial resources in byte coordinates, independently of their C
/// element types. Unsupported wide intervals decline instead of narrowing.
pub(crate) fn byte_resource(resource: &CResource) -> Option<CResource> {
    match resource {
        CResource::Memory(range) => {
            if range.wide_bounds().is_some() {
                return None;
            }
            let (base, bytes) = range.byte_footprint();
            Some(CResource::Memory(CMemoryRange::new_with_element_width(
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
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: Box::new(byte_resource(left)?),
            right: Box::new(byte_resource(right)?),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: Box::new(byte_resource(parent)?),
            child: Box::new(byte_resource(child)?),
        },
        _ => premise.clone(),
    })
}
