//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;
use crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap;

impl ResourceContext {
    /// Compatibility admission: indexed checking first, then explicitly
    /// resume the existing discovery operation for unsupported coverage.
    pub(crate) fn try_compose_with_legacy_discovery_and_occurrences(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        match self.admit_without_discovery(facts, assumptions) {
            OwnershipAdmission::Admitted { context, inserted } => Ok((context, inserted)),
            OwnershipAdmission::Conflict(error) => Err(error),
            OwnershipAdmission::Unsupported(pending) => pending.resume_legacy_discovery(),
        }
    }
}

impl ResourceContext {
    /// Compatibility query for one new memory owner. Retain the selected held
    /// fact at the comparison, rather than rediscovering it for diagnostics.
    /// Only old/new pairs are checked; neither partition is revalidated.
    fn legacy_memory_boundary_conflict(
        &self,
        right: &ResourceFact,
        before: ResourceEntryId,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceContextValidityError, ResourceFact)> {
        let right_range = right.memory_own_range()?;
        let coordinates = constant_memory_coordinates(right_range);
        if coordinates
            .as_ref()
            .is_some_and(|(_, start, end)| start >= end)
        {
            return None;
        }
        let same_origin_neighbors = coordinates.and_then(|(origin, start, end)| {
            let members = self
                .storage
                .index
                .owned_memory_by_block
                .get(&right_range.base().block)?
                .len();
            self.constant_owned_neighbors(&origin, start, end, members)
        });
        if let Some(mut candidates) = same_origin_neighbors {
            candidates.remove(&before);
            // Every owned range of this block has this origin, so the two
            // neighbours stand for the block; ranges an exact alias
            // relates from other blocks are still compared.
            if assumptions.has_pointer_block_aliases() {
                candidates.extend(
                    self.owned_validity_candidates(
                        right_range,
                        Some(&right_range.base().block),
                        assumptions,
                    )
                    .into_iter()
                    .filter(|entry| *entry < before),
                );
            }
            for left_entry in candidates {
                crate::instrumentation::record_deterministic_work(1);
                let left = self.fact(left_entry);
                if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                    left,
                    right,
                    assumptions,
                ) {
                    return Some((error, left.clone()));
                }
            }
            return None;
        }
        for left_entry in self.owned_validity_candidates(right_range, None, assumptions) {
            if left_entry >= before {
                break;
            }
            crate::instrumentation::record_deterministic_work(1);
            let left = self.fact(left_entry);
            if let Some(error) =
                resource_family_algebra(left.family()).pair_validity_error(left, right, assumptions)
            {
                return Some((error, left.clone()));
            }
        }
        None
    }

    /// Check only the new boundary of an already constructed return body.
    /// Unsupported memory geometry explicitly retains legacy discovery.
    pub(in crate::kernel) fn returned_boundary_conflict_with_legacy_discovery(
        &self,
        frontier: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Option<(ResourceFact, ResourceFact)> {
        for piece in frontier {
            crate::instrumentation::record_deterministic_work(1);
            let exclusive = match piece.resource() {
                Resource::Instance(instance) => {
                    self.storage.index.instances.get(&instance.identity)
                }
                Resource::PopulationAuthority(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_) => self.storage.index.by_resource.get(piece.resource()),
                _ => None,
            };
            if let Some(entry) = exclusive.and_then(|entries| entries.iter().next()) {
                return Some((piece.clone(), self.fact(*entry).clone()));
            }
            let held = match self.constant_owned_overlap(piece, assumptions) {
                ConstantOwnedOverlap::Clear => None,
                ConstantOwnedOverlap::Overlap(entry) => Some(self.fact(entry).clone()),
                ConstantOwnedOverlap::Unsupported => self
                    .legacy_memory_boundary_conflict(piece, self.storage.next_entry_id, assumptions)
                    .map(|(_, held)| held),
            };
            if let Some(held) = held {
                return Some((piece.clone(), held));
            }
        }
        None
    }
}

impl PendingOwnershipAdmission<'_> {
    pub(crate) fn resume_legacy_discovery(
        self,
    ) -> Result<
        (ResourceContext, Vec<(ResourceFact, ResourceOccurrenceId)>),
        ResourceContextValidityError,
    > {
        let Self {
            context,
            inserted,
            indexed_checked,
            first_new,
            first_unresolved,
            assumptions,
        } = self;
        for right_entry in first_unresolved..context.storage.next_entry_id {
            let right = context.fact(right_entry);
            if right_entry != first_unresolved
                && let Some(error) = context.exclusive_validity_error(right)
            {
                return Err(error);
            }
            if indexed_checked[(right_entry - first_new) as usize] {
                continue;
            }
            if let Some((error, _)) =
                context.legacy_memory_boundary_conflict(right, right_entry, assumptions)
            {
                return Err(error);
            }
        }
        context.advance_prepared_memory_equalities(assumptions);
        Ok((context, inserted))
    }
}

impl crate::kernel::search::ProofSearch<ResourceContext> {
    pub(crate) fn ownership_validity_candidates(
        proof_input: &ResourceContext,
        range: &MemoryRange,
        skip_block: Option<&PointerBlock>,
        assumptions: &PureFactContext,
    ) -> BTreeSet<ResourceEntryId> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("ownership_validity_candidates");
        let index = &proof_input.storage.index;
        let base = range.base();
        let mut candidates = BTreeSet::new();
        // The caller has already covered skip_block. If it is the only
        // owned block, aliases cannot nominate any remaining candidates.
        if skip_block.is_some_and(|block| !proof_input.has_owned_memory_outside_block(block)) {
            return candidates;
        }
        // Same-block aliases can nominate only members of this block. When
        // there are fewer owned members than aliases, checking the complete
        // block is cheaper than expanding the aliases' equality classes.
        // Cross-block aliases retain the indexed path below.
        if Some(&base.block) != skip_block
            && assumptions.exact_pointer_aliases(base).next().is_none()
            && let Some(entries) = index.owned_memory_by_block.get(&base.block)
            && entries.len() <= assumptions.exact_pointer_offset_alias_count(base)
        {
            for entry in entries.iter() {
                crate::instrumentation::record_deterministic_work(1);
                candidates.insert(*entry);
            }
            return candidates;
        }
        let add_owned_at_base = |candidates: &mut BTreeSet<ResourceEntryId>, at: &Pointer| {
            if Some(&at.block) == skip_block {
                return;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entries) = index.owned_memory_by_base.get(at) {
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    candidates.insert(*entry);
                }
            }
        };
        for alias in assumptions.exact_pointer_aliases(base) {
            if Some(&alias.block) == skip_block {
                continue;
            }
            if let Some(neighbors) =
                proof_input.constant_owned_neighbors_at_exact_alias(range, alias)
            {
                candidates.extend(neighbors);
            } else {
                add_owned_at_base(&mut candidates, alias);
            }
        }
        if Some(&base.block) == skip_block {
            return candidates;
        }
        let mut roots = related_memory_base_roots(base, assumptions);
        for alias in assumptions.exact_pointer_offset_aliases(base) {
            crate::instrumentation::record_deterministic_work(1);
            // An alias whose root is already collected adds nothing: its
            // related roots are the scalings of the same recorded-equality
            // class, which is a whole connected component. Without this, N
            // aliases of one base each re-walked the N-member class.
            if roots.contains(&memory_base_root(&alias)) {
                continue;
            }
            roots.extend(related_memory_base_roots(&alias, assumptions));
        }
        let query_root = memory_base_root(base);
        let coordinates = constant_memory_coordinates(range);
        for root in &roots {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entries) = index.owned_memory_by_root.get(root) {
                let neighbors = coordinates.as_ref().and_then(|(origin, start, end)| {
                    (root == &query_root)
                        .then(|| {
                            proof_input.constant_owned_neighbors(
                                origin,
                                *start,
                                *end,
                                entries.len(),
                            )
                        })
                        .flatten()
                });
                if let Some(neighbors) = neighbors {
                    candidates.extend(neighbors);
                } else {
                    for entry in entries.iter() {
                        crate::instrumentation::record_deterministic_work(1);
                        candidates.insert(*entry);
                    }
                }
            }
            // The other direction: an owned range whose own base has a
            // same-block exact alias at this root. The equalities are
            // symmetric and indexed by the root of each side, so this is
            // one keyed lookup that costs the equalities naming the root.
            for aliased in assumptions.offsets_with_an_alias_at_root(&root.1) {
                add_owned_at_base(
                    &mut candidates,
                    &Pointer {
                        block: root.0.clone(),
                        offset: aliased,
                    },
                );
            }
        }
        candidates
    }
}
