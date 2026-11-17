//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

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
