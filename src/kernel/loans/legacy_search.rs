//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

impl crate::kernel::search::ProofSearch<LoanLedger> {
    pub(crate) fn loan_aliases(
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Vec<CMemoryRange> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("loan_aliases");
        // Rebase through the indexed, directly stated equalities before scaling
        // element offsets. An equality such as w == p + 1 relates different pointer
        // spellings, which syntactic pointer subtraction alone cannot see.
        let mut bases = vec![range.base().clone()];
        bases.extend(assumptions.exact_pointer_aliases(range.base()).cloned());
        bases.extend(assumptions.exact_pointer_offset_aliases(range.base()));
        for _ in bases.iter().skip(1) {
            crate::instrumentation::record_deterministic_work(1);
        }
        bases
            .into_iter()
            .map(|base| {
                // The bounds move unread to another spelling of the base, so
                // either kind of range is rebased the same way.
                let (start, end) = range.bound_terms();
                range.with_bounds(base, start.clone(), end.clone())
            })
            .collect()
    }
}

impl crate::kernel::search::ProofSearch<LoanLedger> {
    pub(crate) fn loan_access(
        proof_input: &LoanLedger,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Result<(), LoanRefusal> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("loan_access");
        // This barrier only restricts otherwise owner-authorized writes.
        // With no active memory loans there is nothing to compare, regardless
        // of pointer aliases, non-memory loans, or ended loan history.
        if !proof_input.has_active_memory_loans() || memory_range_is_empty(range) {
            return Ok(());
        }
        let aliases = memory_range_aliases(range, assumptions);
        let indexed_ranges_exist = !proof_input.storage.data.active_memory_index.is_empty()
            || !proof_input.storage.data.active_memory_subtree.is_empty();
        if indexed_ranges_exist {
            // Any exact spelling of the same concrete address can drive the
            // dyadic lookup. The alias facts are indexed, so this visits only
            // the query's stated aliases and their interval buckets.
            let mut indexed_alias_exists = false;
            for alias in &aliases {
                if memory_interval_nodes(alias).is_some() {
                    indexed_alias_exists = true;
                    if proof_input.first_active_memory_overlap(alias)?.is_some() {
                        return Err(LoanRefusal::ActiveDependency);
                    }
                }
            }
            if !indexed_alias_exists
                && !(aliases.iter().all(|alias| {
                    matches!(
                        alias.base().block,
                        PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_)
                    )
                }) && proof_input.storage.data.active_nonlocal_indexed_ranges == 0
                    && proof_input.storage.data.unindexed_memory.is_empty())
            {
                // Every indexed loan is then on a fresh `local:` block. An
                // external input cannot reach those blocks unless an exact
                // alias says otherwise; in that case the test above refuses
                // the non-indexable query conservatively.
                return Err(LoanRefusal::UnsupportedPartition);
            }
        }
        let mut checked_blocks = BTreeSet::new();
        for alias in aliases {
            if !checked_blocks.insert(alias.base().block.clone()) {
                continue;
            }
            let Some(protected) = proof_input
                .storage
                .data
                .unindexed_memory
                .get(&alias.base().block)
            else {
                continue;
            };
            for (_, ranges) in protected.iter() {
                for protected in ranges {
                    crate::instrumentation::record_deterministic_work(1);
                    if protected_range_proven_overlapping(range, protected, assumptions) {
                        return Err(LoanRefusal::ActiveDependency);
                    }
                }
            }
        }
        Ok(())
    }
}
