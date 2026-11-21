//! Proof discovery, separate from explicit proof operations.
//!
//! This behavior-preserving boundary is a namespace parameterized by the
//! existing context. Search borrows that context and returns ordinary proof
//! successors/evidence; it owns no second proof state. Source-spelling adapters
//! specialize it for Surface Proof. Remaining callers are inventoried by the
//! build-time dependency manifest.
use std::marker::PhantomData;

pub(crate) struct ProofSearch<P: ?Sized> {
    _context: PhantomData<fn(&P)>,
}

mod permission;
pub(crate) mod proposition_search;
pub(crate) mod store_separation;
pub(crate) use permission::SearchPermission;

pub(crate) fn disjunction_candidates(
    context: &crate::kernel::PureFactContext,
) -> impl Iterator<Item = &crate::kernel::Proposition> {
    context.disjunction_fact_propositions(SearchPermission::new())
}

/// Enumerate universal premises only while planning an expandable proof.
pub(crate) fn universal_candidates(
    facts: &crate::kernel::proof::PureFactStore,
) -> impl Iterator<Item = &crate::kernel::Proposition> {
    facts.universal_facts_for_search(SearchPermission::new())
}

#[cfg(test)]
mod operation_guard;
#[cfg(test)]
pub(crate) use operation_guard::{FastOperationScope, record_discovery};

/// Select explicit implication sources from the consequent's indexed bucket.
pub(crate) fn implication_candidates(
    facts: &crate::kernel::proof::PureFactStore,
    goal: &crate::kernel::Proposition,
) -> Vec<crate::kernel::Proposition> {
    facts.implication_sources_for_search(goal, SearchPermission::new())
}

/// Project only disjunctions connected to the requested fact. Search, rather
/// than the simple checker, owns enumeration of a potentially growing bucket.
pub(crate) fn connected_disjunction_candidates(
    context: &crate::kernel::PureFactContext,
    goal: &crate::kernel::Proposition,
) -> Vec<crate::kernel::Proposition> {
    #[cfg(test)]
    record_discovery("connected_disjunction_candidates");
    let keys = crate::kernel::reasoning::variable_collection::collect_atomic_connection_keys(goal);
    let mut seen = std::collections::HashSet::new();
    let mut selected = Vec::new();
    for key in keys {
        for source in context.disjunctions_connected_to(&key) {
            crate::instrumentation::record_deterministic_work(1);
            if seen.insert(source as *const crate::kernel::Proposition) {
                selected.push(source.clone());
                if selected.len() == 64 {
                    return selected;
                }
            }
        }
    }
    selected
}

/// Probe a load equality bridge over a bounded prefix of indexed candidates.
pub(crate) fn load_equality_candidates(
    facts: &crate::kernel::proof::PureFactStore,
    goal: &crate::kernel::Proposition,
    limit: usize,
) -> Vec<crate::kernel::Proposition> {
    let candidates = facts.load_equality_candidates_for_solve(goal, limit, SearchPermission::new());
    if !candidates.is_empty()
        && crate::kernel::proof::fact_reasoning::plan_load_variable_bridge(
            goal,
            &candidates,
            facts.assumptions(),
        )
    {
        candidates
    } else {
        Vec::new()
    }
}
