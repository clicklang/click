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
pub(crate) use permission::SearchPermission;

pub(crate) fn disjunction_candidates(
    context: &crate::kernel::PureFactContext,
) -> impl Iterator<Item = &crate::kernel::Proposition> {
    context.disjunction_fact_propositions(SearchPermission::new())
}
