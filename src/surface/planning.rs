//! Surface Click planning: the search that finds a proof, separated from
//! the kernel that checks one.
//!
//! A planner here may explore freely. Everything it produces is handed back
//! to the kernel as a checked operation or an explicit certificate, so a
//! planning bug can lose a proof but can never issue authority.

pub(crate) mod proposition_search;

mod permission;
pub(crate) use permission::SearchPermission;

/// Ambient disjunction candidates for the smart closer. The capability stays
/// inside planning; callers still construct checked `cases` steps.
pub(in crate::surface) fn disjunction_candidates(
    context: &crate::kernel::PureFactContext,
) -> impl Iterator<Item = &crate::kernel::Proposition> {
    context.disjunction_fact_propositions(SearchPermission::new())
}
