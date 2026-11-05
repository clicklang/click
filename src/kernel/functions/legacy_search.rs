//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

impl crate::kernel::search::ProofSearch<CFunction> {
    pub(crate) fn call_frame(
        residual: &ResourceContext,
        definitions: &[CCompositeResourceDefinition],
        state: &CState,
        assumptions: &PureFactContext,
    ) -> CallKeptOwnership {
        let mut ranges = Vec::new();
        let mut premises = Vec::new();
        for fact in residual.owned_instances() {
            if let Some((body_ranges, body_premises)) =
                unmatched_instance_body_ownership(fact, definitions, state, assumptions).or_else(
                    || matched_instance_body_ownership(fact, definitions, state, assumptions),
                )
            {
                ranges.extend(body_ranges);
                premises.extend(body_premises);
            }
        }
        // A family whose bodies are argument-direct owns the same ranges
        // wherever its facts are held, so the kept set answers for those
        // composites per queried address and they are not opened here
        // (`CallKeptRanges::range_holding`). Every other family opens each of
        // its held composites at this state.
        let definition = |name: &str| {
            definitions
                .binary_search_by(|definition| definition.name().cmp(name))
                .ok()
                .map(|index| &definitions[index])
        };
        let mut direct = Vec::new();
        for (name, facts) in residual.owned_composite_families() {
            if let Some(found) = definition(name)
                && found.has_argument_direct_body()
            {
                if direct
                    .last()
                    .is_none_or(|last: &CCompositeResourceDefinition| last.name() != name)
                {
                    direct.push(found.clone());
                }
                continue;
            }
            for fact in facts {
                let Some(expanded) = expand_composites_for_frame(
                    &ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_fact(fact.clone()),
                    definitions,
                    state.memory(),
                    assumptions,
                ) else {
                    continue;
                };
                ranges.extend(owned_memory_ranges_of(&expanded));
            }
        }
        CallKeptOwnership::new(
            residual.clone(),
            CallKeptRanges::new(
                ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_facts(ranges.into_iter().map(CResourceFact::own_memory)),
                premises,
                (!direct.is_empty()).then(|| std::sync::Arc::new(direct)),
            ),
            assumptions,
        )
    }
}
