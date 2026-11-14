//! Remaining legacy call-frame discovery dependencies.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

impl crate::kernel::search::ProofSearch<ProgramFunction> {
    pub(in crate::kernel) fn call_frame(
        residual: &ResourceContext,
        definitions: &[CompositeResourceDefinition],
        _state: &ExecutionState,
        assumptions: &PureFactContext,
    ) -> CallKeptOwnership {
        #[cfg(test)]
        crate::kernel::search::record_discovery("call_frame");
        let premises = Vec::new();
        // A family whose bodies are argument-direct owns the same ranges
        // wherever its facts are held, so the kept set answers for those
        // composites per queried address and they are not opened here
        // (`CallKeptRanges::range_holding`). Other families remain opaque:
        // discovering their hidden memory is separate proof reasoning.
        let definition = |name: &str| {
            definitions
                .binary_search_by(|definition| definition.name().cmp(name))
                .ok()
                .map(|index| &definitions[index])
        };
        let mut direct = Vec::new();
        for (name, _) in residual.owned_composite_families() {
            if let Some(found) = definition(name)
                && found.has_argument_direct_body()
            {
                if direct
                    .last()
                    .is_none_or(|last: &CompositeResourceDefinition| last.name() != name)
                {
                    direct.push(found.clone());
                }
            }
        }
        CallKeptOwnership::new(
            residual.clone(),
            CallKeptRanges::new(
                ResourceContext::new_with_equalities(assumptions),
                premises,
                (!direct.is_empty()).then(|| std::sync::Arc::new(direct)),
            ),
            assumptions,
        )
    }
}
