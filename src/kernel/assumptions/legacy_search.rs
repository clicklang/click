//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

impl crate::kernel::search::ProofSearch<PureFactContext> {
    pub(crate) fn composition_context(proof_input: &PureFactContext) -> PureFactContext {
        #[cfg(test)]
        crate::kernel::search::record_discovery("composition_context");
        let mut context = PureFactContext::new();
        for resources in proof_input.resource_compositions.scan_for_upkeep() {
            context =
                context.assume_proposition(Proposition::CResourceComposition(resources.clone()));
        }
        context
    }
}
