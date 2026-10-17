//! Separation sources indexed by numeric address classes. Explicit range
//! separation and C comparisons' selected two-holder projections share one
//! index; larger ownership frames never generate all their possible pairs.
use super::*;
use std::sync::Arc;

fn anchor(range: &CMemoryRange) -> Option<Pointer> {
    let offset = crate::kernel::assumptions::memory_range_anchor(range)?;
    Some(Pointer {
        block: range.base().block.clone(),
        offset,
    })
}

impl EqualityGraph {
    pub(super) fn adjust_address_separation_source(
        &self,
        source: &Arc<dyn terms::PointerFactSource>,
        insert: bool,
    ) -> bool {
        let anchors = match source.proposition() {
            Proposition::CResourceSeparate { left, right } => {
                let (CResource::Memory(a), CResource::Memory(b)) = (left.as_ref(), right.as_ref())
                else {
                    return false;
                };
                let (Some(a), Some(b)) = (anchor(a), anchor(b)) else {
                    return true;
                };
                [a, b]
            }

            _ => return false,
        };
        let mut state = self.state.lock().expect("equality graph");
        for pointer in &anchors {
            self.register_logical_read_values(&mut state, [pointer]);
            state.register_pointer_address(pointer);
        }
        let identity = Arc::as_ptr(source) as *const () as usize;
        if insert {
            state.separation_sources = state.separation_sources.with_value(identity);
            state.pointer_fact_inputs.insert(identity, source.clone());
        } else {
            state.separation_sources = state.separation_sources.without_value(&identity);
            state.pointer_fact_inputs.remove(&identity);
        }
        // Indexed condition applications already propagate operand unions and
        // retain exact source payloads. No independent alias graph is needed.
        for (a, b) in [(&anchors[0], &anchors[1]), (&anchors[1], &anchors[0])] {
            let condition = ConditionTerm::uint64_equal(
                Bitvector32Term::pointer_address(a.clone()),
                Bitvector32Term::pointer_address(b.clone()),
            );
            // Equal anchors and literal addresses can simplify to a constant.
            // They need no indexed application (and grant no new conclusion).
            let Some(node) = state.terms.condition_node(&condition) else {
                continue;
            };
            state.terms.adjust_pointer_fact(
                node,
                terms::PointerFactKey::AddressSeparation,
                source,
                insert,
            );
        }
        true
    }

    /// Retain the actual scoped premise, rather than manufacturing a pointer
    /// inequality that could discard the numeric separation conclusion.
    pub(in crate::kernel) fn address_separation_source(
        &self,
        condition: &ConditionTerm,
    ) -> Option<Proposition> {
        let (a, b) = match condition {
            ConditionTerm::PointerEqual(a, b) => (a.as_ref(), b.as_ref()),
            ConditionTerm::Bitvector64Equal(a, b) => (a.address_pointer()?, b.address_pointer()?),
            _ => return None,
        };
        let numeric = ConditionTerm::uint64_equal(
            Bitvector32Term::pointer_address(a.clone()),
            Bitvector32Term::pointer_address(b.clone()),
        );
        let mut state = self.state.lock().expect("equality graph");
        if state.separation_sources.is_empty() {
            return None;
        }
        self.prepare_condition(&mut state, &numeric);
        let a = state.terms.numeric_address(a);
        let b = state.terms.numeric_address(b);
        if state.terms.scalar_class_root(a) == state.terms.scalar_class_root(b) {
            return None;
        }
        let node = state.terms.condition_node(&numeric)?;
        state
            .terms
            .pointer_facts(node, &terms::PointerFactKey::AddressSeparation)
            .get(&String::new())?
            .iter()
            .next()
            .map(|(_, source)| source.proposition().clone())
    }
}
