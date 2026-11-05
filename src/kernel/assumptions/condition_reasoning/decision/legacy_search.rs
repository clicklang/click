//! Existing slow dependencies extracted without changing their decisions.
//! Each entry remains reachable only through its inventoried compatibility caller.
use super::*;

impl crate::kernel::search::ProofSearch<PureFactContext> {
    pub(crate) fn owned_anchor_distinctness(
        proof_input: &PureFactContext,
        left: &Pointer,
        right: &Pointer,
    ) -> Option<bool> {
        if proof_input.resource_compositions.is_empty() {
            return None;
        }
        let lefts = proof_input.pointer_equality_component(left);
        let rights = proof_input.pointer_equality_component(right);
        if lefts
            .iter()
            .any(|(pointer, _)| rights.iter().any(|(other, _)| other == pointer))
        {
            // One equality chain connects the two sides: they are one
            // address, and no owned member can say otherwise.
            return None;
        }
        // A composition holding both members is listed under a key of each:
        // a member's base, which a member lookup probes among the
        // spelling's additive bases, or its block (`CompositionMemberIndex`).
        let spellings = lefts.iter().chain(&rights).map(|(pointer, _)| pointer);
        let bases = spellings
            .clone()
            .flat_map(super::super::memory_reasoning::additive_base_spellings)
            .collect::<Vec<_>>();
        let blocks = spellings.map(|pointer| &pointer.block).collect::<Vec<_>>();
        for resources in proof_input.composition_members.listed_under(&bases, blocks) {
            for (left_index, (left_spelling, _)) in lefts.iter().enumerate() {
                let Some(left_member) =
                    proof_input.owned_member_holding_access(resources, left_spelling, 1)
                else {
                    continue;
                };
                for (right_index, (right_spelling, _)) in rights.iter().enumerate() {
                    let Some(right_member) =
                        proof_input.owned_member_holding_access(resources, right_spelling, 1)
                    else {
                        continue;
                    };
                    if left_member == right_member
                        || matches!(left_member.base().block, PointerBlock::StringLiteral { .. })
                        || matches!(
                            right_member.base().block,
                            PointerBlock::StringLiteral { .. }
                        )
                    {
                        continue;
                    }
                    proof_input.record_pointer_equality_path(&lefts, left_index)?;
                    proof_input.record_pointer_equality_path(&rights, right_index)?;
                    record_implicit_reasoning_provenance(
                        proof_input,
                        &Proposition::CResourceComposition(resources.clone()),
                    );
                    return Some(false);
                }
            }
        }
        None
    }
}
