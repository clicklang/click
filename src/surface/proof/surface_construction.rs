use super::*;

pub(in crate::surface::proof) fn have_proof_is_smart_solve(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default
        | SourceProof::Tactic(SmartTactic::ImplicitTail | SmartTactic::Solve) => true,
        SourceProof::Script(tactics) => matches!(
            tactics.as_slice(),
            [ProofTactic::Solve] | [ProofTactic::SolveUsing(_)]
        ),
    }
}
