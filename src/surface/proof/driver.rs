//! Interprets proof scripts and selects explicit operations or proof search.
//!
//! A driver borrows the existing persistent state. It owns no proof state,
//! performs no replay, and changes no search policy. The implementation files
//! in `driver/` are mounted by their existing helper modules to preserve private
//! helper visibility while moving orchestration off the Proof interface.
use super::proof_object::{Proof, ProofScope};

pub(in crate::surface) struct ProofDriver<'p, P> {
    pub(in crate::surface::proof) proof: &'p P,
}

/// Borrow a source proof or scope for script interpretation.
/// Method lookup also accepts borrowed proofs without copying their state.
pub(in crate::surface) trait DriveProof: Sized {
    fn driver(&self) -> ProofDriver<'_, Self> {
        ProofDriver { proof: self }
    }
}
impl DriveProof for Proof<'_> {}
impl DriveProof for ProofScope<'_> {}

/// A source obligation is a terminal refusal, even when a structural
/// partition miss would let the caller try a different execution route.
#[derive(Debug)]
pub(in crate::surface::proof) enum OutcomeSplitFailure {
    Partition(super::ClickError),
    Obligation(super::ClickError),
}

impl From<super::ClickError> for OutcomeSplitFailure {
    fn from(error: super::ClickError) -> Self {
        Self::Partition(error)
    }
}

/// Peel the written implication chain, retaining an explicit program point
/// on both its antecedents and its conclusion.
pub(in crate::surface::proof) fn fact_application_parts(
    fact: &super::SurfaceProposition,
) -> (Vec<super::SurfaceProposition>, super::SurfaceProposition) {
    if let super::SurfaceProposition::At {
        selector,
        proposition,
    } = fact
    {
        let (premises, conclusion) = fact_application_parts(proposition);
        let at = |proposition| super::SurfaceProposition::At {
            selector: selector.clone(),
            proposition: Box::new(proposition),
        };
        return (premises.into_iter().map(&at).collect(), at(conclusion));
    }
    let mut premises = Vec::new();
    let mut conclusion = fact;
    while let super::SurfaceProposition::Implies(left, right) = conclusion {
        premises.push(left.as_ref().clone());
        conclusion = right;
    }
    (premises, conclusion.clone())
}
