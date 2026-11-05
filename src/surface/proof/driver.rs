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
