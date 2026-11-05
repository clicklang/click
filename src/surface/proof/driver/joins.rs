//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Applies planner (or, with `expanded`, already-expanded) execution
    /// steps inside the bounded C `if` arms `enclosing` names, innermost
    /// last. A path runs to function exit, so an execution-advancing step
    /// that finds the frontier at an arm's typed boundary continues
    /// privately into that arm's parent continuation through its split
    /// record, and again through the next record while the parent's own
    /// region is exhausted: a path escapes exactly as many arms as it is
    /// nested inside, as [`Self::try_focused_execute_to_exit_within`] does.
    /// Logical steps run at a boundary unchanged. A case split inside an arm
    /// (a load or condition with path cases) runs each case under the same
    /// chain, so a case that finishes the arm continues past it instead of
    /// failing as running off the arm.
    pub(in crate::surface::proof) fn apply_execution_steps_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        let mut proof = driver_proof.clone();
        let mut enclosing = enclosing.to_vec();
        for step in steps {
            if matches!(step, ProofStep::Step | ProofStep::If { .. }) {
                while proof.is_at_region_boundary() {
                    let Some(record) = enclosing.pop() else {
                        break;
                    };
                    proof = proof.continue_arm_into_parent_frontier(record)?;
                }
            }
            proof = match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                    ..
                } => proof.apply_execution_if_within(
                    &enclosing,
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                    expanded,
                )?,
                _ => proof.driver().apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }
}
