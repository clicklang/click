//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Completes externally owned fixed-state obligations against this frontier and
    /// exports their one structured certificate.
    ///
    /// Earlier checked descendants (notably `have` scopes) remain in the
    /// prefix. Each obligation is then independently selected and closed by
    /// an ordinary `Assumption` step against the accumulated persistent fact
    /// context. Certificate composition is therefore an audited terminal
    /// operation of `Proof`, not caller-owned syntax assembly.
    #[cfg(test)]
    pub(in crate::surface::proof) fn complete_fixed_state_obligations(
        &self,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .complete_fixed_state_obligations_inner(None, goals, &[])
            .map(|(certificate, _)| certificate)
    }

    /// Completes the obligations with a certificate relative to `since`.
    ///
    /// An evolving outcome proof carries every earlier drained tactic in its
    /// lineage; those steps are recorded by their own tactics, so the grouped
    /// closure exports only the scope and closer work performed after the
    /// caller's checkpoint. A fresh grouped root passes its own root
    /// checkpoint and the two forms agree.
    pub(in crate::surface::proof) fn complete_fixed_state_obligations_since(
        &self,
        since: &ProofCheckpoint<'a>,
        goals: &[ClickProposition],
        claim_goals: &[Vec<crate::kernel::CClaimGoal>],
    ) -> Result<
        (
            ProofCertificate,
            Vec<crate::kernel::proof::CheckedProposition>,
        ),
        ClickError,
    > {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .complete_fixed_state_obligations_inner(Some(since), goals, claim_goals)
    }

    pub(in crate::surface::proof) fn complete_fixed_state_obligations_inner(
        &self,
        since: Option<&ProofCheckpoint<'a>>,
        goals: &[ClickProposition],
        claim_goals: &[Vec<crate::kernel::CClaimGoal>],
    ) -> Result<
        (
            ProofCertificate,
            Vec<crate::kernel::proof::CheckedProposition>,
        ),
        ClickError,
    > {
        let driver_proof = self.proof;
        if goals.is_empty() {
            return Err(driver_proof
                .step_error("fixed-state obligation completion requires at least one goal"));
        }
        let fixed_state_context =
            matches!(driver_proof.context.as_ref(), ProofContext::FixedState(_))
                && matches!(
                    driver_proof.focused_obligation(),
                    Some(Obligation::Frontier(_))
                );
        let outcome_frontier = matches!(
            driver_proof.focused_obligation(),
            Some(Obligation::FunctionOutcome(_))
        );
        if !fixed_state_context && !outcome_frontier {
            return Err(driver_proof
                .step_error("fixed-state obligations require an open fixed-state proof context"));
        }
        let mut steps = match since {
            Some(since) => driver_proof.certificate_since(since)?.steps().to_vec(),
            None => driver_proof.certificate().steps().to_vec(),
        };
        let mut checked_propositions = Vec::with_capacity(goals.len());
        for (index, goal) in goals.iter().enumerate() {
            // Close the kernel's own goal for the claim when the accumulated
            // facts state it, so the completed proposition names its claim.
            let claim_closer = claim_goals.get(index).and_then(|forms| {
                forms.iter().find_map(|form| {
                    driver_proof
                        .focus_kernel_claim_goal(form, goal)
                        .and_then(|focused| focused.driver().apply_step(ProofStep::Assumption))
                        .ok()
                })
            });
            let closer = match claim_closer {
                Some(closer) => closer,
                None => driver_proof
                    .focus_fixed_state_surface_goal(goal)?
                    .driver()
                    .apply_step(ProofStep::Assumption)?,
            };
            checked_propositions.push(closer.completed_proposition()?);
            steps.extend_from_slice(closer.certificate().steps());
        }
        Ok((ProofCertificate::from_steps(steps)?, checked_propositions))
    }
}
