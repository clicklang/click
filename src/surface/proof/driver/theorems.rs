//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Retain an application's evaluated arguments and instantiated result,
    /// then prove its argument and premise obligations before publication.
    pub(in crate::surface::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Proof<'a>, ClickError> {
        if (matches!(
            self.proof.context.as_ref(),
            ProofContext::Pure(_) | ProofContext::FixedState(_)
        ) || matches!(self.proof.context.as_ref(), ProofContext::Execution(_))
            && (!self.proof.is_at_function_exit() || self.proof.focused_outcome_data().is_some()))
        {
            let prepared = self.proof.prepare_theorem_application(application)?;
            let (current, premises) =
                self.prove_theorem_application_obligations(application, &prepared.obligations)?;
            let step = ProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: premises.clone(),
            };
            return current.driver().observe_step(step, |_| {
                let applied =
                    current.finish_prepared_theorem_application(prepared, application, premises)?;
                Ok(current
                    .driver()
                    .spell_applied_conclusions(application, applied))
            });
        }
        let driver_proof = self.proof;
        let Some(step) = crate::kernel::search::ProofSearch::select_theorem_application_step(
            driver_proof,
            application,
        )?
        else {
            return Err(driver_proof.step_error(
                "theorem application requires a result-sensitive fixed-state proof after function exit",
            ));
        };
        driver_proof
            .driver()
            .apply_selected_theorem_application(step)
    }

    fn prove_theorem_application_obligations(
        &self,
        application: &TheoremApplication,
        obligations: &[UnresolvedRequirement],
    ) -> Result<(Proof<'a>, Vec<ClickProposition>), ClickError> {
        let mut current = self.proof.clone();
        let mut premises = Vec::new();
        for requirement in obligations {
            if requirement.surface.is_none()
                && matches!(
                    normalize_proposition(&requirement.proposition),
                    NormalizedProposition::True
                )
            {
                continue;
            }
            let surface = current
                .requirement_surface(
                    requirement,
                    &ProofStep::ApplyTheoremUsing {
                        application: application.clone(),
                        premises: vec![],
                    },
                )?
                .ok_or_else(|| {
                    current.step_error("theorem application obligation has no Surface spelling")
                })?
                .surface;
            if implicit_solve_disabled() {
                return Err(current.step_error("bare `apply` has implicit premise obligations; write `apply(...) using { ... }` to supply their proofs explicitly"));
            }
            let scope = current.driver().open_have(surface.clone())?;
            let Some(closed) = scope.driver().try_solve_closure()? else {
                return Err(scope.body().step_error(format!(
                    "theorem `{}` has an unproved obligation: `{}`",
                    application.name,
                    crate::surface::printing::source_click_proposition(&surface)
                )));
            };
            current = closed.join()?;
            premises.push(surface);
        }
        Ok((current, premises))
    }

    pub(in crate::surface::proof) fn apply_selected_theorem_application(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof.driver().apply_step(step).map_err(|error| {
            driver_proof.step_error(format!(
                "theorem search selected a simple candidate that Proof rejected: {}",
                error.raw_summary()
            ))
        })
    }
}
