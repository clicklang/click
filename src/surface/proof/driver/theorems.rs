//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Instantiate a named pure theorem's premise obligations, then let the
    /// driver prove them before selecting the application's remaining argument
    /// evidence. Other proof contexts retain their existing selection route.
    pub(in crate::surface::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Proof<'a>, ClickError> {
        let prepared;
        let driver_proof = if matches!(self.proof.context.as_ref(), ProofContext::Pure(_))
            && application.name != "population_member_count_zero"
            && !crate::surface::proof::theorem_application::is_integer_range_fold_theorem_name(
                &application.name,
            ) {
            let requirements = self.proof.prepare_pure_theorem_requirements(application)?;
            prepared = self.prove_pure_theorem_requirements(application, requirements)?;
            &prepared
        } else {
            self.proof
        };
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

    fn prove_pure_theorem_requirements(
        &self,
        application: &TheoremApplication,
        requirements: Vec<ClickProposition>,
    ) -> Result<Proof<'a>, ClickError> {
        let mut current = self.proof.clone();
        for requirement in requirements {
            if implicit_solve_disabled() {
                return Err(current.step_error("bare `apply` has implicit premise obligations; write `apply(...) using { ... }` to supply their proofs explicitly"));
            }
            let scope = current.driver().open_have(requirement.clone())?;
            let Some(closed) = scope.driver().try_solve_closure()? else {
                return Err(scope.body().step_error(format!(
                    "theorem `{}` has an unproved obligation: `{}`",
                    application.name,
                    crate::surface::printing::source_click_proposition(&requirement),
                )));
            };
            current = closed.join()?;
        }
        Ok(current)
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
