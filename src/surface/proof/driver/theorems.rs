//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Use established antecedents directly and retain proofs for open ones.
    pub(in crate::surface::proof) fn apply_fact_application(
        &self,
        fact: &ClickProposition,
    ) -> Result<Proof<'a>, ClickError> {
        let (antecedents, _) = crate::surface::proof::driver::fact_application_parts(fact);
        if antecedents.is_empty() {
            return Err(self
                .proof
                .step_error("`apply(fact)` requires an implication fact"));
        }
        let step = ProofStep::ApplyFact(fact.clone());
        let direct = self.apply_step(step.clone());
        if direct.is_ok() || implicit_solve_disabled() {
            return direct;
        }
        let mut current = self.proof.clone();
        for antecedent in &antecedents {
            let lowered =
                current.lower_cited_surface_proposition(antecedent, "implication antecedent")?;
            if current.facts().pure_known_available(&lowered) {
                continue;
            }
            let scope = current.driver().open_have(antecedent.clone())?;
            let Some(closed) = scope.driver().try_solve_closure()? else {
                return Err(scope
                    .body()
                    .step_error(format!(
                        "`apply(fact)` has an unproved antecedent: `{}`",
                        crate::surface::printing::source_click_proposition(antecedent)
                    ))
                    .with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch));
            };
            current = closed.join()?;
        }
        current.driver().apply_step(step)
    }

    /// Retain an application's evaluated arguments and instantiated result,
    /// then prove its argument and premise obligations before publication.
    pub(in crate::surface::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Proof<'a>, ClickError> {
        if !matches!(self.proof.context.as_ref(), ProofContext::Execution(_))
            || !self.proof.is_at_function_exit()
            || self.proof.focused_outcome_data().is_some()
        {
            let step = ProofStep::ApplyTheorem(application.clone());
            return self.observe_step(step, |_| {
                self.apply_prepared_theorem(application, !implicit_solve_disabled())
            });
        }
        // The kernel's population law has no declared requirements to
        // instantiate: its one premise is the written population count, so it
        // applies at an exit that still holds several outcomes.
        let driver_proof = self.proof;
        let Some(step) =
            crate::surface::proof::theorem_application::population_member_count_zero_step(
                application,
            )
        else {
            return Err(driver_proof.step_error(
                "theorem application requires a result-sensitive fixed-state proof after function exit",
            ));
        };
        driver_proof
            .driver()
            .apply_selected_theorem_application(step)
    }

    /// Apply the theorem after checking its own instantiated requirements.
    /// Certificate replay calls this with solving disabled.
    pub(in crate::surface::proof) fn apply_prepared_theorem(
        &self,
        application: &TheoremApplication,
        allow_solve: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let prepared = self.proof.prepare_theorem_application(application)?;
        let mut current = self.proof.clone();
        let step = ProofStep::ApplyTheorem(application.clone());
        for requirement in &prepared.obligations {
            if current.theorem_obligation_available(requirement) {
                continue;
            }
            let surface = current
                .requirement_surface(requirement, &step)?
                .ok_or_else(|| {
                    current.step_error("theorem application obligation has no Surface form")
                })?
                .surface;
            let scope = current.driver().open_have(surface.clone())?;
            let refusal = || {
                scope.body().step_error(format!(
                    "theorem `{}` has an unproved obligation: `{}`",
                    application.name,
                    crate::surface::printing::source_click_proposition(&surface)
                ))
            };
            if let Ok(closed) = scope.driver().apply_step(ProofStep::Known) {
                current = closed.join()?;
                continue;
            }
            if !allow_solve {
                return Err(refusal());
            }
            let _timing = crate::surface::proof::timing::TacticTiming::implicit_solve();
            let _origin = crate::surface::proof_trace::TraceOrigin::enter(Some("implicit solve"));
            let Some(closed) = scope.driver().try_solve_closure()? else {
                return Err(
                    refusal().with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch)
                );
            };
            current = closed.join()?;
        }
        let applied = current.finish_prepared_theorem_application(prepared, application)?;
        Ok(current
            .driver()
            .spell_applied_conclusions(application, applied))
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
