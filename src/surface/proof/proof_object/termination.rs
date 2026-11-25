use super::*;
use crate::kernel::{OrdinaryTerminationScope, TerminationCheck};

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn for_program_termination(
        scope: &Arc<OrdinaryTerminationScope>,
        surface: &SurfaceProposition,
        context: &'a PureTheoremContext,
        definitions: SpecDefinitions<'a>,
        theorems: &'a TheoremEnvironment,
    ) -> Self {
        let mut root = Self::for_pure_surface_goal(
            "program.termination",
            &[],
            scope.goal().clone(),
            surface.clone(),
            context,
            definitions,
            theorems,
        );
        let presentation = match root.focused_obligation().unwrap() {
            Obligation::Proposition(goal) => goal.presentation.clone(),
            _ => unreachable!(),
        };
        root.state = KernelProofObject::for_program_termination(
            ProofLocals::default(),
            scope.clone(),
            presentation,
        );
        root
    }

    pub(super) fn apply_termination_check(
        &self,
        step: TerminationCheck,
    ) -> Result<KernelProofHandle, ClickError> {
        let (state, report) = self
            .state
            .check_termination(&step)
            .map_err(|error| self.step_error(error))?;
        let scope = state
            .termination_scope()
            .expect("checked operation owns its termination scope");
        let mut locals = state.locals().clone();
        locals.termination_diagnostics.extend(report);
        for fact in state.checked_facts() {
            let surface = super::super::program_termination::spelling(scope, fact);
            locals.surface_facts.record_lowering(&surface, fact)?;
        }
        Ok(state.with_locals(locals))
    }

    pub(in crate::surface::proof) fn finish_program_termination(
        &self,
    ) -> Result<crate::kernel::ProvedProgramContracts, ClickError> {
        self.state
            .finish_program_termination()
            .map_err(|error| self.step_error(error))
    }

    pub(in crate::surface::proof) fn termination_scope(
        &self,
    ) -> Option<&Arc<OrdinaryTerminationScope>> {
        self.state.termination_scope()
    }
    pub(in crate::surface::proof) fn termination_failure(
        &self,
    ) -> Option<crate::kernel::ProgramContractFailure> {
        self.state
            .locals()
            .termination_diagnostics
            .failure(self.state.termination_scope()?, self.goal()?)
    }
    pub(in crate::surface::proof) fn termination_tactic_names(&self) -> &BTreeSet<String> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!("termination is a proposition proof")
        };
        context
            .spec_definitions
            .termination_tactics
            .expect("termination scope retains its source labels")
    }
}
