//! Source proof orchestration.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    pub(in crate::surface::proof) fn apply_all_source(
        &self,
        tactic: &ProofTactic,
        implicit_tail: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        // Keep the conjunction at its claim-level source site so each
        // nested arm receives the same address as a tactic written there.
        driver_proof
            .driver()
            .try_addressed_linear_script(
                std::slice::from_ref(tactic),
                std::slice::from_ref(driver_proof.site()),
                &mut None,
                None,
                implicit_tail,
            )?
            .ok_or_else(|| {
                driver_proof.step_error("`all` requires complete proofs of its conjuncts")
            })
    }

    /// Splits a proof path condition that exactly names the current C `if`
    /// and applies each arm's leading source step as a checked `Step` on
    /// that focused branch Proof, which decides the C `if` from the assumed case. The returned arms remain
    /// proof cases, so their source scopes may continue through the C join;
    /// only the branch-entry transition is selected here.
    pub(in crate::surface::proof) fn try_split_source_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, usize); 2],
    ) -> Result<Option<(Proof<'a>, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let driver_proof = self.proof;
        let Some(execution) = driver_proof.execution() else {
            return Ok(None);
        };
        let ProofContext::Execution(context) = driver_proof.context.as_ref() else {
            return Ok(None);
        };
        let statement_index = execution.core.frontier.next_statement_index;
        let (_, current_state, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "source proof `if`",
        )?;
        let ProgramStatement::If {
            condition: c_condition,
            ..
        } = statement
        else {
            return Ok(None);
        };
        let source_fact =
            driver_proof.lower_surface_proposition(condition, "proof `if` condition")?;
        let c_surface = surface_program_condition(
            &c_condition,
            &current_state,
            Some(&execution.presentation.recorded_states),
        )?;
        let c_fact =
            driver_proof.lower_surface_proposition(&c_surface, "current C `if` condition")?;
        if !path_condition_equivalent(&source_fact, &c_fact) {
            return Ok(None);
        }

        let surface_condition = surface_at_program_point(
            &c_surface,
            &ProgramPointRef {
                region: CodeRegionRef::Region(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let (split, record) = driver_proof.split_focused_execution_if_with_surface_condition(
            condition.clone(),
            surface_condition,
        )?;
        let mut advanced = split;
        for (arm_index, take_then) in [(0usize, true), (1usize, false)] {
            let (_, source_index) = arm_steps[arm_index];
            advanced = advanced
                .focus_execution_if_arm(&record, take_then)?
                .driver()
                .apply_step_at(ProofStep::Step, source_index)?;
        }
        Ok(Some((advanced, record)))
    }
}
