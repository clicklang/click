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
                } => proof.driver().apply_execution_if_within(
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
    /// Applies one expanded arm of the split `arm_enclosing` ends with,
    /// inside the bounded arms before it.
    fn apply_focused_expanded_execution_arm(
        &self,
        arm_enclosing: &[&ExecutionSplit<'a>],
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[ProofStep],
    ) -> Result<Proof<'a>, ClickError> {
        let proof_object = self.proof;
        let record = arm_enclosing
            .last()
            .expect("an expanded arm runs inside its own split");
        let Some((proof, entry_steps)) = proof_object.focus_expanded_execution_arm_entry(
            record,
            take_then,
            surface_condition,
            steps,
        )?
        else {
            return Err(self
                .proof
                .step_error("cannot advance an infeasible expanded execution arm"));
        };
        proof
            .driver()
            .apply_execution_steps_within(arm_enclosing, &steps[entry_steps..], true)
    }

    /// Applies one planner (or, with `expanded`, already-expanded) `if`
    /// inside the bounded arms `enclosing` names (see
    /// [`Self::apply_execution_steps_within`]).
    fn apply_execution_if_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Proof<'a>, ClickError> {
        // A planner `if` at a C `if` whose condition has one path per truth
        // value enters an actual C `if` arm, including its branch-entry
        // statement steps. Every other planner `if` is a proof-level case
        // split: a native C `switch` is one checked statement whose symbolic
        // dispatch needs each generated arm to supply its selected case fact;
        // a statement or condition with path cases (a load that may read an
        // earlier store's cell, a short-circuit condition) needs each case's
        // facts before its one successor exists. The planner splits such an
        // operation one condition at a time and re-runs it on each side, so
        // the same question decides every nested planner `if` here as well.
        // An expanded `if` is the C branch exactly when it spells the C
        // condition, as at the top level; otherwise it is a case split.
        let mut split = None;
        let case_split = if expanded {
            !self.proof.frontier_is_execution_branch(condition)?
        } else if self.proof.execution_frontier_is_switch()? {
            true
        } else {
            match self.proof.execution_frontier_cases()? {
                FrontierCases::PathCases => true,
                FrontierCases::Branch(computed) => {
                    split = computed;
                    false
                }
            }
        };
        if case_split {
            let (split, record) = self.proof.split_focused_execution_if(condition.clone())?;
            let then_done = split
                .focus_execution_if_arm(&record, true)?
                .driver()
                .apply_execution_steps_within(enclosing, then_steps, expanded)?;
            let else_done = then_done
                .focus_execution_if_arm(&record, false)?
                .driver()
                .apply_execution_steps_within(enclosing, else_steps, expanded)?;
            return if then_done.is_at_function_exit() && else_done.is_at_function_exit() {
                else_done.join_focused_execution_if_terminal(&record)
            } else {
                else_done.join_focused_if(
                    &record.marker,
                    record.split,
                    record.arm_branches,
                    condition.clone(),
                )
            };
        }
        self.apply_execution_branch_within(
            enclosing, condition, then_steps, else_steps, expanded, split,
        )
    }

    /// Splits the C `if` at the frontier and applies each arm's steps inside
    /// `enclosing` and the new split, then joins. `condition_split` is the
    /// frontier condition's checked split if the caller already has it.
    fn apply_execution_branch_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
        expanded: bool,
        condition_split: Option<ConditionSplit>,
    ) -> Result<Proof<'a>, ClickError> {
        let (split, record) = self
            .proof
            .split_focused_execution_branch_with(condition_split)?;
        let mut arm_enclosing: Vec<&ExecutionSplit<'a>> = enclosing.to_vec();
        arm_enclosing.push(&record);
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                if expanded && !steps.is_empty() {
                    return Err(self.proof.step_error(format!(
                        "expanded execution {} arm is nonempty, but the checked C branch is infeasible",
                        if take_then { "then" } else { "else" },
                    )));
                }
                continue;
            }
            if expanded {
                // Proof operations may follow the last C step. Entry validation
                // and the checked join enforce the arm's execution boundary.
                advanced = advanced.driver().apply_focused_expanded_execution_arm(
                    &arm_enclosing,
                    take_then,
                    condition,
                    steps,
                )?;
                continue;
            }
            let entry_steps = advanced
                .checked_expanded_execution_arm_entry_steps(&record, take_then, None)?
                .len();
            if steps.len() < entry_steps
                || !steps[..entry_steps]
                    .iter()
                    .all(|step| matches!(step, ProofStep::Step))
            {
                return Err(self.proof.step_error(format!(
                    "planned execution {} arm does not begin with its {entry_steps} C branch-entry step(s)",
                    if take_then { "then" } else { "else" },
                )));
            }
            advanced = advanced
                .focus_split_arm(&record, take_then)?
                .driver()
                .apply_execution_steps_within(&arm_enclosing, &steps[entry_steps..], false)?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Applies an already-expanded logical C branch as one audited structural
    /// Proof transition. Source syntax supplies only its condition and simple
    /// arm operations; the split, entry validation, focused branch successors, and
    /// join remain owned by this Proof lineage.
    pub(in crate::surface::proof) fn apply_expanded_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
    ) -> Result<Proof<'a>, ClickError> {
        self.apply_execution_branch_within(&[], condition, then_steps, else_steps, true, None)
    }
}
