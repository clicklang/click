//! Checked termination operations on ordinary proposition proof states.
use super::*;
use crate::kernel::{OrdinaryTerminationScope, TerminationCheck, TerminationCheckReport};
use std::sync::Arc;

impl<L: Clone, P: Clone, O: Clone, E: Clone> ProofObject<L, ProofObligation<P, O>, E> {
    pub(crate) fn for_program_termination(
        locals: L,
        scope: Arc<OrdinaryTerminationScope>,
        presentation: P,
    ) -> Self {
        let goal = scope.goal().clone();
        let root = Self::root(
            locals,
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, presentation)),
                ProofBranchState {
                    facts: PureFactStore::default(),
                    unfolded_predicates: Default::default(),
                    execution: None,
                },
            ),
        );
        let mut state = root.state.as_ref().clone();
        state.termination = Some(scope);
        state.termination_root = true;
        Self::new(state, root.focused_branch)
    }

    pub(crate) fn with_termination_context(&self, scope: Arc<OrdinaryTerminationScope>) -> Self {
        let mut state = self.state.as_ref().clone();
        state.termination = Some(scope);
        state.termination_root = false;
        Self::new(state, self.focused_branch)
    }

    pub(crate) fn termination_scope(&self) -> Option<&Arc<OrdinaryTerminationScope>> {
        self.state.termination.as_ref()
    }

    pub(crate) fn check_termination(
        &self,
        step: &TerminationCheck,
    ) -> Result<(Self, TerminationCheckReport), String> {
        let scope = self
            .state
            .termination
            .as_ref()
            .ok_or("termination steps require a termination proof")?;
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("termination step requires an open goal")?;
        let (added, report) = scope.check(step, &branch.state.facts)?;
        let mut next = branch.clone();
        for fact in &added {
            next.state.facts = next.state.facts.with_fact(fact.clone());
        }
        let state = self
            .publish_checked_focused_result(
                self.state.locals.clone(),
                Some(next),
                added.clone(),
                added,
            )
            .map_err(|_| "termination step lost its focused goal")?;
        Ok((state, report))
    }

    pub(crate) fn finish_program_termination(
        &self,
    ) -> Result<crate::kernel::termination::completion::ProvedProgramContracts, String> {
        if !self.state.termination_root {
            return Err("this proof is not the program termination root".into());
        }
        self.completion()
            .ok_or("the ordinary termination proof still has open goals")?;
        Ok(self
            .state
            .termination
            .as_ref()
            .expect("the native root captured its scope")
            .finish())
    }
}
