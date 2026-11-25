//! Which written tactics each proof context admits, declared in one place.
//!
//! A written tactic converts to a checked step through one mapping,
//! `ProofStep::from_leaf_tactic`. A context differs only in which tactics it
//! admits; this table says which, so a context never carries its own copy of
//! the conversion.

use super::*;

/// A proof context that interprets written tactics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) enum SourceContext {
    /// A proposition goal: a `have` body, a theorem or claim proof, or an
    /// explicit script inside smart search.
    PureGoal,
    /// An execution frontier that has not reached the function exit: the
    /// linear continuation, a focused execution arm, a loop's `maintain`
    /// body and a linear `with` scope.
    ExecutionFrontier,
    /// A path that has reached the function exit, where a tactic runs once
    /// per concrete outcome.
    PostExecution,
}

impl SourceContext {
    /// Whether this context runs `tactic` as one checked leaf step.
    fn admits_leaf(self, tactic: &ProofTactic) -> bool {
        // A memory observation reads one held permission, without changing
        // resources, so it also applies in a proposition or outcome proof.
        if matches!(
            tactic,
            ProofTactic::ObserveResource(
                ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_)
            ) | ProofTactic::ObserveSubject(_)
        ) {
            return true;
        }
        match self {
            Self::PureGoal => matches!(
                tactic,
                ProofTactic::ApplyFactUsing { .. }
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::Induct { .. }
                    | ProofTactic::UnfoldProposition(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::Witness(_)
                    | ProofTactic::LetSatisfy(_)
                    | ProofTactic::Choose(_)
                    | ProofTactic::CheckTerminationLocal(_)
                    | ProofTactic::CheckTerminationComponent { .. }
                    | ProofTactic::CheckTerminationCallbacks
                    | ProofTactic::Known
                    | ProofTactic::Normalize
                    | ProofTactic::ArithmeticUsing(_)
                    | ProofTactic::Preserve(_)
                    | ProofTactic::CloseBounds(_)
                    | ProofTactic::NormalizeUsing(_)
                    | ProofTactic::CompatibilityNormalize(_)
                    | ProofTactic::Intro
                    | ProofTactic::IntroAs(_)
                    | ProofTactic::IntroBinder(_)
                    | ProofTactic::Enumerate
                    | ProofTactic::Contradiction(_)
                    | ProofTactic::Rewrite(_)
                    | ProofTactic::CompatibilityFactTransport { .. }
                    | ProofTactic::Instantiate { .. }
            ),
            Self::ExecutionFrontier => matches!(
                tactic,
                ProofTactic::Mark(_)
                    | ProofTactic::Step
                    | ProofTactic::StepContract(_)
                    | ProofTactic::StepBind(_)
                    | ProofTactic::StepCall(_)
                    | ProofTactic::UserTactic(_)
                    | ProofTactic::CompatibilityFactTransport { .. }
                    | ProofTactic::UnfoldProposition(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::UnfoldResource(_)
                    | ProofTactic::UnfoldWitnesses { .. }
                    | ProofTactic::FoldResource(_)
                    | ProofTactic::ReleaseView(_)
                    | ProofTactic::ObserveResource(_)
                    | ProofTactic::Iterated(_)
                    | ProofTactic::Instantiate { .. }
                    | ProofTactic::ApplyFactUsing { .. }
                    | ProofTactic::ApplyTheoremUsing { .. }
            ),
            Self::PostExecution => matches!(
                tactic,
                ProofTactic::UserTactic(_)
                    | ProofTactic::FoldResource(_)
                    | ProofTactic::UnfoldResource(_)
                    | ProofTactic::UnfoldProposition(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::ApplyFactUsing { .. }
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::Choose(_)
                    | ProofTactic::LetSatisfy(_)
                    | ProofTactic::Instantiate { .. }
                    | ProofTactic::Witness(_)
                    | ProofTactic::Intro
                    | ProofTactic::IntroAs(_)
                    | ProofTactic::IntroBinder(_)
                    | ProofTactic::Known
                    | ProofTactic::Enumerate
                    | ProofTactic::Normalize
                    | ProofTactic::CloseBounds(_)
                    | ProofTactic::NormalizeUsing(_)
                    | ProofTactic::CompatibilityNormalize(_)
                    | ProofTactic::ArithmeticUsing(_)
                    | ProofTactic::Preserve(_)
                    | ProofTactic::Rewrite(_)
                    | ProofTactic::CompatibilityFactTransport { .. }
            ),
        }
    }

    /// The checked step for `tactic` when this context admits it as a leaf.
    pub(in crate::surface::proof) fn leaf_step(self, tactic: &ProofTactic) -> Option<ProofStep> {
        if self.admits_leaf(tactic) {
            ProofStep::from_leaf_tactic(tactic)
        } else {
            None
        }
    }

    /// Whether this context runs `tactic` at all, as a leaf or through its
    /// own checked transition. At an execution frontier the linear
    /// continuation hands the first tactic outside this set, with its
    /// suffix, to the outcome driver; an arm refuses it. A pure goal's
    /// structured tactics are interpreted by the script that owns the goal,
    /// so only its leaves are listed here. After execution, the structured
    /// and smart tactics not yet listed here are still converted by
    /// `flat_post_execution_tactic`.
    pub(in crate::surface::proof) fn admits(self, tactic: &ProofTactic) -> bool {
        self.admits_leaf(tactic)
            || match self {
                Self::PureGoal | Self::PostExecution => false,
                Self::ExecutionFrontier => matches!(
                    tactic,
                    ProofTactic::CloseInvariants
                        | ProofTactic::CloseInvariantsBy(_)
                        | ProofTactic::Choose(_)
                        | ProofTactic::LetSatisfy(_)
                        | ProofTactic::StepProved { .. }
                        | ProofTactic::ApplyFact(_)
                        | ProofTactic::ApplyTheorem(_)
                        | ProofTactic::Transport { .. }
                        | ProofTactic::Have(_)
                        | ProofTactic::ExecuteUntil(_)
                        | ProofTactic::SmartExecute
                        | ProofTactic::Loop(_)
                ),
            }
    }
}
