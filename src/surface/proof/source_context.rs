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
    /// linear continuation, a focused execution arm, a loop's `preserve`
    /// body and a linear `open` scope.
    ExecutionFrontier,
    /// A path that has reached the function exit, where a tactic runs once
    /// per concrete outcome.
    PostExecution,
}

impl SourceContext {
    /// Whether this context runs `tactic` as one checked leaf step.
    fn admits_leaf(self, tactic: &ProofTactic) -> bool {
        match self {
            Self::PureGoal => matches!(
                tactic,
                ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::Induct { .. }
                    | ProofTactic::ApplyInductionUsing { .. }
                    | ProofTactic::UnfoldPredicate(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::PeelFunction { .. }
                    | ProofTactic::Witness(_)
                    | ProofTactic::LetSatisfy(_)
                    | ProofTactic::Choose(_)
                    | ProofTactic::Assumption
                    | ProofTactic::Extract(_)
                    | ProofTactic::Normalize
                    | ProofTactic::ArithmeticUsing(_)
                    | ProofTactic::ArithmeticCertificate(_)
                    | ProofTactic::NormalizeUsing(_)
                    | ProofTactic::Intro
                    | ProofTactic::IntroAs(_)
                    | ProofTactic::Enumerate
                    | ProofTactic::Contradiction(_)
                    | ProofTactic::Rewrite(_)
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::InstantiateUsing { .. }
            ),
            Self::ExecutionFrontier => matches!(
                tactic,
                ProofTactic::Mark(_)
                    | ProofTactic::Step
                    | ProofTactic::StepContract(_)
                    | ProofTactic::StepBind(_)
                    | ProofTactic::StepCall(_)
                    | ProofTactic::UserTactic(_)
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::UnfoldPredicate(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::PeelFunction { .. }
                    | ProofTactic::UnfoldResource(_)
                    | ProofTactic::UnfoldWitnesses { .. }
                    | ProofTactic::FoldResource(_)
                    | ProofTactic::ObserveResource(_)
                    | ProofTactic::Iterated(_)
                    | ProofTactic::ApplyTheoremUsing { .. }
            ),
            Self::PostExecution => matches!(
                tactic,
                ProofTactic::FoldResource(_)
                    | ProofTactic::UnfoldResource(_)
                    | ProofTactic::ConstructResource(_)
                    | ProofTactic::UnfoldPredicate(_)
                    | ProofTactic::UnfoldFunction(_)
                    | ProofTactic::PeelFunction { .. }
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::Choose(_)
                    | ProofTactic::LetSatisfy(_)
                    | ProofTactic::Witness(_)
                    | ProofTactic::Intro
                    | ProofTactic::IntroAs(_)
                    | ProofTactic::Assumption
                    | ProofTactic::Normalize
                    | ProofTactic::NormalizeUsing(_)
                    | ProofTactic::ArithmeticUsing(_)
                    | ProofTactic::ArithmeticCertificate(_)
                    | ProofTactic::Rewrite(_)
                    | ProofTactic::TransportUsing { .. }
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
                        | ProofTactic::ApplyTheorem(_)
                        | ProofTactic::Transport { .. }
                        | ProofTactic::Have(_)
                        | ProofTactic::Extract(_)
                        | ProofTactic::ExecuteUntil(_)
                        | ProofTactic::SmartExecute
                        | ProofTactic::Loop(_)
                ),
            }
    }
}
