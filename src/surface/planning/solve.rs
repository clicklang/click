//! Certificate and equality-rewrite planning for `solve`.

#[cfg(test)]
use crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::surface::*;

pub(in crate::surface) fn computes_with_known(goal: &Proposition) -> bool {
    match goal {
        Proposition::And(left, right) => computes_with_known(left) && computes_with_known(right),
        Proposition::Or(left, right) => computes_with_known(left) || computes_with_known(right),
        _ => crate::kernel::proof::fact_reasoning::computes_leaf(goal),
    }
}

/// Choose a goal-local closer when the ordinary checker can compute it.
pub(in crate::surface) fn plan_context_free_closer(goal: &Proposition) -> Option<ProofTactic> {
    computes_with_known(goal).then_some(ProofTactic::Known)
}

/// The single explicit-certificate search shared by every smart-simplification
/// construction path. Both the fixed-state proof `close() using` chain and the
/// post-execution outcome planner must call through here, so a named simple
/// rule available to one is available to the other. `is_available` is the
/// caller's judgment of when the current goal closes by `known`.
#[cfg(test)]
pub(in crate::surface) fn plan_explicit_equality_rewrites_from(
    goal: &Proposition,
    premises: &[(Proposition, SyntaxProposition)],
    available: &[Proposition],
    is_available: &impl Fn(&Proposition) -> bool,
    closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    fn reverse_equality(
        kernel: &Proposition,
        surface: &SyntaxProposition,
    ) -> Option<(Proposition, SyntaxProposition)> {
        let kernel = match kernel {
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    OldConditionTerm::Compare {
                        format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    _,
                )) = condition_source_0.old_condition() =>
            {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: *format,
                        relation: CompareRelation::Equal,
                        left: right.clone(),
                        right: left.clone(),
                    },
                    true,
                )
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    _,
                )) = condition_source_0.old_condition() =>
            {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: right.clone(),
                        right: left.clone(),
                    },
                    true,
                )
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((OldConditionTerm::PointerEqual(left, right), _)) =
                    condition_source_0.old_condition() =>
            {
                Proposition::condition_is(
                    OldConditionTerm::PointerEqual(right.clone(), left.clone()),
                    true,
                )
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((OldConditionTerm::AddressEqual(left, right), _)) =
                    condition_source_0.old_condition() =>
            {
                Proposition::condition_is(
                    OldConditionTerm::AddressEqual(right.clone(), left.clone()),
                    true,
                )
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((OldConditionTerm::AddressOffsetEqual(left, right), _)) =
                    condition_source_0.old_condition() =>
            {
                Proposition::condition_is(
                    OldConditionTerm::AddressOffsetEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
                Proposition::Equal(
                    Term::Algebraic(right.clone()),
                    Term::Algebraic(left.clone()),
                )
            }
            _ => return None,
        };
        let SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface
        else {
            return None;
        };
        Some((
            kernel,
            SyntaxProposition::Comparison {
                left: right.clone(),
                operator: ComparisonOperator::Equal,
                right: left.clone(),
            },
        ))
    }

    fn search(
        current: Proposition,
        premises: &[(Proposition, SyntaxProposition)],
        available: &[Proposition],
        used: &mut [bool],
        tactics: &mut Vec<ProofTactic>,
        is_available: &impl Fn(&Proposition) -> bool,
        closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
    ) -> bool {
        // The search tries premise orders depth first, so its node count is
        // factorial in the equalities it may use. Each node observes the
        // enclosing tactic's deadline and work budget, so a search that
        // cannot close fails when its tactic's bound runs out rather than
        // running on to finish.
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        if is_available(&current) {
            tactics.push(ProofTactic::Known);
            return true;
        }
        if let Some(closer) = plan_context_free_closer(&current) {
            tactics.push(closer);
            return true;
        }
        if let Some(suffix) = closer(&current) {
            tactics.extend(suffix);
            return true;
        }
        // A disjunction closes the way `known` closes it: one
        // disjunct must be the same total boolean condition as an
        // available fact up to polarity (`x > 0` from `not (x <= 0)`).
        // Construction mirrors exactly that rule, and commits only
        // when a disjunct closes, so nothing beyond the two children is
        // examined.
        if let Proposition::Or(left_child, right_child) = &current {
            for child in [left_child.as_ref(), right_child.as_ref()] {
                if available
                    .iter()
                    .any(|fact| condition_polarity_equivalent(fact, child))
                {
                    tactics.push(ProofTactic::Known);
                    return true;
                }
            }
        }
        for (index, (kernel, surface)) in premises.iter().enumerate() {
            if used[index] {
                continue;
            }
            let mut orientations = vec![(kernel.clone(), surface.clone())];
            if let Some(reverse) = reverse_equality(kernel, surface) {
                orientations.push(reverse);
            }
            for (oriented_kernel, oriented_surface) in orientations {
                let Ok(rewritten) =
                    rewrite_proposition_by_exact_equality(&current, &oriented_kernel, available)
                else {
                    continue;
                };
                used[index] = true;
                tactics.push(ProofTactic::Rewrite(oriented_surface));
                if search(
                    rewritten,
                    premises,
                    available,
                    used,
                    tactics,
                    is_available,
                    closer,
                ) {
                    return true;
                }
                tactics.pop();
                used[index] = false;
            }
        }
        false
    }

    let mut used = vec![false; premises.len()];
    let mut tactics = Vec::new();
    search(
        goal.clone(),
        premises,
        available,
        &mut used,
        &mut tactics,
        is_available,
        closer,
    )
    .then_some(tactics)
}

/// The checked kernel evidence behind one successful smart simplification.
/// Search produces this at the moment it succeeds and immediately writes it
/// as explicit surface tactics; it is never stored, ordered into a plan, or
/// checked as a private operation program. A derivation the surface
/// vocabulary cannot write is a search failure, not a lowering error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum SolveEvidence {
    /// A goal-local computation may produce a checked certificate.
    GoalLocal,
    /// A kernel derivation of the goal from its context premises.
    Derivation(PropositionDerivation),
}

pub(in crate::surface) fn plan_solve_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Option<SolveEvidence> {
    if matches!(
        normalize_proposition(proposition),
        NormalizedProposition::True
    ) {
        Some(SolveEvidence::GoalLocal)
    } else {
        Some(SolveEvidence::Derivation(
            crate::kernel::search::ProofSearch::derive_solve_proposition(assumptions, proposition)?,
        ))
    }
}

/// Generated termination dependencies are planned inside normal bounded solve;
/// every selected operation is retained as a Source certificate step.
pub(in crate::surface) fn plan_termination(
    scope: &crate::kernel::OrdinaryTerminationScope,
    goal: &Proposition,
    facts: &crate::kernel::proof::PureFactStore,
) -> Result<Vec<crate::kernel::TerminationCheck>, ClickError> {
    check_verification_deadline()?;
    let plan = scope.plan(goal, facts);
    check_verification_deadline()?;
    plan.map_err(ClickError::new)
}
