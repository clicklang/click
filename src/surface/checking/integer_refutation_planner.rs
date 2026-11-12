//! Plan a mathematical `Integer` bound by refuting its negation.
//!
//! The goal's integer negation and the selected premises become linear
//! constraints for the simplex (`simplex.rs`). An infeasible system yields
//! Farkas multipliers, which become an ordinary `Integer` certificate:
//! premise and `negated_goal` nodes, scaled and added up to a constant
//! contradiction. The kernel checks that certificate; nothing here is
//! trusted.

use super::simplex::{self, Constraint, FarkasTerm, Rational, Relation, SimplexOutcome};
use crate::kernel::machine_integer::bounds::operation_bound;
use crate::kernel::proof::integer_arithmetic::{
    IntegerAffineAtom, IntegerAffineClaim, IntegerAffineRelation, IntegerArithmeticCertificate,
    IntegerArithmeticNode, add_claim, excluded_type_bound, integer_affine_claim,
    integer_affine_claims, integer_disequality_claims, machine_type_range_claim, negate_claim,
    scale_claim,
};
use crate::kernel::{IntegerTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// The result of a refutation attempt.
#[derive(Debug)]
pub(crate) enum IntegerRefutation {
    /// A certificate for the goal. Its premise nodes index `premises`, the
    /// premises the refutation used, in the order the caller passed them.
    Proved {
        certificate: IntegerArithmeticCertificate,
        premises: Vec<Proposition>,
    },
    /// The premises and the negated goal have a rational solution, given as
    /// atom values. The goal does not follow from these premises by linear
    /// arithmetic. The `solve` diagnostics (stage-1 milestone 5) will report
    /// it; until then only the tests read the values.
    #[cfg_attr(not(test), allow(dead_code))]
    Counterexample(Vec<(IntegerAffineAtom, Rational)>),
    /// The goal is not a mathematical `Integer` bound this planner refutes.
    Outside,
    /// The work budget ran out.
    Exhausted,
}

/// Refute the integer negation of `goal` from `premises`. Premises that are
/// not linear `Integer` claims are ignored. Work is charged to the active
/// deterministic budget.
#[cfg(test)]
pub(super) fn plan_integer_refutation(
    goal: &Proposition,
    premises: &[Proposition],
) -> IntegerRefutation {
    plan_integer_refutation_with_ranges(goal, premises, &[])
}

/// Where one constraint of the refutation comes from.
#[derive(Clone, Copy)]
enum Source {
    NegatedGoal,
    Premise(usize),
    /// The type range of `ranges[index]`; `upper` selects its maximum.
    Range {
        index: usize,
        upper: bool,
    },
    /// The bound `operations[index]`, an unsigned quotient, shift, or
    /// remainder by a constant, takes from its operand.
    Operation {
        index: usize,
        upper: bool,
    },
    /// The bound premise `index`, a disequality with a type endpoint, gives.
    Excluded(usize),
    /// Constraint `bound`, a non-strict premise or the negated goal `t <= 0`,
    /// made strict, `t + 1 <= 0`, by premise `disequal`, `l != r` with
    /// `l - r` equal to `t` or `-t`.
    Strict {
        bound: usize,
        disequal: usize,
    },
}

/// As [`plan_integer_refutation`], also using the type range of each machine
/// observation in `ranges` (each an `IntegerTerm::Machine`). A range the
/// refutation uses becomes a `TypeRange` node, which needs no premise. When
/// `ranges` is not empty, each unsigned quotient, shift, or remainder by a
/// constant among the constraints' terms is also bounded by its operand
/// (`OperationBound`), and each premise that is a disequality with a type
/// endpoint gives its bound (`ExcludedTypeBound`).
pub(super) fn plan_integer_refutation_with_ranges(
    goal: &Proposition,
    premises: &[Proposition],
    ranges: &[IntegerTerm],
) -> IntegerRefutation {
    let Some(goal_claim) = integer_affine_claim(goal) else {
        return IntegerRefutation::Outside;
    };
    // The bounds an operation's meaning or a disequality with a type
    // endpoint gives come with the type ranges, on the caller's retry that
    // asks for them; a refutation from the facts alone keeps its certificate.
    let bounds = !ranges.is_empty();
    // A goal with no atoms that does not hold, such as `false`, is proved
    // by refuting the premises alone: the kernel accepts a contradiction for
    // any supported goal, so its negation adds no constraint.
    let contradiction = goal_claim.terms.is_empty()
        && match goal_claim.relation {
            IntegerAffineRelation::LessEqual => goal_claim.constant.is_positive(),
            IntegerAffineRelation::Equal => !goal_claim.constant.is_zero(),
        };
    if !contradiction && goal_claim.relation != IntegerAffineRelation::LessEqual {
        return IntegerRefutation::Outside;
    }

    // The negated goal, when there is one, is the first constraint; the
    // usable premises follow.
    let mut sources: Vec<Source> = Vec::new();
    let mut claims: Vec<IntegerAffineClaim> = Vec::new();
    if !contradiction {
        let mut negated = negate_claim(&goal_claim, IntegerAffineRelation::LessEqual);
        negated.constant += BigInt::one();
        sources.push(Source::NegatedGoal);
        claims.push(negated);
    }
    for (index, premise) in premises.iter().enumerate() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return IntegerRefutation::Exhausted;
        }
        for claim in integer_affine_claims(premise) {
            sources.push(Source::Premise(index));
            claims.push(claim);
        }
        if bounds
            && let Some(claim) =
                excluded_type_bound(premise).and_then(|bound| integer_affine_claim(&bound))
        {
            sources.push(Source::Excluded(index));
            claims.push(claim);
        }
    }
    for (index, value) in ranges.iter().enumerate() {
        let IntegerTerm::Machine(machine) = value else {
            continue;
        };
        for upper in [false, true] {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return IntegerRefutation::Exhausted;
            }
            if let Some(claim) = machine_type_range_claim(machine, upper) {
                sources.push(Source::Range { index, upper });
                claims.push(claim);
            }
        }
    }

    // Each unsigned quotient, shift, or remainder by a constant among the
    // constraints' atoms is bounded by its operand. A bound can name a new
    // operand atom, itself such an operation (`x / 1000 / 1000`), so the
    // atoms are visited as a worklist, each once.
    let mut operations: Vec<crate::kernel::SharedMachineIntegerTerm> = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut next = if bounds { 0 } else { claims.len() };
    while next < claims.len() {
        let machines = claims[next]
            .terms
            .keys()
            .filter_map(|atom| match atom {
                IntegerAffineAtom::Machine(machine) => Some(machine.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        next += 1;
        for machine in machines {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return IntegerRefutation::Exhausted;
            }
            if !visited.insert(machine.id()) {
                continue;
            }
            let bounds = [false, true]
                .into_iter()
                .filter_map(|upper| {
                    Some((
                        upper,
                        integer_affine_claim(&operation_bound(&machine, upper)?)?,
                    ))
                })
                .collect::<Vec<_>>();
            if bounds.is_empty() {
                continue;
            }
            let index = operations.len();
            operations.push(machine);
            for (upper, claim) in bounds {
                sources.push(Source::Operation { index, upper });
                claims.push(claim);
            }
        }
    }

    let mut atoms: BTreeMap<IntegerAffineAtom, usize> = BTreeMap::new();
    let constraints: Vec<Constraint> = claims
        .iter()
        .map(|claim| Constraint {
            terms: claim
                .terms
                .iter()
                .map(|(atom, coefficient)| {
                    let next = atoms.len();
                    (
                        *atoms.entry(atom.clone()).or_insert(next),
                        coefficient.clone(),
                    )
                })
                .collect(),
            constant: claim.constant.clone(),
            relation: match claim.relation {
                IntegerAffineRelation::LessEqual => Relation::LessEqual,
                IntegerAffineRelation::Equal => Relation::Equal,
            },
        })
        .collect();

    let mut outcome = simplex::solve(atoms.len(), &constraints, |units| {
        !crate::instrumentation::deadline_exceeded_with_work(units)
    });
    // A disequality is no linear constraint, so it joins only after the
    // linear system alone leaves a counterexample: each premise `l != r`
    // makes strict a premise or negated-goal bound of the same difference,
    // found by one lookup in an index of those bounds. A refutation without
    // one keeps its certificate.
    if matches!(outcome, SimplexOutcome::Feasible(_)) {
        let base = claims.len();
        let mut bounds: std::collections::HashMap<_, Vec<usize>> = std::collections::HashMap::new();
        for (position, (claim, source)) in claims.iter().zip(&sources).enumerate() {
            if claim.relation == IntegerAffineRelation::LessEqual
                && !claim.terms.is_empty()
                && matches!(source, Source::NegatedGoal | Source::Premise(_))
            {
                bounds
                    .entry((claim.terms.clone(), claim.constant.clone()))
                    .or_default()
                    .push(position);
            }
        }
        if !bounds.is_empty() {
            for (index, premise) in premises.iter().enumerate() {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return IntegerRefutation::Exhausted;
                }
                for difference in integer_disequality_claims(premise) {
                    let negated = negate_claim(&difference, IntegerAffineRelation::Equal);
                    for key in [
                        (difference.terms, difference.constant),
                        (negated.terms, negated.constant),
                    ] {
                        for position in bounds.get(&key).into_iter().flatten() {
                            if crate::instrumentation::deadline_exceeded_with_work(1) {
                                return IntegerRefutation::Exhausted;
                            }
                            let mut strict = claims[*position].clone();
                            strict.constant += BigInt::one();
                            sources.push(Source::Strict {
                                bound: *position,
                                disequal: index,
                            });
                            claims.push(strict);
                        }
                    }
                }
            }
        }
        if claims.len() > base {
            let strict = claims[base..].iter().map(|claim| Constraint {
                terms: claim
                    .terms
                    .iter()
                    .map(|(atom, coefficient)| (atoms[atom], coefficient.clone()))
                    .collect(),
                constant: claim.constant.clone(),
                relation: Relation::LessEqual,
            });
            let constraints = constraints
                .iter()
                .cloned()
                .chain(strict)
                .collect::<Vec<_>>();
            outcome = simplex::solve(atoms.len(), &constraints, |units| {
                !crate::instrumentation::deadline_exceeded_with_work(units)
            });
        }
    }
    let terms = match outcome {
        SimplexOutcome::Infeasible(terms) => terms,
        SimplexOutcome::Feasible(model) => {
            let mut by_index: Vec<Option<IntegerAffineAtom>> = vec![None; atoms.len()];
            for (atom, index) in atoms {
                by_index[index] = Some(atom);
            }
            return IntegerRefutation::Counterexample(
                model
                    .into_iter()
                    .filter_map(|(index, value)| Some((by_index[index].clone()?, value)))
                    .collect(),
            );
        }
        SimplexOutcome::Exhausted => return IntegerRefutation::Exhausted,
    };
    match certificate_from_farkas(&terms, &claims, &sources, premises, ranges, &operations) {
        Some(proved) => proved,
        None => IntegerRefutation::Outside,
    }
}

/// Build the certificate: one premise or `negated_goal` node per used
/// constraint, an equality turned into the direction its multiplier's sign
/// selects, each scaled by its multiplier's magnitude, and all of them added.
fn certificate_from_farkas(
    terms: &[FarkasTerm],
    claims: &[IntegerAffineClaim],
    sources: &[Source],
    premises: &[Proposition],
    ranges: &[IntegerTerm],
    operations: &[crate::kernel::SharedMachineIntegerTerm],
) -> Option<IntegerRefutation> {
    let mut nodes: Vec<IntegerArithmeticNode> = Vec::new();
    let mut used_premises: Vec<Proposition> = Vec::new();
    let mut premise_slots: BTreeMap<usize, usize> = BTreeMap::new();
    let mut addends: Vec<(usize, IntegerAffineClaim)> = Vec::new();
    for term in terms {
        let claim = claims.get(term.constraint)?;
        let mut base = nodes.len();
        let mut source_of = *sources.get(term.constraint)?;
        // A strict bound is its non-strict bound's node, then the step.
        let strict = match source_of {
            Source::Strict { bound, disequal } => {
                source_of = *sources.get(bound)?;
                Some((claims.get(bound)?, disequal))
            }
            _ => None,
        };
        let node_claim = strict.map_or(claim, |(bound, _)| bound);
        match source_of {
            Source::Strict { .. } => return None,
            Source::NegatedGoal => nodes.push(IntegerArithmeticNode::NegatedGoal {
                result: node_claim.clone(),
            }),
            Source::Range { index, upper } => nodes.push(IntegerArithmeticNode::TypeRange {
                value: ranges.get(index)?.clone(),
                upper,
                result: node_claim.clone(),
            }),
            Source::Operation { index, upper } => {
                nodes.push(IntegerArithmeticNode::OperationBound {
                    value: IntegerTerm::Machine(operations.get(index)?.clone()),
                    upper,
                    result: node_claim.clone(),
                })
            }
            Source::Excluded(index) => {
                let next = used_premises.len();
                let slot = *premise_slots.entry(index).or_insert_with(|| {
                    used_premises.push(premises[index].clone());
                    next
                });
                nodes.push(IntegerArithmeticNode::ExcludedTypeBound {
                    index: slot,
                    result: node_claim.clone(),
                });
            }
            Source::Premise(index) => {
                let next = used_premises.len();
                let slot = *premise_slots.entry(index).or_insert_with(|| {
                    used_premises.push(premises[index].clone());
                    next
                });
                nodes.push(IntegerArithmeticNode::Premise {
                    index: slot,
                    result: node_claim.clone(),
                });
            }
        }
        if let Some((_, disequal)) = strict {
            let next = used_premises.len();
            let slot = *premise_slots.entry(disequal).or_insert_with(|| {
                used_premises.push(premises[disequal].clone());
                next
            });
            nodes.push(IntegerArithmeticNode::StrictFromDisequal {
                bound: base,
                disequal: slot,
                result: claim.clone(),
            });
            base = nodes.len() - 1;
        }
        let (mut source, mut current) = (base, claim.clone());
        if claim.relation == IntegerAffineRelation::Equal {
            let reverse = term.multiplier.is_negative();
            let bound = if reverse {
                negate_claim(claim, IntegerAffineRelation::LessEqual)
            } else {
                IntegerAffineClaim {
                    relation: IntegerAffineRelation::LessEqual,
                    terms: claim.terms.clone(),
                    constant: claim.constant.clone(),
                }
            };
            nodes.push(IntegerArithmeticNode::EqualityToLessEqual {
                source,
                reverse,
                result: bound.clone(),
            });
            source = nodes.len() - 1;
            current = bound;
        }
        let magnitude = term.multiplier.abs();
        if !magnitude.is_one() {
            let scaled = scale_claim(&current, &magnitude)?;
            nodes.push(IntegerArithmeticNode::Scale {
                source,
                coefficient: magnitude,
                result: scaled.clone(),
            });
            source = nodes.len() - 1;
            current = scaled;
        }
        addends.push((source, current));
    }
    let mut addends = addends.into_iter();
    let (mut sum_node, mut sum) = addends.next()?;
    for (node, claim) in addends {
        let total = add_claim(&sum, &claim);
        nodes.push(IntegerArithmeticNode::Add {
            left: sum_node,
            right: node,
            result: total.clone(),
        });
        sum_node = nodes.len() - 1;
        sum = total;
    }
    Some(IntegerRefutation::Proved {
        certificate: IntegerArithmeticCertificate {
            nodes,
            conclusion: sum_node,
        },
        premises: used_premises,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ConditionTerm, IntegerTerm, Variable};

    fn x(id: u64) -> IntegerTerm {
        IntegerTerm::Variable(Variable(id))
    }

    fn le(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(left, right), true)
    }

    fn lt(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(left.into(), right.into()),
            true,
        )
    }

    fn eq(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_equal(left, right), true)
    }

    fn c(value: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(value)
    }

    fn proves(goal: &Proposition, premises: &[Proposition]) -> Vec<Proposition> {
        match plan_integer_refutation(goal, premises) {
            IntegerRefutation::Proved {
                certificate,
                premises,
            } => {
                assert_eq!(
                    certificate.check(goal, &premises),
                    Ok(()),
                    "{certificate:?}"
                );
                premises
            }
            other => panic!("expected a proof, got {other:?}"),
        }
    }

    fn ne(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerNotEqual(left.into(), right.into()),
            true,
        )
    }

    #[test]
    fn a_disequality_makes_its_bound_strict_after_a_counterexample() {
        // a <= b, a != b  ⊢  a < b, and through a chain: b <= c ⊢ a < c.
        let (a, b, cc) = (x(21), x(22), x(23));
        let used = proves(
            &lt(a.clone(), b.clone()),
            &[le(a.clone(), b.clone()), ne(b.clone(), a.clone())],
        );
        assert_eq!(used.len(), 2);
        proves(
            &lt(a.clone(), cc.clone()),
            &[
                le(a.clone(), b.clone()),
                ne(a.clone(), b.clone()),
                le(b.clone(), cc.clone()),
            ],
        );
        // The negated goal is a bound too: a != 5 and a <= 5 ⊢ a <= 4.
        proves(
            &le(a.clone(), c(4)),
            &[ne(a.clone(), c(5)), le(a.clone(), c(5))],
        );
        // Each alone, or a disequality of another difference, is no proof.
        for premises in [
            vec![le(a.clone(), b.clone())],
            vec![ne(a.clone(), b.clone())],
            vec![le(a.clone(), b.clone()), ne(a.clone(), cc.clone())],
        ] {
            assert!(
                matches!(
                    plan_integer_refutation(&lt(a.clone(), b.clone()), &premises),
                    IntegerRefutation::Counterexample(_)
                ),
                "{premises:?}"
            );
        }
        // A refutation the linear premises already give keeps its
        // certificate: no strict step is added.
        let IntegerRefutation::Proved { certificate, .. } = plan_integer_refutation(
            &lt(a.clone(), b.clone()),
            &[lt(a.clone(), b.clone()), ne(a.clone(), b.clone())],
        ) else {
            panic!("a strict premise proves the strict goal");
        };
        assert!(
            !certificate
                .nodes
                .iter()
                .any(|node| matches!(node, IntegerArithmeticNode::StrictFromDisequal { .. }))
        );
    }

    #[test]
    fn chains_bounds_and_cites_only_what_it_uses() {
        // i < n, n <= 1000, total <= 255 * i  ⊢  total <= 255000.
        let (i, n, total, unrelated) = (x(1), x(2), x(3), x(4));
        let premises = vec![
            lt(i.clone(), n.clone()),
            le(n, c(1000)),
            le(unrelated, c(7)),
            le(total.clone(), IntegerTerm::multiply(c(255), i)),
        ];
        let goal = le(total, c(255000));
        let used = proves(&goal, &premises);
        assert_eq!(used.len(), 3);
        assert!(!used.contains(&premises[2]));
    }

    #[test]
    fn uses_equalities_in_either_direction() {
        // a == b + c, b == 2, c == 3  ⊢  a <= 5 and 5 <= a.
        let (a, b, cc) = (x(11), x(12), x(13));
        let premises = vec![
            eq(a.clone(), IntegerTerm::add(b.clone(), cc.clone())),
            eq(b, c(2)),
            eq(cc, c(3)),
        ];
        proves(&le(a.clone(), c(5)), &premises);
        proves(&le(c(5), a), &premises);
    }

    #[test]
    fn reports_a_counterexample_when_the_goal_does_not_follow() {
        let (i, n) = (x(21), x(22));
        let premises = vec![le(i.clone(), n.clone()), le(n, c(10))];
        let goal = le(i.clone(), c(9));
        let IntegerRefutation::Counterexample(model) = plan_integer_refutation(&goal, &premises)
        else {
            panic!("expected a counterexample");
        };
        let value = model
            .iter()
            .find(|(atom, _)| *atom == IntegerAffineAtom::Variable(Variable(21)))
            .map(|(_, value)| value.clone())
            .expect("i has a value");
        assert!(value > Rational::integer(BigInt::from(9)));
    }

    #[test]
    fn equality_and_machine_goals_are_outside_this_planner() {
        let goal = eq(x(31), c(1));
        assert!(matches!(
            plan_integer_refutation(&goal, &[]),
            IntegerRefutation::Outside
        ));
    }

    #[test]
    fn a_strict_goal_uses_integer_tightening() {
        // 2x <= 7 does not give x < 3 rationally (x = 3.5), but x <= 3 is
        // integral reasoning the planner does not do yet; x < 4 follows
        // rationally.
        let goal = lt(x(41), c(4));
        proves(&goal, &[le(IntegerTerm::multiply(c(2), x(41)), c(7))]);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/surface/checking/integer_refutation_planner/tests.rs");
    }
}
