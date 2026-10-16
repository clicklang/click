//! Bounded planning for the checked signed-int32 arithmetic certificate.
//!
//! This module is deliberately a planner, not a validation oracle.  It reads
//! only the goal and the exact premise slice supplied by its caller, chooses a
//! finite local derivation, and leaves all semantic validation to the kernel
//! certificate checker.

use crate::kernel::proof::signed_arithmetic::{
    SignedArithmeticAtom, SignedArithmeticCarrier, SignedArithmeticCertificate,
    SignedArithmeticClaim, SignedArithmeticComparison, SignedArithmeticInterval,
    SignedArithmeticNode, SignedArithmeticRelation, add_claim,
};
use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};

const MAX_SELECTED_PREMISES: usize = 64;
const MAX_NODES: usize = 4096;
const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;

pub(in crate::surface) fn plan_signed_arithmetic_certificate(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<SignedArithmeticCertificate> {
    plan_signed_arithmetic_certificate_with_mode(goal, premises, false)
}

/// Explicit `arithmetic() using` may request the extra checked weakening
/// step without changing the certificates chosen by automatic proof search.
pub(in crate::surface) fn plan_signed_arithmetic_certificate_with_weakening(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<SignedArithmeticCertificate> {
    plan_signed_arithmetic_certificate_with_mode(goal, premises, true)
}

/// Plans once from the premises' own bounds, and only when that finds no
/// certificate plans again letting an atom's `int32` range stand in for a
/// bound no premise states (`Planner::int32_range_fallback`). Keeping the
/// range out of the first pass leaves every certificate the planner already
/// found unchanged; the second pass runs only where the first failed, so a
/// miss costs at most one more bounded plan.
fn plan_signed_arithmetic_certificate_with_mode(
    goal: &Proposition,
    premises: &[Proposition],
    allow_weakening: bool,
) -> Option<SignedArithmeticCertificate> {
    if premises.len() > MAX_SELECTED_PREMISES {
        return None;
    }
    // The kernel checks arithmetic atoms in canonical form. A population
    // count may still carry a raw memory read here, while another premise
    // names that same value by its registered load variable.
    let goal = crate::kernel::canonical_condition_fact(goal);
    signed_claim(&goal)?;
    let premises = premises
        .iter()
        .map(crate::kernel::canonical_condition_fact)
        .collect::<Vec<_>>();
    plan_signed_arithmetic_certificate_in_pass(&goal, &premises, allow_weakening, false).or_else(
        || plan_signed_arithmetic_certificate_in_pass(&goal, &premises, allow_weakening, true),
    )
}

fn plan_signed_arithmetic_certificate_in_pass(
    goal: &Proposition,
    premises: &[Proposition],
    allow_weakening: bool,
    int32_range_fallback: bool,
) -> Option<SignedArithmeticCertificate> {
    if premises.len() > MAX_SELECTED_PREMISES {
        return None;
    }
    let expected = signed_claim(goal)?;
    if is_trivial(&expected) {
        return Some(certificate(
            vec![SignedArithmeticNode::Trivial { result: expected }],
            0,
        ));
    }
    charge_claim_comparison(&expected)?;

    let claims = premises
        .iter()
        .enumerate()
        .filter_map(|(index, proposition)| {
            charge_work(1)?;
            signed_claim(proposition).map(|claim| (index, claim))
        })
        .collect::<Vec<_>>();

    for (index, claim) in &claims {
        charge_claim_comparison(claim)?;
        if claim == &expected {
            return Some(certificate(
                vec![SignedArithmeticNode::Premise {
                    index: *index,
                    result: claim.clone(),
                }],
                0,
            ));
        }
    }
    if comparison_terms(goal).is_some_and(|(left, right, _)| {
        is_affine_planning_atom(left) && is_affine_planning_atom(right)
    }) && let Some(plan) = plan_affine_from_selected_claims(
        premises,
        &claims,
        &expected,
        allow_weakening,
        int32_range_fallback,
    ) {
        return Some(plan);
    }
    if !int32_range_fallback && let Some(plan) = plan_affine_one_premise(&claims, &expected) {
        return Some(plan);
    }
    if let Some(plan) = plan_machine_affine_goal(goal, premises, &claims, int32_range_fallback) {
        return Some(plan);
    }
    if let Some(plan) = plan_interval_goal(goal, premises, &claims, int32_range_fallback) {
        return Some(plan);
    }
    plan_affine_with_checked_premises(
        goal,
        premises,
        &claims,
        &expected,
        allow_weakening,
        int32_range_fallback,
    )
}

fn plan_affine_with_checked_premises(
    goal: &Proposition,
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
    expected: &SignedArithmeticClaim,
    allow_weakening: bool,
    int32_range_fallback: bool,
) -> Option<SignedArithmeticCertificate> {
    // Keep the original opaque claims while proving every operation's
    // definedness. No premise may justify its own decomposition circularly.
    let (left, right, _) = comparison_terms(goal)?;
    let compound_goal = !is_affine_planning_atom(left) || !is_affine_planning_atom(right);
    let mut evidence = Planner::new(premises, claims, int32_range_fallback);
    // A goal operation is defined from the original facts where they bound
    // it. A converted affine premise is not its own definedness evidence,
    // but once converted from the original facts it may bound the goal's
    // operands, as `a == b + 1` with `b` bounded bounds `a` in `a - 1`; that
    // evidence is built after the conversions below.
    let goal_intervals = |planner: &mut Planner<'_>| -> Option<(Option<usize>, Option<usize>)> {
        let (left, right) = affine_operation_terms(goal)?;
        let left = match left {
            Some(term) => Some(planner.build_interval_for_affine(term)?),
            None => None,
        };
        let right = match right {
            Some(term) => Some(planner.build_interval_for_affine(term)?),
            None => None,
        };
        Some((left, right))
    };
    let (expected, goal_evidence) = if compound_goal {
        (
            decomposed_signed_claim(goal)?,
            Some(goal_intervals(&mut evidence)),
        )
    } else {
        (expected.clone(), None)
    };
    // Each pass converts the premises whose operations the facts so far
    // bound: the original ones, and those converted by earlier passes, so
    // `c == a + 1` converts once `a == b + 1` has bounded `a`. A premise's
    // own conversion never reads itself converted. At most one pass per
    // premise, and none after a pass that converts nothing.
    let mut decomposed = claims.to_vec();
    let mut converted = vec![false; claims.len()];
    let (mut nodes, mut intervals, mut premise_cache) =
        (evidence.nodes, evidence.intervals, evidence.premise_cache);
    for _ in 0..claims.len() {
        let mut planner = Planner::new(premises, &decomposed, int32_range_fallback);
        planner.nodes = nodes;
        planner.intervals = intervals;
        planner.premise_cache = premise_cache;
        let mut conversions = Vec::new();
        for (position, (index, claim)) in claims.iter().enumerate() {
            charge_work(1)?;
            if converted[position] {
                continue;
            }
            let conversion = (|| {
                let proposition = &premises[*index];
                let (left, right) = affine_operation_terms(proposition)?;
                let result = decomposed_signed_claim(proposition)?;
                let left_evidence = match left {
                    Some(term) => Some(planner.build_interval_for_affine(term)?),
                    None => None,
                };
                let right_evidence = match right {
                    Some(term) => Some(planner.build_interval_for_affine(term)?),
                    None => None,
                };
                let left_evidence = left_evidence.or(right_evidence)?;
                let right_evidence = right_evidence.unwrap_or(left_evidence);
                let source = planner.premise(*index, claim)?;
                let node = planner.push(SignedArithmeticNode::AffinePremise {
                    source,
                    left_evidence,
                    right_evidence,
                    result: result.clone(),
                })?;
                Some((result, node))
            })();
            if let Some((result, node)) = conversion {
                conversions.push((position, *index, result, node));
            }
        }
        (nodes, intervals, premise_cache) =
            (planner.nodes, planner.intervals, planner.premise_cache);
        if conversions.is_empty() {
            break;
        }
        // The next pass, and the affine phase, read these conversions.
        for (position, index, result, node) in conversions {
            decomposed[position] = (index, result);
            converted[position] = true;
            premise_cache.insert(index, node);
        }
    }
    if !converted.contains(&true) {
        return None;
    }
    let mut planner = Planner::new(premises, &decomposed, int32_range_fallback);
    planner.nodes = nodes;
    planner.intervals = intervals;
    planner.premise_cache = premise_cache;
    let goal_evidence = match goal_evidence {
        Some(Some(evidence)) => Some(evidence),
        Some(None) => Some(goal_intervals(&mut planner)?),
        None => None,
    };
    let source = planner.affine_claim_or_bounds(&expected, allow_weakening)?;
    let conclusion = match goal_evidence {
        Some((left, right)) => affine_conclusion(&mut planner, goal, source, left, right)?,
        None => source,
    };
    Some(certificate(planner.nodes, conclusion))
}

fn plan_affine_from_selected_claims(
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
    expected: &SignedArithmeticClaim,
    allow_weakening: bool,
    int32_range_fallback: bool,
) -> Option<SignedArithmeticCertificate> {
    let mut planner = Planner::new(premises, claims, int32_range_fallback);
    let conclusion = planner.affine_claim_or_bounds(expected, allow_weakening)?;
    Some(certificate(planner.nodes, conclusion))
}

/// Classifies one explicitly named premise without trying to prove a goal.
///
/// Callers that assemble an exact premise slice must not invoke the planner
/// with a fabricated goal: a context-free/trivial goal can succeed while the
/// cited premise is completely unrelated.  Keep this predicate bounded and
/// syntactic; the actual certificate remains the kernel's authority.
pub(in crate::surface) fn signed_arithmetic_premise_supported(proposition: &Proposition) -> bool {
    signed_claim(proposition).is_some_and(|claim| charge_claim_comparison(&claim).is_some())
}

fn certificate(nodes: Vec<SignedArithmeticNode>, conclusion: usize) -> SignedArithmeticCertificate {
    SignedArithmeticCertificate { nodes, conclusion }
}

fn charge_work(units: usize) -> Option<()> {
    (!crate::instrumentation::deadline_exceeded_with_work(units.max(1))).then_some(())
}

fn signed_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    let (relation, left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Constant(constant), value) => {
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms: BTreeMap::new(),
                constant: if *constant == value {
                    BigInt::zero()
                } else {
                    BigInt::one()
                },
            });
        }
        _ => return None,
    };
    let (terms, mut constant) = affine_difference(left, right)?;
    if strict {
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

pub(in crate::surface) fn decomposed_signed_claim(
    proposition: &Proposition,
) -> Option<SignedArithmeticClaim> {
    let canonical = crate::kernel::canonical_condition_fact(proposition);
    let proposition = &canonical;
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    let (relation, left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            let (terms, constant) = decomposed_affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            let (terms, constant) = decomposed_affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        _ => return None,
    };
    let (terms, mut constant) = decomposed_affine_difference(left, right)?;
    if strict {
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

fn affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        charge_work(coefficient.bits() as usize + 1)?;
        if let Bitvector32Term::Constant(value) = term {
            let value = BigInt::from(*value as i32);
            charge_bigint_binary_work(&coefficient, &value)?;
            let product = &coefficient * &value;
            charge_bigint_binary_work(&constant, &product)?;
            constant += product;
        } else {
            let atom = SignedArithmeticAtom::from_term(term)?;
            charge_map_update_work(terms.len(), &atom, &coefficient)?;
            let previous = terms.get(&atom).cloned().unwrap_or_default();
            charge_bigint_binary_work(&previous, &coefficient)?;
            let updated = previous + coefficient;
            if updated.is_zero() {
                terms.remove(&atom);
            } else {
                terms.insert(atom, updated);
            }
        }
    }
    Some((terms, constant))
}

fn decomposed_affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        charge_work(coefficient.bits() as usize + 1)?;
        match term {
            Bitvector32Term::Constant(value) => {
                let value = BigInt::from(*value as i32);
                charge_bigint_binary_work(&coefficient, &value)?;
                let product = &coefficient * &value;
                charge_bigint_binary_work(&constant, &product)?;
                constant += product;
            }
            Bitvector32Term::Add(left, right) => {
                pending.push((right, coefficient.clone()));
                pending.push((left, coefficient));
            }
            Bitvector32Term::Subtract(left, right) => {
                pending.push((right, -coefficient.clone()));
                pending.push((left, coefficient));
            }
            // The kernel decomposes a conversion only through interval
            // evidence that its operand is inside the destination range.
            Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            } if crate::kernel::proof::signed_arithmetic::narrowed_word_cast(
                *source,
                *destination,
            ) =>
            {
                pending.push((value, coefficient));
            }
            Bitvector32Term::Multiply(left, right) => {
                if let Some(value) = left.as_const() {
                    let value = BigInt::from(value as i32);
                    let scaled = coefficient.clone() * &value;
                    charge_bigint_binary_work(&coefficient, &value)?;
                    pending.push((right, scaled));
                } else if let Some(value) = right.as_const() {
                    let value = BigInt::from(value as i32);
                    let scaled = coefficient.clone() * &value;
                    charge_bigint_binary_work(&coefficient, &value)?;
                    pending.push((left, scaled));
                } else {
                    let atom = SignedArithmeticAtom::from_term(term)?;
                    charge_map_update_work(terms.len(), &atom, &coefficient)?;
                    let previous = terms.get(&atom).cloned().unwrap_or_default();
                    let updated = previous + coefficient;
                    if updated.is_zero() {
                        terms.remove(&atom);
                    } else {
                        terms.insert(atom, updated);
                    }
                }
            }
            _ => {
                let atom = SignedArithmeticAtom::from_term(term)?;
                charge_map_update_work(terms.len(), &atom, &coefficient)?;
                let previous = terms.get(&atom).cloned().unwrap_or_default();
                charge_bigint_binary_work(&previous, &coefficient)?;
                let updated = previous + coefficient;
                if updated.is_zero() {
                    terms.remove(&atom);
                } else {
                    terms.insert(atom, updated);
                }
            }
        }
    }
    Some((terms, constant))
}

fn is_trivial(claim: &SignedArithmeticClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            SignedArithmeticRelation::LessEqual => claim.constant <= BigInt::zero(),
            SignedArithmeticRelation::Equal => claim.constant.is_zero(),
            SignedArithmeticRelation::Disequal => !claim.constant.is_zero(),
        }
}

fn plan_affine_one_premise(
    claims: &[(usize, SignedArithmeticClaim)],
    expected: &SignedArithmeticClaim,
) -> Option<SignedArithmeticCertificate> {
    for (index, source) in claims {
        charge_work(1)?;
        charge_claim_comparison(source)?;
        if source.relation == expected.relation
            && let Some(coefficient) = scale_factor(source, expected)
            && (source.relation == SignedArithmeticRelation::Equal
                || (coefficient > BigInt::zero()
                    && (source.relation != SignedArithmeticRelation::Disequal
                        || !coefficient.is_zero())))
        {
            let mut nodes = vec![SignedArithmeticNode::Premise {
                index: *index,
                result: source.clone(),
            }];
            if coefficient != BigInt::one() {
                nodes.push(SignedArithmeticNode::Scale {
                    source: 0,
                    coefficient,
                    result: expected.clone(),
                });
                return Some(certificate(nodes, 1));
            }
            return Some(certificate(nodes, 0));
        }
        if source.relation == SignedArithmeticRelation::LessEqual
            && expected.relation == SignedArithmeticRelation::LessEqual
            && source.terms == expected.terms
            && source.constant >= expected.constant
        {
            let weakening = &expected.constant - &source.constant;
            let mut nodes = vec![SignedArithmeticNode::Premise {
                index: *index,
                result: source.clone(),
            }];
            if !weakening.is_zero() {
                nodes.push(SignedArithmeticNode::Trivial {
                    result: SignedArithmeticClaim {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        relation: SignedArithmeticRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: weakening,
                    },
                });
                nodes.push(SignedArithmeticNode::Add {
                    left: 0,
                    right: 1,
                    result: expected.clone(),
                });
                return Some(certificate(nodes, 2));
            }
            return Some(certificate(nodes, 0));
        }
        if expected.relation == SignedArithmeticRelation::LessEqual
            && source.relation == SignedArithmeticRelation::Equal
        {
            for reverse in [false, true] {
                let direction = equality_direction(source, reverse);
                if direction == *expected {
                    return Some(certificate(
                        vec![
                            SignedArithmeticNode::Premise {
                                index: *index,
                                result: source.clone(),
                            },
                            SignedArithmeticNode::EqualityToLessEqual {
                                source: 0,
                                reverse,
                                result: direction,
                            },
                        ],
                        1,
                    ));
                }
                if direction.terms == expected.terms && direction.constant >= expected.constant {
                    let weakening = &expected.constant - &direction.constant;
                    let mut nodes = vec![
                        SignedArithmeticNode::Premise {
                            index: *index,
                            result: source.clone(),
                        },
                        SignedArithmeticNode::EqualityToLessEqual {
                            source: 0,
                            reverse,
                            result: direction.clone(),
                        },
                    ];
                    if !weakening.is_zero() {
                        nodes.push(SignedArithmeticNode::Trivial {
                            result: SignedArithmeticClaim {
                                carrier: SignedArithmeticCarrier::SignedInt32,
                                relation: SignedArithmeticRelation::LessEqual,
                                terms: BTreeMap::new(),
                                constant: weakening,
                            },
                        });
                        nodes.push(SignedArithmeticNode::Add {
                            left: 1,
                            right: 2,
                            result: expected.clone(),
                        });
                        return Some(certificate(nodes, 3));
                    }
                    return Some(certificate(nodes, 1));
                }
            }
        }
    }
    None
}

fn plan_machine_affine_goal(
    goal: &Proposition,
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
    int32_range_fallback: bool,
) -> Option<SignedArithmeticCertificate> {
    let (left_operation, right_operation) = affine_operation_terms(goal)?;
    let expected = decomposed_signed_claim(goal)?;
    let mut planner = Planner::new(premises, claims, int32_range_fallback);
    let left_evidence = match left_operation {
        Some(term) => {
            // Affine conclusions decompose their operation roots using the
            // interval evidence.  A direct interval bound treats its root as
            // an opaque atom, so it cannot be used here without changing the
            // algebra represented by the conclusion.  Keep direct compound
            // bounds available to ordinary interval comparisons, but require
            // recursive operation evidence for this path.
            let value = planner.build_interval_for_affine(term);
            Some(value?)
        }
        None => None,
    };
    let right_evidence = match right_operation {
        Some(term) => Some(planner.build_interval_for_affine(term)?),
        None => None,
    };
    let source = planner.affine_claim(&expected, false).or_else(|| {
        is_trivial(&expected).then(|| {
            planner.push(SignedArithmeticNode::Trivial {
                result: expected.clone(),
            })
        })?
    });
    let source = source?;
    let conclusion = affine_conclusion(&mut planner, goal, source, left_evidence, right_evidence)?;
    Some(certificate(planner.nodes, conclusion))
}

fn affine_conclusion(
    planner: &mut Planner<'_>,
    goal: &Proposition,
    source: usize,
    left_evidence: Option<usize>,
    right_evidence: Option<usize>,
) -> Option<usize> {
    match (left_evidence, right_evidence) {
        (Some(left_evidence), Some(right_evidence)) => {
            planner.push(SignedArithmeticNode::AffineConclusionWithEvidence {
                source,
                left_evidence,
                right_evidence,
                result: goal.clone(),
            })
        }
        (Some(evidence), None) | (None, Some(evidence)) => {
            planner.push(SignedArithmeticNode::AffineConclusion {
                source,
                evidence,
                result: goal.clone(),
            })
        }
        (None, None) => None,
    }
}

fn affine_operation_terms(
    proposition: &Proposition,
) -> Option<(Option<&Bitvector32Term>, Option<&Bitvector32Term>)> {
    let (left, right, _) = comparison_terms(proposition)?;
    let is_affine_operation = |term: &Bitvector32Term| {
        matches!(
            term,
            Bitvector32Term::Add(_, _)
                | Bitvector32Term::Subtract(_, _)
                | Bitvector32Term::Multiply(_, _)
        ) || is_narrowed_word_cast(term)
    };
    let left_operation = is_affine_operation(left).then_some(left);
    let right_operation = is_affine_operation(right).then_some(right);
    (left_operation.is_some() || right_operation.is_some())
        .then_some((left_operation, right_operation))
}

/// A goal side the affine planner may combine premises over as one opaque
/// atom: a term with no machine operation, or the sign-bit flip
/// `v ^ 2^31` of one. The flip is how a 32-bit unsigned order is spelled
/// (`ConditionTerm::unsigned_less_than` states `x <u n` as
/// `(x ^ 2^31) <s (n ^ 2^31)`), and it is total: no operand makes it
/// undefined. So an unsigned chain `x <u n`, `n <=u 4` sums over the flipped
/// atoms exactly as the signed chain over `x` and `n` sums over theirs. A
/// flipped atom is a different atom from its operand, so an unsigned bound
/// never composes with a signed one on the same variable.
fn is_affine_planning_atom(term: &Bitvector32Term) -> bool {
    if let Bitvector32Term::BitwiseXor(left, right) = term {
        let operand = match (left.as_ref(), right.as_ref()) {
            (Bitvector32Term::Constant(0x8000_0000), operand)
            | (operand, Bitvector32Term::Constant(0x8000_0000)) => operand,
            _ => return false,
        };
        return !contains_machine_operation(operand);
    }
    !contains_machine_operation(term)
}

fn contains_machine_operation(root: &Bitvector32Term) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        match term {
            Bitvector32Term::Add(_, _)
            | Bitvector32Term::Subtract(_, _)
            | Bitvector32Term::Multiply(_, _)
            | Bitvector32Term::Divide(_, _)
            | Bitvector32Term::Remainder(_, _)
            | Bitvector32Term::ShiftLeft(_, _)
            | Bitvector32Term::ArithmeticShiftRight(_, _)
            | Bitvector32Term::LogicalShiftRight(_, _)
            | Bitvector32Term::BitwiseAnd(_, _)
            | Bitvector32Term::BitwiseOr(_, _)
            | Bitvector32Term::BitwiseXor(_, _) => {
                return true;
            }
            Bitvector32Term::BitwiseNot(_) => return true,
            term if is_narrowed_word_cast(term) => return true,
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    false
}

/// A C conversion the checked `IntervalNarrowedCast` node can relate to its
/// operand.
fn is_narrowed_word_cast(term: &Bitvector32Term) -> bool {
    matches!(
        term,
        Bitvector32Term::MachineIntegerCast { source, destination, .. }
            if crate::kernel::proof::signed_arithmetic::narrowed_word_cast(*source, *destination)
    )
}

fn scale_factor(source: &SignedArithmeticClaim, target: &SignedArithmeticClaim) -> Option<BigInt> {
    charge_claim_comparison(source)?;
    charge_claim_comparison(target)?;
    if source.terms.is_empty() {
        if !target.terms.is_empty() {
            return None;
        }
        return (source.constant != BigInt::zero())
            .then(|| {
                charge_bigint_binary_work(&target.constant, &source.constant)?;
                let coefficient = target.constant.clone() / &source.constant;
                charge_bigint_binary_work(&source.constant, &coefficient)?;
                let product = source.constant.clone() * &coefficient;
                charge_bigint_binary_work(&product, &target.constant)?;
                (product == target.constant).then_some(coefficient)
            })
            .flatten();
    }
    let mut factor = None;
    for (atom, coefficient) in &source.terms {
        charge_work(coefficient.bits() as usize + 1)?;
        charge_work(
            atom.work()
                .saturating_mul(
                    (usize::BITS - source.terms.len().saturating_add(1).leading_zeros()) as usize,
                )
                .max(1),
        )?;
        charge_map_lookup_work(target.terms.len(), atom)?;
        let target_coefficient = target.terms.get(atom).cloned().unwrap_or_default();
        charge_work(target_coefficient.bits() as usize + 1)?;
        if coefficient.is_zero() {
            continue;
        }
        let quotient = &target_coefficient / coefficient;
        charge_bigint_binary_work(&target_coefficient, coefficient)?;
        let product = coefficient * &quotient;
        charge_bigint_binary_work(coefficient, &quotient)?;
        if product != target_coefficient {
            return None;
        }
        if let Some(existing) = &factor {
            charge_bigint_binary_work(existing, &quotient)?;
            if existing != &quotient {
                return None;
            }
        } else {
            factor = Some(quotient);
        }
    }
    let factor = factor?;
    charge_work(source.constant.bits() as usize + factor.bits() as usize + 2)?;
    charge_bigint_binary_work(&source.constant, &factor)?;
    let product = source.constant.clone() * &factor;
    charge_bigint_binary_work(&product, &target.constant)?;
    if product != target.constant {
        return None;
    }
    for atom in target.terms.keys() {
        charge_map_lookup_work(source.terms.len(), atom)?;
        if !source.terms.contains_key(atom) {
            return None;
        }
    }
    Some(factor)
}

fn add_affine_claims(
    left: &SignedArithmeticClaim,
    right: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if left.carrier != right.carrier
        || left.relation != SignedArithmeticRelation::LessEqual
        || right.relation != SignedArithmeticRelation::LessEqual
    {
        return None;
    }
    charge_claim_comparison(left)?;
    charge_claim_comparison(right)?;
    let mut terms = left.terms.clone();
    for (atom, coefficient) in &right.terms {
        charge_map_update_work(terms.len(), atom, coefficient)?;
        let previous = terms.get(atom).cloned().unwrap_or_default();
        charge_bigint_binary_work(&previous, coefficient)?;
        let updated = previous + coefficient;
        if updated.is_zero() {
            terms.remove(atom);
        } else {
            terms.insert(atom.clone(), updated);
        }
    }
    charge_bigint_binary_work(&left.constant, &right.constant)?;
    Some(SignedArithmeticClaim {
        carrier: left.carrier,
        relation: SignedArithmeticRelation::LessEqual,
        terms,
        constant: &left.constant + &right.constant,
    })
}

fn subtract_affine_claims(
    target: &SignedArithmeticClaim,
    left: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if target.carrier != left.carrier
        || target.relation != SignedArithmeticRelation::LessEqual
        || left.relation != SignedArithmeticRelation::LessEqual
    {
        return None;
    }
    charge_claim_comparison(target)?;
    charge_claim_comparison(left)?;
    let mut terms = target.terms.clone();
    for (atom, coefficient) in &left.terms {
        charge_map_update_work(terms.len(), atom, coefficient)?;
        let previous = terms.get(atom).cloned().unwrap_or_default();
        let updated = previous - coefficient;
        if updated.is_zero() {
            terms.remove(atom);
        } else {
            terms.insert(atom.clone(), updated);
        }
    }
    charge_bigint_binary_work(&target.constant, &left.constant)?;
    Some(SignedArithmeticClaim {
        carrier: target.carrier,
        relation: SignedArithmeticRelation::LessEqual,
        terms,
        constant: &target.constant - &left.constant,
    })
}

fn claim_fingerprint(claim: &SignedArithmeticClaim) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(&claim.carrier).hash(&mut hasher);
    std::mem::discriminant(&claim.relation).hash(&mut hasher);
    for (atom, coefficient) in &claim.terms {
        atom.hash(&mut hasher);
        coefficient.hash(&mut hasher);
    }
    claim.constant.hash(&mut hasher);
    hasher.finish()
}

fn charge_claim_comparison(claim: &SignedArithmeticClaim) -> Option<()> {
    let logarithmic = (usize::BITS - claim.terms.len().saturating_add(1).leading_zeros()) as usize;
    let mut units = claim.terms.len().saturating_add(1);
    units = units.saturating_add(claim.constant.bits() as usize + 1);
    for (atom, coefficient) in &claim.terms {
        units = units.saturating_add(
            atom.work()
                .saturating_add(coefficient.bits() as usize + 1)
                .saturating_mul(logarithmic.max(1)),
        );
    }
    charge_work(units)
}

fn charge_map_update_work(
    map_len: usize,
    atom: &SignedArithmeticAtom,
    coefficient: &BigInt,
) -> Option<()> {
    let logarithmic = (usize::BITS - map_len.saturating_add(1).leading_zeros()) as usize;
    charge_work(
        atom.work()
            .saturating_add(coefficient.bits() as usize + 1)
            .saturating_mul(logarithmic.max(1))
            .saturating_mul(3),
    )
}

fn charge_bigint_binary_work(left: &BigInt, right: &BigInt) -> Option<()> {
    charge_work((left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1))
}

fn charge_map_lookup_work(map_len: usize, atom: &SignedArithmeticAtom) -> Option<()> {
    let logarithmic = (usize::BITS - map_len.saturating_add(1).leading_zeros()) as usize;
    charge_work(atom.work().saturating_mul(logarithmic.max(1)))
}

fn equality_direction(source: &SignedArithmeticClaim, reverse: bool) -> SignedArithmeticClaim {
    if reverse {
        SignedArithmeticClaim {
            carrier: source.carrier,
            relation: SignedArithmeticRelation::LessEqual,
            terms: source.terms.iter().map(|(a, c)| (a.clone(), -c)).collect(),
            constant: -&source.constant,
        }
    } else {
        SignedArithmeticClaim {
            carrier: source.carrier,
            relation: SignedArithmeticRelation::LessEqual,
            terms: source.terms.clone(),
            constant: source.constant.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct DefinednessKey {
    operator: u8,
    left: u64,
    right: u64,
}

fn definedness_parts_from_term(
    term: &Bitvector32Term,
) -> Option<(u8, &Bitvector32Term, &Bitvector32Term)> {
    Some(match term {
        Bitvector32Term::Add(left, right) => (0, left, right),
        Bitvector32Term::Subtract(left, right) => (1, left, right),
        Bitvector32Term::Multiply(left, right) => (2, left, right),
        Bitvector32Term::ShiftLeft(left, right) => (3, left, right),
        Bitvector32Term::Remainder(left, right) => (4, left, right),
        _ => return None,
    })
}

fn definedness_parts_from_proposition(
    proposition: &Proposition,
) -> Option<(u8, &Bitvector32Term, &Bitvector32Term)> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    Some(match condition {
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => (0, left, right),
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => (1, left, right),
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => (2, left, right),
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => (3, left, right),
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => (4, left, right),
        _ => return None,
    })
}

#[derive(Clone, Copy)]
struct BoundCandidate {
    position: usize,
    bound: i64,
    /// For an equality premise, the direction of the `<=` it gives this
    /// bound (`EqualityToLessEqual`'s `reverse`); `None` for a `<=` premise.
    equality: Option<bool>,
}

/// Where a derived bound's other atom gets its own bound.
#[derive(Clone, Copy)]
enum OtherBound {
    Premise(BoundCandidate),
    /// A node already proving it, itself derived.
    Derived(usize),
    Range,
}

#[derive(Clone, Copy)]
enum BoundSide {
    Lower,
    Upper,
}

#[derive(Default)]
struct BoundCandidates {
    lower: Option<BoundCandidate>,
    upper: Option<BoundCandidate>,
}

struct Planner<'a> {
    premises: &'a [Proposition],
    claims: &'a [(usize, SignedArithmeticClaim)],
    nodes: Vec<SignedArithmeticNode>,
    intervals: Vec<Option<SignedArithmeticInterval>>,
    interval_cache: HashMap<SignedArithmeticAtom, usize>,
    defined_cache: HashMap<DefinednessKey, Option<usize>>,
    definedness_index: Option<HashMap<DefinednessKey, Vec<usize>>>,
    bound_index: Option<HashMap<SignedArithmeticAtom, BoundCandidates>>,
    term_hash_cache: HashMap<usize, u64>,
    premise_cache: HashMap<usize, usize>,
    /// The atoms whose bounds `derived_bound` is deriving, outermost first:
    /// a bound reached through another derived bound never revisits one.
    deriving: Vec<SignedArithmeticAtom>,
    /// Whether `derived_bound` may use an atom's own `int32` range where no
    /// premise bounds it (the planner's second pass only).
    int32_range_fallback: bool,
}

impl<'a> Planner<'a> {
    fn new(
        premises: &'a [Proposition],
        claims: &'a [(usize, SignedArithmeticClaim)],
        int32_range_fallback: bool,
    ) -> Self {
        Self {
            int32_range_fallback,
            premises,
            claims,
            nodes: Vec::new(),
            intervals: Vec::new(),
            interval_cache: HashMap::new(),
            defined_cache: HashMap::new(),
            definedness_index: None,
            bound_index: None,
            term_hash_cache: HashMap::new(),
            premise_cache: HashMap::new(),
            deriving: Vec::new(),
        }
    }

    fn push(&mut self, node: SignedArithmeticNode) -> Option<usize> {
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let index = self.nodes.len();
        self.nodes.push(node);
        self.intervals.push(None);
        Some(index)
    }

    fn push_interval(
        &mut self,
        node: SignedArithmeticNode,
        interval: SignedArithmeticInterval,
    ) -> Option<usize> {
        let index = self.push(node)?;
        self.intervals[index] = Some(interval);
        Some(index)
    }

    fn interval_at(&self, index: usize) -> Option<SignedArithmeticInterval> {
        self.intervals.get(index)?.clone()
    }

    fn premise(&mut self, index: usize, claim: &SignedArithmeticClaim) -> Option<usize> {
        if let Some(node) = self.premise_cache.get(&index) {
            return Some(*node);
        }
        let node = self.push(SignedArithmeticNode::Premise {
            index,
            result: claim.clone(),
        })?;
        self.premise_cache.insert(index, node);
        Some(node)
    }

    /// The node proving an indexed bound's `<=` claim, and that claim: the
    /// premise itself, or for an equality the premise read in the
    /// candidate's direction.
    fn bound_source(
        &mut self,
        candidate: BoundCandidate,
    ) -> Option<(usize, SignedArithmeticClaim)> {
        let (index, claim) = self.claims.get(candidate.position)?;
        let (index, claim) = (*index, claim.clone());
        let node = self.premise(index, &claim)?;
        let Some(reverse) = candidate.equality else {
            return Some((node, claim));
        };
        let direction = equality_direction(&claim, reverse);
        let node = self.push(SignedArithmeticNode::EqualityToLessEqual {
            source: node,
            reverse,
            result: direction.clone(),
        })?;
        Some((node, direction))
    }

    /// [`Self::affine_claim`], or for an equality its two signed
    /// directions, each planned from the same selected facts, retaining
    /// equality substitutions as checked arithmetic nodes rather than
    /// importing a solver verdict.
    fn affine_claim_or_bounds(
        &mut self,
        expected: &SignedArithmeticClaim,
        allow_weakening: bool,
    ) -> Option<usize> {
        self.affine_claim(expected, allow_weakening).or_else(|| {
            if expected.relation != SignedArithmeticRelation::Equal {
                return None;
            }
            let lower = self.affine_claim(&equality_direction(expected, false), allow_weakening)?;
            let upper = self.affine_claim(&equality_direction(expected, true), allow_weakening)?;
            self.push(SignedArithmeticNode::EqualityFromBounds {
                lower,
                upper,
                result: expected.clone(),
            })
        })
    }

    fn affine_claim(
        &mut self,
        target: &SignedArithmeticClaim,
        allow_weakening: bool,
    ) -> Option<usize> {
        if let Some(node) = self.affine_claim_direct(target)? {
            return Some(node);
        }
        self.affine_claim_combined(target, allow_weakening)
    }

    /// `target` from one premise: the premise itself, a positive multiple
    /// of it, or a weakening of it. `Some(None)` when no premise states it.
    fn affine_claim_direct(&mut self, target: &SignedArithmeticClaim) -> Option<Option<usize>> {
        for (index, claim) in self.claims {
            charge_work(1)?;
            charge_claim_comparison(claim)?;
            if claim == target {
                return self.premise(*index, claim).map(Some);
            }
            if claim.relation == target.relation
                && let Some(coefficient) = scale_factor(claim, target)
                && (claim.relation == SignedArithmeticRelation::Equal
                    || (coefficient > BigInt::zero()
                        && (claim.relation != SignedArithmeticRelation::Disequal
                            || !coefficient.is_zero())))
            {
                let source = self.premise(*index, claim)?;
                if coefficient == BigInt::one() {
                    return Some(Some(source));
                }
                return self
                    .push(SignedArithmeticNode::Scale {
                        source,
                        coefficient,
                        result: target.clone(),
                    })
                    .map(Some);
            }
            if claim.relation == SignedArithmeticRelation::LessEqual
                && target.relation == SignedArithmeticRelation::LessEqual
                && claim.terms == target.terms
                && claim.constant >= target.constant
            {
                let source = self.premise(*index, claim)?;
                let weakening = &target.constant - &claim.constant;
                if weakening.is_zero() {
                    return Some(Some(source));
                }
                let trivial = self.push(SignedArithmeticNode::Trivial {
                    result: SignedArithmeticClaim {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        relation: SignedArithmeticRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: weakening,
                    },
                })?;
                return self
                    .push(SignedArithmeticNode::Add {
                        left: source,
                        right: trivial,
                        result: target.clone(),
                    })
                    .map(Some);
            }
        }
        Some(None)
    }

    /// `target` from several premises: pair sums, a strict bound beside a
    /// disequality, substitution through equalities, and for an explicit
    /// premise list the sum of every listed bound.
    fn affine_claim_combined(
        &mut self,
        target: &SignedArithmeticClaim,
        allow_weakening: bool,
    ) -> Option<usize> {
        // Index claims by a bounded structural fingerprint, then verify only
        // hash-collision candidates with the exact affine operation.  This
        // preserves the useful five-premise bound case without a quadratic
        // pair scan over unrelated facts.
        let mut index: HashMap<u64, Vec<usize>> = HashMap::new();
        for (position, (_, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            index
                .entry(claim_fingerprint(claim))
                .or_default()
                .push(position);
        }
        if let Some(node) = self.strict_from_disequal(target, &index)? {
            return Some(node);
        }
        // A strict premise can make the two-premise sum one unit stronger
        // than a weak target. Probe that exact neighboring claim through the
        // same index, then make the weakening explicit in the certificate.
        let stronger = allow_weakening.then(|| SignedArithmeticClaim {
            constant: &target.constant + BigInt::one(),
            ..target.clone()
        });
        for (left_index, left) in self.claims.iter() {
            if left.relation != SignedArithmeticRelation::LessEqual {
                continue;
            }
            for sum_goal in std::iter::once(target).chain(stronger.as_ref()) {
                let complement = subtract_affine_claims(sum_goal, left)?;
                let Some(right_positions) = index.get(&claim_fingerprint(&complement)) else {
                    continue;
                };
                for right_position in right_positions {
                    charge_work(1)?;
                    let (right_index, right) = &self.claims[*right_position];
                    if *right_index == *left_index || add_affine_claims(left, right)? != *sum_goal {
                        continue;
                    }
                    let left_node = self.premise(*left_index, left)?;
                    let right_node = self.premise(*right_index, right)?;
                    let sum_node = self.push(SignedArithmeticNode::Add {
                        left: left_node,
                        right: right_node,
                        result: sum_goal.clone(),
                    })?;
                    if sum_goal == target {
                        return Some(sum_node);
                    }
                    let weakening = self.push(SignedArithmeticNode::Trivial {
                        result: SignedArithmeticClaim {
                            carrier: target.carrier,
                            relation: SignedArithmeticRelation::LessEqual,
                            terms: BTreeMap::new(),
                            constant: -BigInt::one(),
                        },
                    })?;
                    return self.push(SignedArithmeticNode::Add {
                        left: sum_node,
                        right: weakening,
                        result: target.clone(),
                    });
                }
            }
        }
        if let Some(node) = self.affine_pair_through_equality(target) {
            return Some(node);
        }
        if let Some(node) = self.affine_chain_through_equalities(target) {
            return Some(node);
        }
        if allow_weakening {
            return self.affine_sum_of_listed_claims(target);
        }
        None
    }

    /// The sum of every listed inequality, for a chain of any length:
    /// `x < a`, `a <= b`, `b <= 4` sum to `x < 4`. `arithmetic() using`
    /// lists the premises it means, so all of them are added, in order, and
    /// the sum is weakened to the target when it is stronger. The work is
    /// one addition per listed premise; nothing is searched.
    fn affine_sum_of_listed_claims(&mut self, target: &SignedArithmeticClaim) -> Option<usize> {
        if target.relation != SignedArithmeticRelation::LessEqual {
            return None;
        }
        let listed = self
            .claims
            .iter()
            .filter(|(_, claim)| claim.relation == SignedArithmeticRelation::LessEqual)
            .cloned()
            .collect::<Vec<_>>();
        // One or two premises are the cases the searches above decide.
        if listed.len() < 3 {
            return None;
        }
        let mut listed = listed.into_iter();
        let (first_index, mut sum) = listed.next()?;
        let mut node = self.premise(first_index, &sum)?;
        for (index, claim) in listed {
            charge_work(1)?;
            let next = add_affine_claims(&sum, &claim)?;
            let right = self.premise(index, &claim)?;
            node = self.push(SignedArithmeticNode::Add {
                left: node,
                right,
                result: next.clone(),
            })?;
            sum = next;
        }
        if sum == *target {
            return Some(node);
        }
        if sum.terms != target.terms || sum.constant < target.constant {
            return None;
        }
        let trivial = self.push(SignedArithmeticNode::Trivial {
            result: SignedArithmeticClaim {
                carrier: target.carrier,
                relation: SignedArithmeticRelation::LessEqual,
                terms: BTreeMap::new(),
                constant: &target.constant - &sum.constant,
            },
        })?;
        self.push(SignedArithmeticNode::Add {
            left: node,
            right: trivial,
            result: target.clone(),
        })
    }

    /// `target` by substituting equal atoms in turn: an equality naming an
    /// atom of the remaining goal, in the direction whose coefficient there
    /// matches the goal's, is subtracted from it, until one premise states
    /// what remains. `a == d + 1`, `d == c + 1` and `c <= 500` give `a <=
    /// 502` as `(a - d <= 1) + ((d - c <= 1) + (c <= 500))`, each equality
    /// read as `<=` by the checked `EqualityToLessEqual` step. Each equality
    /// is used once, the first that names a remaining atom, so the chain is
    /// at most one step per premise and each step one pass over them.
    fn affine_chain_through_equalities(&mut self, target: &SignedArithmeticClaim) -> Option<usize> {
        if target.relation != SignedArithmeticRelation::LessEqual {
            return None;
        }
        let mut used = vec![false; self.claims.len()];
        // Each substituted equality's direction and the goal it leaves.
        let mut steps: Vec<(usize, bool, SignedArithmeticClaim)> = Vec::new();
        let mut remaining = target.clone();
        let base = loop {
            if steps.len() == self.claims.len() {
                return None;
            }
            if !steps.is_empty() {
                if let Some(node) = self.affine_claim_direct(&remaining)? {
                    break node;
                }
                if let Some(node) = self.affine_claim_from_atom_bounds(&remaining) {
                    break node;
                }
            }
            let mut next = None;
            for (position, (_, claim)) in self.claims.iter().enumerate() {
                charge_work(1)?;
                if used[position] || claim.relation != SignedArithmeticRelation::Equal {
                    continue;
                }
                let found = claim.terms.iter().find_map(|(atom, coefficient)| {
                    let wanted = remaining.terms.get(atom)?;
                    let reverse = if coefficient == wanted {
                        false
                    } else if -coefficient == *wanted {
                        true
                    } else {
                        return None;
                    };
                    Some(reverse)
                });
                if let Some(reverse) = found {
                    next = Some((position, reverse));
                    break;
                }
            }
            let (position, reverse) = next?;
            used[position] = true;
            let direction = equality_direction(&self.claims[position].1, reverse);
            remaining = subtract_affine_claims(&remaining, &direction)?;
            steps.push((position, reverse, remaining.clone()));
        };
        // Fold back up: each step adds its equality direction to the proof
        // of the goal it left, giving the goal before it.
        let mut node = base;
        let mut goals = std::iter::once(target.clone())
            .chain(steps.iter().map(|(_, _, left)| left.clone()))
            .collect::<Vec<_>>();
        goals.pop();
        for ((position, reverse, _), goal) in steps.into_iter().zip(goals).rev() {
            let direction = self.bound_source(BoundCandidate {
                position,
                bound: 0,
                equality: Some(reverse),
            })?;
            node = self.push(SignedArithmeticNode::Add {
                left: direction.0,
                right: node,
                result: goal,
            })?;
        }
        Some(node)
    }

    /// `target` as the sum of one indexed bound per atom, on the side its
    /// coefficient needs (an upper bound for `+1`, a lower one for `-1`),
    /// weakened to the target's constant: `0 <= b <= 500` and `0 <= d <=
    /// 100` give `b + d <= 1000`. One index lookup per atom.
    fn affine_claim_from_atom_bounds(&mut self, target: &SignedArithmeticClaim) -> Option<usize> {
        if target.relation != SignedArithmeticRelation::LessEqual || target.terms.is_empty() {
            return None;
        }
        self.ensure_bound_index()?;
        let mut candidates = Vec::with_capacity(target.terms.len());
        for (atom, coefficient) in &target.terms {
            charge_work(1)?;
            let bounds = self.bound_index.as_ref()?.get(atom)?;
            let candidate = if coefficient == &BigInt::one() {
                bounds.upper?
            } else if coefficient == &BigInt::from(-1) {
                bounds.lower?
            } else {
                return None;
            };
            candidates.push(candidate);
        }
        let mut sum: Option<(usize, SignedArithmeticClaim)> = None;
        for candidate in candidates {
            let (node, claim) = self.bound_source(candidate)?;
            sum = Some(match sum {
                None => (node, claim),
                Some((left, total)) => {
                    let result = add_affine_claims(&total, &claim)?;
                    let node = self.push(SignedArithmeticNode::Add {
                        left,
                        right: node,
                        result: result.clone(),
                    })?;
                    (node, result)
                }
            });
        }
        let (node, total) = sum?;
        if total == *target {
            return Some(node);
        }
        if total.terms != target.terms || total.constant < target.constant {
            return None;
        }
        let trivial = self.push(SignedArithmeticNode::Trivial {
            result: SignedArithmeticClaim {
                carrier: target.carrier,
                relation: SignedArithmeticRelation::LessEqual,
                terms: BTreeMap::new(),
                constant: &target.constant - &total.constant,
            },
        })?;
        self.push(SignedArithmeticNode::Add {
            left: node,
            right: trivial,
            result: target.clone(),
        })
    }

    /// A two-premise sum where one addend is a direction of an equality
    /// premise: `y == x` and `0 <= x` give `0 <= y` as `(x - y <= 0) +
    /// (-x <= 0)`, the equality weakened to the needed direction by the
    /// checked `EqualityToLessEqual` step. This is substitution of an equal
    /// atom, spelled as the linear step the kernel already checks.
    ///
    /// It runs only after the inequality-only pair search found nothing, so
    /// every certificate that search chose is unchanged. Both directions of
    /// each equality are indexed by fingerprint beside the inequalities;
    /// the complement of each left addend is looked up, never pair-scanned.
    fn affine_pair_through_equality(&mut self, target: &SignedArithmeticClaim) -> Option<usize> {
        if target.relation != SignedArithmeticRelation::LessEqual
            || !self
                .claims
                .iter()
                .any(|(_, claim)| claim.relation == SignedArithmeticRelation::Equal)
        {
            return None;
        }
        // (claim position, equality direction or `None` for an inequality,
        // the `<=` claim it contributes)
        let mut sources: Vec<(usize, Option<bool>, SignedArithmeticClaim)> = Vec::new();
        for (position, (_, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            match claim.relation {
                SignedArithmeticRelation::LessEqual => {
                    sources.push((position, None, claim.clone()))
                }
                SignedArithmeticRelation::Equal => {
                    for reverse in [false, true] {
                        sources.push((position, Some(reverse), equality_direction(claim, reverse)));
                    }
                }
                SignedArithmeticRelation::Disequal => {}
            }
        }
        let mut index: HashMap<u64, Vec<usize>> = HashMap::new();
        for (source_position, (_, _, claim)) in sources.iter().enumerate() {
            charge_work(1)?;
            index
                .entry(claim_fingerprint(claim))
                .or_default()
                .push(source_position);
        }
        for left_position in 0..sources.len() {
            let (left_claim_position, left_direction, left) = sources[left_position].clone();
            let complement = subtract_affine_claims(target, &left)?;
            let Some(right_positions) = index.get(&claim_fingerprint(&complement)).cloned() else {
                continue;
            };
            for right_position in right_positions {
                charge_work(1)?;
                let (right_claim_position, right_direction, right) =
                    sources[right_position].clone();
                // At least one addend is an equality direction; a pair of
                // inequalities was the search above.
                if right_claim_position == left_claim_position
                    || (left_direction.is_none() && right_direction.is_none())
                    || add_affine_claims(&left, &right)? != *target
                {
                    continue;
                }
                let left_node = self.less_equal_source(left_claim_position, left_direction)?;
                let right_node = self.less_equal_source(right_claim_position, right_direction)?;
                return self.push(SignedArithmeticNode::Add {
                    left: left_node,
                    right: right_node,
                    result: target.clone(),
                });
            }
        }
        None
    }

    /// The `<=` node for one premise: the premise itself, or for an equality
    /// its checked weakening to the requested direction.
    fn less_equal_source(&mut self, position: usize, direction: Option<bool>) -> Option<usize> {
        let (index, claim) = self.claims[position].clone();
        let premise = self.premise(index, &claim)?;
        let Some(reverse) = direction else {
            return Some(premise);
        };
        self.push(SignedArithmeticNode::EqualityToLessEqual {
            source: premise,
            reverse,
            result: equality_direction(&claim, reverse),
        })
    }

    /// A non-strict bound one unit short of the target closes it together
    /// with a disequality on the bound's own affine form (in either sign):
    /// `t <= 0` and `t != 0` give `t + 1 <= 0`.  Both premises are found by
    /// fingerprint lookup, never by a pair scan.  The outer `Option` is the
    /// work budget; the inner one is whether such premises exist.
    fn strict_from_disequal(
        &mut self,
        target: &SignedArithmeticClaim,
        index: &HashMap<u64, Vec<usize>>,
    ) -> Option<Option<usize>> {
        if target.relation != SignedArithmeticRelation::LessEqual || target.terms.is_empty() {
            return Some(None);
        }
        charge_claim_comparison(target)?;
        let short = SignedArithmeticClaim {
            carrier: target.carrier,
            relation: SignedArithmeticRelation::LessEqual,
            terms: target.terms.clone(),
            constant: &target.constant - BigInt::one(),
        };
        let Some(bound_positions) = index.get(&claim_fingerprint(&short)) else {
            return Some(None);
        };
        let disequalities = [
            SignedArithmeticClaim {
                carrier: short.carrier,
                relation: SignedArithmeticRelation::Disequal,
                terms: short.terms.clone(),
                constant: short.constant.clone(),
            },
            SignedArithmeticClaim {
                carrier: short.carrier,
                relation: SignedArithmeticRelation::Disequal,
                terms: short.terms.iter().map(|(a, c)| (a.clone(), -c)).collect(),
                constant: -&short.constant,
            },
        ];
        for bound_position in bound_positions {
            charge_work(1)?;
            let (bound_index, bound) = &self.claims[*bound_position];
            if *bound != short {
                continue;
            }
            for disequal in &disequalities {
                let Some(disequal_positions) = index.get(&claim_fingerprint(disequal)) else {
                    continue;
                };
                for disequal_position in disequal_positions {
                    charge_work(1)?;
                    let (disequal_index, candidate) = &self.claims[*disequal_position];
                    if candidate != disequal {
                        continue;
                    }
                    let bound_node = self.premise(*bound_index, bound)?;
                    let disequal_node = self.premise(*disequal_index, candidate)?;
                    let node = self.push(SignedArithmeticNode::StrictFromDisequal {
                        bound: bound_node,
                        disequal: disequal_node,
                        result: target.clone(),
                    })?;
                    return Some(Some(node));
                }
            }
        }
        Some(None)
    }

    fn defined(&mut self, term: &Bitvector32Term) -> Option<usize> {
        let cache_key = self.definedness_key_from_term(term)?;
        if let Some(index) = self.defined_cache.get(&cache_key) {
            return index.and_then(|index| {
                self.push(SignedArithmeticNode::DefinedPremise {
                    index,
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                })
            });
        }
        self.ensure_definedness_index()?;
        let index = self
            .definedness_index
            .as_ref()?
            .get(&cache_key)
            .and_then(|candidates| {
                candidates.iter().copied().find(|candidate| {
                    charge_work(1).is_some() && exact_definedness(&self.premises[*candidate], term)
                })
            });
        self.defined_cache.insert(cache_key, index);
        let index = index?;
        self.push(SignedArithmeticNode::DefinedPremise {
            index,
            carrier: SignedArithmeticCarrier::SignedInt32,
            term: term.clone(),
        })
    }

    fn definedness_key_from_term(&mut self, term: &Bitvector32Term) -> Option<DefinednessKey> {
        let (operator, left, right) = definedness_parts_from_term(term)?;
        Some(DefinednessKey {
            operator,
            left: self.term_hash(left)?,
            right: self.term_hash(right)?,
        })
    }

    fn term_hash(&mut self, root: &Bitvector32Term) -> Option<u64> {
        let root_key = root as *const Bitvector32Term as usize;
        if let Some(hash) = self.term_hash_cache.get(&root_key) {
            return Some(*hash);
        }
        enum Task<'a> {
            Visit(&'a Bitvector32Term),
            Finish(&'a Bitvector32Term),
        }
        let mut tasks = vec![Task::Visit(root)];
        while let Some(task) = tasks.pop() {
            charge_work(1)?;
            match task {
                Task::Visit(term) => {
                    let key = term as *const Bitvector32Term as usize;
                    if self.term_hash_cache.contains_key(&key) {
                        continue;
                    }
                    match term {
                        Bitvector32Term::Constant(_)
                        | Bitvector32Term::Int64Constant(_)
                        | Bitvector32Term::UInt64Constant(_)
                        | Bitvector32Term::Variable(_) => {
                            let mut hasher = std::collections::hash_map::DefaultHasher::new();
                            std::mem::discriminant(term).hash(&mut hasher);
                            term.hash(&mut hasher);
                            self.term_hash_cache.insert(key, hasher.finish());
                        }
                        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                            tasks.push(Task::Finish(term));
                            tasks.extend(arguments.iter().rev().map(Task::Visit));
                        }
                        crate::kernel::binary_bitvector32_term!(left, right) => {
                            tasks.push(Task::Finish(term));
                            tasks.push(Task::Visit(right));
                            tasks.push(Task::Visit(left));
                        }
                        Bitvector32Term::BitwiseNot(operand)
                        | Bitvector32Term::Int64From32(operand)
                        | Bitvector32Term::UInt64From32(operand)
                        | Bitvector32Term::UInt32From64(operand)
                        | Bitvector32Term::Int64FromUInt32(operand)
                        | Bitvector32Term::UInt64FromInt32(operand)
                        | Bitvector32Term::UInt64FromInt64(operand) => {
                            tasks.push(Task::Finish(term));
                            tasks.push(Task::Visit(operand));
                        }
                        _ => return None,
                    }
                }
                Task::Finish(term) => {
                    let key = term as *const Bitvector32Term as usize;
                    if self.term_hash_cache.contains_key(&key) {
                        continue;
                    }
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    std::mem::discriminant(term).hash(&mut hasher);
                    match term {
                        Bitvector32Term::PureFunctionApplication { name, arguments } => {
                            name.hash(&mut hasher);
                            arguments.len().hash(&mut hasher);
                            for argument in arguments {
                                self.term_hash_cache
                                    .get(&(argument as *const Bitvector32Term as usize))?
                                    .hash(&mut hasher);
                            }
                        }
                        crate::kernel::binary_bitvector32_term!(left, right) => {
                            self.term_hash_cache
                                .get(&(left.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                            self.term_hash_cache
                                .get(&(right.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                        }
                        Bitvector32Term::BitwiseNot(operand)
                        | Bitvector32Term::Int64From32(operand)
                        | Bitvector32Term::UInt64From32(operand)
                        | Bitvector32Term::UInt32From64(operand)
                        | Bitvector32Term::Int64FromUInt32(operand)
                        | Bitvector32Term::UInt64FromInt32(operand)
                        | Bitvector32Term::UInt64FromInt64(operand) => {
                            self.term_hash_cache
                                .get(&(operand.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                        }
                        _ => return None,
                    }
                    self.term_hash_cache.insert(key, hasher.finish());
                }
            }
        }
        self.term_hash_cache.get(&root_key).copied()
    }

    fn ensure_definedness_index(&mut self) -> Option<()> {
        if self.definedness_index.is_some() {
            return Some(());
        }
        let mut index: HashMap<DefinednessKey, Vec<usize>> = HashMap::new();
        for (candidate, proposition) in self.premises.iter().enumerate() {
            charge_work(1)?;
            let Some((operator, left, right)) = definedness_parts_from_proposition(proposition)
            else {
                continue;
            };
            let key = DefinednessKey {
                operator,
                left: self.term_hash(left)?,
                right: self.term_hash(right)?,
            };
            index.entry(key).or_default().push(candidate);
        }
        self.definedness_index = Some(index);
        Some(())
    }

    fn ensure_bound_index(&mut self) -> Option<()> {
        if self.bound_index.is_some() {
            return Some(());
        }
        let mut index: HashMap<SignedArithmeticAtom, BoundCandidates> = HashMap::new();
        for (position, (_, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            if claim.terms.len() != 1 {
                continue;
            }
            // An equality of one atom bounds it on both sides: each side is
            // the premise read as `<=` in one direction.
            let directions: &[Option<bool>] = match claim.relation {
                SignedArithmeticRelation::LessEqual => &[None],
                SignedArithmeticRelation::Equal => &[Some(false), Some(true)],
                _ => continue,
            };
            for &equality in directions {
                let claim = &match equality {
                    Some(reverse) => equality_direction(claim, reverse),
                    None => claim.clone(),
                };
                let (atom, coefficient) = claim.terms.iter().next()?;
                charge_work(atom.work().saturating_add(coefficient.bits() as usize + 1))?;
                let Some(bound) = (if coefficient == &BigInt::from(-1) {
                    claim.constant.to_i64().map(|value| value.max(SIGNED_MIN))
                } else if coefficient == &BigInt::one() {
                    (-&claim.constant)
                        .to_i64()
                        .map(|value| value.min(SIGNED_MAX))
                } else {
                    None
                }) else {
                    continue;
                };
                let entry = index.entry(atom.clone()).or_default();
                if coefficient == &BigInt::from(-1)
                    && entry.lower.is_none_or(|candidate| bound > candidate.bound)
                {
                    entry.lower = Some(BoundCandidate {
                        position,
                        bound,
                        equality,
                    });
                } else if coefficient == &BigInt::one()
                    && entry.upper.is_none_or(|candidate| bound < candidate.bound)
                {
                    entry.upper = Some(BoundCandidate {
                        position,
                        bound,
                        equality,
                    });
                }
            }
        }
        self.bound_index = Some(index);
        Some(())
    }

    fn interval_atom(&mut self, term: &Bitvector32Term) -> Option<usize> {
        let cache_key = SignedArithmeticAtom::from_term(term)?;
        if let Some(index) = self.interval_cache.get(&cache_key) {
            return Some(*index);
        }
        if let Some(value) = term.as_const().map(|value| i64::from(value as i32)) {
            let index = self.push_interval(
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                    lower: value,
                    upper: value,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: value,
                    upper: value,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        let safe_atom = Self::is_safe_interval_atom(term);
        let atom = SignedArithmeticAtom::from_term(term)?;
        self.ensure_bound_index()?;
        let candidates = self.bound_index.as_ref()?.get(&atom);
        let direct_lower = candidates.and_then(|candidates| candidates.lower);
        let direct_upper = candidates.and_then(|candidates| candidates.upper);
        // A bound the premises state for this atom alone is one premise
        // node; one they state through another atom is that premise added
        // to the other atom's own bound, which is still one affine node.
        let lower = match direct_lower {
            Some(candidate) => Some((self.bound_source(candidate)?.0, candidate.bound)),
            None => self.derived_bound(&atom, BoundSide::Lower)?,
        };
        let upper = match direct_upper {
            Some(candidate) => Some((self.bound_source(candidate)?.0, candidate.bound)),
            None => self.derived_bound(&atom, BoundSide::Upper)?,
        };
        if lower.is_none() && upper.is_none() {
            if !safe_atom {
                return None;
            }
            let index = self.push_interval(
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        let affine_interval_node = |source, lower, upper| {
            if safe_atom {
                SignedArithmeticNode::IntervalFromAffine {
                    source,
                    term: term.clone(),
                    lower,
                    upper,
                }
            } else {
                SignedArithmeticNode::IntervalFromAffineDirect {
                    source,
                    term: term.clone(),
                    lower,
                    upper,
                }
            }
        };
        let Some((lower_node, lower_bound)) = lower else {
            let (upper_node, upper_bound) = upper?;
            let index = self.push_interval(
                affine_interval_node(upper_node, SIGNED_MIN, upper_bound),
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        };
        let lower_node_index = self.push_interval(
            affine_interval_node(lower_node, lower_bound, SIGNED_MAX),
            SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower: lower_bound,
                upper: SIGNED_MAX,
            },
        )?;
        if let Some((upper_node, upper_bound)) = upper {
            // Contradictory bounds intersect to an empty interval, which the
            // kernel refuses outright. Decline here so the tactic reports a
            // prompt arithmetic failure instead of emitting a certificate
            // that cannot be checked.
            if lower_bound > upper_bound {
                return None;
            }
            let upper_interval = self.push_interval(
                affine_interval_node(upper_node, SIGNED_MIN, upper_bound),
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
            )?;
            let result = SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower: lower_bound,
                upper: upper_bound,
            };
            let index = self.push_interval(
                SignedArithmeticNode::IntervalIntersect {
                    left: lower_node_index,
                    right: upper_interval,
                    result,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower_bound,
                    upper: upper_bound,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        self.interval_cache.insert(cache_key, lower_node_index);
        Some(lower_node_index)
    }

    /// A bound on `atom` that the premises state through one other atom: a
    /// premise relating the two, `atom >= other - c` for a lower bound or
    /// `atom <= other + c` for an upper one, added to the other atom's own
    /// direct bound of the same side, which cancels the other atom and
    /// leaves a bound on `atom` alone. `i >= 0` and `i < n` give `n >= 1`
    /// this way, which is what shows `n - i` defined.
    ///
    /// When no premise bounds the other atom, its int32 range does
    /// (`Int32Range`, `other <= INT32_MAX` or `INT32_MIN <= other`), provided
    /// it is an opaque atom: `i < n` then gives `i <= INT32_MAX - 1`, which is
    /// what shows `i + 1` defined. A non-strict `i <= n` gives only
    /// `i <= INT32_MAX`, which shows nothing.
    ///
    /// The result is `Ok(None)` when no premise pair states one, and `None`
    /// only when the work budget is spent. The scan reads each claim once
    /// and looks the other atom's bound up in the index, so it is linear in
    /// the premises; it never chains through a third atom.
    /// A bound on `atom` alone from a two-atom premise and a bound on its
    /// other atom: that atom's own premise bound or, failing one, a bound
    /// derived the same way, so `c == m + 1`, `m == b + 1` and `b <= 500`
    /// bound `c`. Each derivation visits an atom once, at most one per
    /// premise deep.
    fn derived_bound(
        &mut self,
        atom: &SignedArithmeticAtom,
        side: BoundSide,
    ) -> Option<Option<(usize, i64)>> {
        if self.deriving.contains(atom) || self.deriving.len() >= self.claims.len() {
            return Some(None);
        }
        self.deriving.push(atom.clone());
        let bound = self.derived_bound_through(atom, side);
        self.deriving.pop();
        bound
    }

    fn derived_bound_through(
        &mut self,
        atom: &SignedArithmeticAtom,
        side: BoundSide,
    ) -> Option<Option<(usize, i64)>> {
        let own_coefficient = match side {
            BoundSide::Lower => BigInt::from(-1),
            BoundSide::Upper => BigInt::one(),
        };
        let mut best: Option<(
            BoundCandidate,
            SignedArithmeticClaim,
            Vec<(OtherBound, SignedArithmeticClaim)>,
            i64,
        )> = None;
        for (position, (_, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            if claim.terms.len() < 2 || !claim.terms.contains_key(atom) {
                continue;
            }
            // An equality relates its atoms on both sides: each is the
            // premise read as `<=` in one direction.
            let directions: &[Option<bool>] = match claim.relation {
                SignedArithmeticRelation::LessEqual => &[None],
                SignedArithmeticRelation::Equal => &[Some(false), Some(true)],
                _ => continue,
            };
            'direction: for &equality in directions {
                let claim = &match equality {
                    Some(reverse) => equality_direction(claim, reverse),
                    None => claim.clone(),
                };
                let source = BoundCandidate {
                    position,
                    bound: 0,
                    equality,
                };
                if claim.terms.get(atom) != Some(&own_coefficient) {
                    continue;
                }
                // Each other atom is cancelled by its bound on the side its
                // coefficient needs: an upper one for `-1`, a lower one for
                // `+1`.
                let mut others = Vec::new();
                let mut sum = claim.clone();
                for (other, coefficient) in &claim.terms {
                    if other == atom {
                        continue;
                    }
                    let other_side = if coefficient == &BigInt::from(-1) {
                        BoundSide::Upper
                    } else if coefficient == &BigInt::one() {
                        BoundSide::Lower
                    } else {
                        continue 'direction;
                    };
                    let Some(other_bound) = self.other_bound(other, other_side)? else {
                        continue 'direction;
                    };
                    let Some(next) = add_claim(&sum, &other_bound.1) else {
                        continue 'direction;
                    };
                    sum = next;
                    others.push(other_bound);
                }
                // The sum names `atom` alone, with the coefficient of this side.
                if sum.terms.len() != 1 || sum.terms.get(atom) != Some(&own_coefficient) {
                    continue;
                }
                let Some(bound) = (match side {
                    BoundSide::Lower => sum.constant.to_i64().map(|value| value.max(SIGNED_MIN)),
                    BoundSide::Upper => {
                        (-&sum.constant).to_i64().map(|value| value.min(SIGNED_MAX))
                    }
                }) else {
                    continue;
                };
                let better = match (&best, side) {
                    (None, _) => true,
                    (Some((_, _, _, current)), BoundSide::Lower) => bound > *current,
                    (Some((_, _, _, current)), BoundSide::Upper) => bound < *current,
                };
                if better {
                    best = Some((source, claim.clone(), others, bound));
                }
            }
        }
        let Some((source, claim, others, bound)) = best else {
            return Some(None);
        };
        let mut node = self.bound_source(source)?.0;
        let mut sum = claim;
        for (other, other_claim) in others {
            let right = match other {
                OtherBound::Premise(candidate) => self.bound_source(candidate)?.0,
                OtherBound::Derived(node) => node,
                OtherBound::Range => self.push(SignedArithmeticNode::Int32Range {
                    result: other_claim.clone(),
                })?,
            };
            sum = add_claim(&sum, &other_claim)?;
            node = self.push(SignedArithmeticNode::Add {
                left: node,
                right,
                result: sum.clone(),
            })?;
        }
        Some(Some((node, bound)))
    }

    /// A bound on `other` alone on `side`: its own premise bound, one
    /// derived through another premise, or, in the fallback pass, its int32
    /// range; with the `<=` claim it states.
    fn other_bound(
        &mut self,
        other: &SignedArithmeticAtom,
        side: BoundSide,
    ) -> Option<Option<(OtherBound, SignedArithmeticClaim)>> {
        let candidate = self
            .bound_index
            .as_ref()?
            .get(other)
            .and_then(|candidates| match side {
                BoundSide::Lower => candidates.lower,
                BoundSide::Upper => candidates.upper,
            });
        if let Some(candidate) = candidate {
            let Some((_, claim)) = self.claims.get(candidate.position) else {
                return Some(None);
            };
            let claim = match candidate.equality {
                Some(reverse) => equality_direction(claim, reverse),
                None => claim.clone(),
            };
            return Some(Some((OtherBound::Premise(candidate), claim)));
        }
        if let Some((node, _)) = self.derived_bound(other, side)? {
            // The derived node's own `<=` claim on `other`.
            let Some(SignedArithmeticNode::Add { result, .. }) = self.nodes.get(node) else {
                return Some(None);
            };
            return Some(Some((OtherBound::Derived(node), result.clone())));
        }
        if !self.int32_range_fallback {
            return Some(None);
        }
        // The other atom's own int32 range is on the side that cancels it.
        Some(
            crate::kernel::proof::signed_arithmetic::int32_range_bound(
                other.clone(),
                matches!(side, BoundSide::Upper),
            )
            .map(|range| (OtherBound::Range, range)),
        )
    }

    fn is_safe_interval_atom(term: &Bitvector32Term) -> bool {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term {
                Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_) => {}
                Bitvector32Term::UInt32From64(_)
                    if SignedArithmeticAtom::from_term(term).is_some() => {}
                Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter());
                }
                _ => return false,
            }
        }
        true
    }

    fn build_interval(&mut self, root: &Bitvector32Term) -> Option<usize> {
        self.build_interval_with_direct(root, true)
    }

    fn build_interval_for_affine(&mut self, root: &Bitvector32Term) -> Option<usize> {
        self.build_interval_with_direct(root, false)
    }

    fn build_interval_with_direct(
        &mut self,
        root: &Bitvector32Term,
        allow_direct: bool,
    ) -> Option<usize> {
        enum Task<'a> {
            Visit(&'a Bitvector32Term, bool),
            Build(&'a Bitvector32Term),
        }
        let mut tasks = vec![Task::Visit(root, allow_direct)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            charge_work(1)?;
            match task {
                Task::Visit(term, allow_direct) => match term {
                    Bitvector32Term::Constant(_) => results.push(self.interval_atom(term)?),
                    Bitvector32Term::Add(left, right)
                    | Bitvector32Term::Subtract(left, right)
                    | Bitvector32Term::Multiply(left, right) => {
                        if allow_direct && let Some(index) = self.interval_atom(term) {
                            results.push(index);
                            continue;
                        }
                        tasks.push(Task::Build(term));
                        // A direct bound may be the only evidence for a child
                        // operation in an interval comparison.  It stops the
                        // traversal at that child, so direct payloads are
                        // disjoint rather than repeated along one path.
                        tasks.push(Task::Visit(right, allow_direct));
                        tasks.push(Task::Visit(left, allow_direct));
                    }
                    Bitvector32Term::Remainder(operand, divisor)
                    | Bitvector32Term::ShiftLeft(operand, divisor)
                    | Bitvector32Term::ArithmeticShiftRight(operand, divisor) => {
                        divisor.as_const()?;
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(operand, allow_direct));
                    }
                    Bitvector32Term::MachineIntegerCast {
                        value,
                        source,
                        destination,
                    } if crate::kernel::proof::signed_arithmetic::narrowed_word_cast(
                        *source,
                        *destination,
                    ) =>
                    {
                        if allow_direct && let Some(index) = self.interval_atom(term) {
                            results.push(index);
                            continue;
                        }
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(value, allow_direct));
                    }
                    Bitvector32Term::BitwiseAnd(left, right)
                    | Bitvector32Term::BitwiseXor(left, right) => {
                        let (operand, _) = if right.as_const().is_some() {
                            (left, right)
                        } else if left.as_const().is_some() {
                            (right, left)
                        } else {
                            return None;
                        };
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(operand, allow_direct));
                    }
                    _ => results.push(self.interval_atom(term)?),
                },
                Task::Build(term) => {
                    let operand = results.pop()?;
                    let (left, right) = match term {
                        Bitvector32Term::Add(_, _)
                        | Bitvector32Term::Subtract(_, _)
                        | Bitvector32Term::Multiply(_, _) => (Some(results.pop()?), Some(operand)),
                        _ => (None, Some(operand)),
                    };
                    let result = self.build_operation(term, left, right)?;
                    results.push(result);
                }
            }
        }
        results.pop()
    }

    /// A premise that bounds an operation directly, such as `0 <= i` for the
    /// back-edge value `i == i0 + 1`, stops the traversal at that operation.
    /// When that direct bound is one-sided, the operation's operands may
    /// still bound its other side (`i0 < n` and `n <= c` bound `i0 + 1` by
    /// `c`), so the operation is also built from its operands and the two
    /// intervals are intersected. Without this a true premise could only
    /// lose a certificate: citing `0 <= i` beside `i0 < n` hid the upper
    /// bound the operands give. The consumer asks for this only where the
    /// one-sided interval is what refuses it, so the extra work is one build
    /// of this operation's operands, and certificates that did not need it
    /// keep their single direct root.
    fn tighten_one_sided_direct_interval(
        &mut self,
        term: &Bitvector32Term,
        direct: usize,
    ) -> usize {
        let Some(direct_interval) = self.interval_at(direct) else {
            return direct;
        };
        if direct_interval.lower > SIGNED_MIN && direct_interval.upper < SIGNED_MAX {
            return direct;
        }
        let (left, right) = match term {
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right) => (left, right),
            _ => return direct,
        };
        let Some(structural) = (|| {
            let left = self.build_interval_with_direct(left, true)?;
            let right = self.build_interval_with_direct(right, true)?;
            self.build_operation(term, Some(left), Some(right))
        })() else {
            return direct;
        };
        let Some(structural_interval) = self.interval_at(structural) else {
            return direct;
        };
        let lower = direct_interval.lower.max(structural_interval.lower);
        let upper = direct_interval.upper.min(structural_interval.upper);
        let tightened = if lower == direct_interval.lower && upper == direct_interval.upper {
            return direct;
        } else if lower == structural_interval.lower && upper == structural_interval.upper {
            structural
        } else if lower > upper {
            return direct;
        } else {
            let result = SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower,
                upper,
            };
            let Some(index) = self.push_interval(
                SignedArithmeticNode::IntervalIntersect {
                    left: direct,
                    right: structural,
                    result: result.clone(),
                },
                result,
            ) else {
                return direct;
            };
            index
        };
        if let Some(cache_key) = SignedArithmeticAtom::from_term(term) {
            self.interval_cache.insert(cache_key, tightened);
        }
        tightened
    }

    fn build_operation(
        &mut self,
        term: &Bitvector32Term,
        left_index: Option<usize>,
        right_index: Option<usize>,
    ) -> Option<usize> {
        match term {
            // A conversion whose operand stays inside the destination range
            // is that operand (`narrowed_cast_identity`); outside it the
            // planner has no evidence to offer.
            Bitvector32Term::MachineIntegerCast {
                source,
                destination,
                ..
            } => {
                let operand = right_index?;
                let interval = self.interval_at(operand)?;
                let (lo, hi) = destination.format().bounds();
                let (lo, hi) = (i64::try_from(lo).ok()?, i64::try_from(hi).ok()?);
                let floor = if *source == crate::kernel::MachineIntegerType::UInt32 {
                    lo.max(0)
                } else {
                    lo
                };
                (interval.lower >= floor && interval.upper <= hi).then_some(())?;
                self.push_interval(
                    SignedArithmeticNode::IntervalNarrowedCast {
                        operand,
                        source: *source,
                        destination: *destination,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::Add(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let lower = l.lower.checked_add(r.lower)?;
                let upper = l.upper.checked_add(r.upper)?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower.max(SIGNED_MIN),
                    upper: upper.min(SIGNED_MAX),
                };
                if let Some(defined) = self.defined(term) {
                    return self.push_interval(
                        SignedArithmeticNode::IntervalAdd {
                            left,
                            right,
                            defined,
                            result: interval.clone(),
                        },
                        interval,
                    );
                }
                if lower >= SIGNED_MIN && upper <= SIGNED_MAX {
                    return self.push_interval(
                        SignedArithmeticNode::IntervalAddBounded {
                            left,
                            right,
                            result: interval.clone(),
                        },
                        interval,
                    );
                }
                None
            }
            Bitvector32Term::Subtract(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let lower = l.lower.checked_sub(r.upper)?;
                let upper = l.upper.checked_sub(r.lower)?;
                (lower >= SIGNED_MIN && upper <= SIGNED_MAX).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                let defined = self.defined(term).unwrap_or(left);
                self.push_interval(
                    SignedArithmeticNode::IntervalSubtract {
                        left,
                        right,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::Multiply(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let values = [
                    l.lower as i128 * r.lower as i128,
                    l.lower as i128 * r.upper as i128,
                    l.upper as i128 * r.lower as i128,
                    l.upper as i128 * r.upper as i128,
                ];
                let lower = *values.iter().min()?;
                let upper = *values.iter().max()?;
                (lower >= SIGNED_MIN as i128 && upper <= SIGNED_MAX as i128).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower as i64,
                    upper: upper as i64,
                };
                let defined = self.defined(term).unwrap_or(left);
                self.push_interval(
                    SignedArithmeticNode::IntervalMultiply {
                        left,
                        right,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::Remainder(dividend, divisor) => {
                // A known residue transports through a checked bounded sum.
                if let Bitvector32Term::Add(base, addend) = dividend.as_ref()
                    && Self::is_safe_interval_atom(base)
                    && let Some(addend) = addend.as_const().and_then(|v| v.to_i32())
                    && let Some(divisor) = divisor.as_const().and_then(|v| v.to_i32())
                    && let Some(operand) = self.build_interval(base)
                {
                    let original = Bitvector32Term::Remainder(
                        base.clone(),
                        Box::new(Bitvector32Term::Constant(divisor as u32)),
                    );
                    if let Some(remainder) = self.interval_atom(&original)
                        && let Some(op) = self.interval_at(operand)
                        && let Some(rem) = self.interval_at(remainder)
                        && let Ok(result) =
                            crate::kernel::proof::signed_arithmetic::interval_remainder_add(
                                &op, &rem, addend, divisor, 0,
                            )
                    {
                        return self.push_interval(
                            SignedArithmeticNode::IntervalRemainderAdd {
                                operand,
                                remainder,
                                addend,
                                divisor,
                                result: result.clone(),
                            },
                            result,
                        );
                    }
                }
                let operand = right_index?;
                let divisor = divisor.as_const()?.to_i32()?;
                if divisor == 0 {
                    return None;
                }
                let op = self.interval_at(operand)?;
                let bounded = divisor != -1 || !(op.lower <= SIGNED_MIN && op.upper >= SIGNED_MIN);
                let defined = self.defined(term).or_else(|| bounded.then_some(operand))?;
                let magnitude = i64::from(divisor).abs().saturating_sub(1);
                let (lower, upper) = if op.lower >= 0 {
                    (0, magnitude)
                } else if op.upper < 0 {
                    (-magnitude, 0)
                } else {
                    (-magnitude, magnitude)
                };
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalRemainder {
                        operand,
                        divisor,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::ShiftLeft(_, shift) => {
                let operand = right_index?;
                let shift = shift.as_const()?.to_i32()?;
                if !(0..32).contains(&shift) {
                    return None;
                }
                let op = self.interval_at(operand)?;
                if op.lower < 0 {
                    return None;
                }
                let factor = 1_i128 << shift;
                let lower = op.lower as i128 * factor;
                let upper = op.upper as i128 * factor;
                (lower >= SIGNED_MIN as i128 && upper <= SIGNED_MAX as i128).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower as i64,
                    upper: upper as i64,
                };
                let defined = self.defined(term).unwrap_or(operand);
                self.push_interval(
                    SignedArithmeticNode::IntervalShiftLeft {
                        operand,
                        shift,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::ArithmeticShiftRight(_, shift) => {
                let operand = right_index?;
                let shift = shift.as_const()?.to_i32()?;
                if !(0..32).contains(&shift) {
                    return None;
                }
                let op = self.interval_at(operand)?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: i64::from((op.lower as i32) >> shift),
                    upper: i64::from((op.upper as i32) >> shift),
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalArithmeticShiftRight {
                        operand,
                        shift,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::BitwiseAnd(left, right) => {
                let operand = right_index?;
                let mask = left.as_const().or_else(|| right.as_const())?;
                if mask > i32::MAX as u32 {
                    return None;
                }
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: 0,
                    upper: i64::from(mask as i32),
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalBitwiseAnd {
                        operand,
                        mask,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::BitwiseXor(left, right) => {
                let operand = right_index?;
                let (operand_term, sign_bit) = if left.as_const() == Some(0x8000_0000) {
                    (right, left)
                } else if right.as_const() == Some(0x8000_0000) {
                    (left, right)
                } else {
                    return None;
                };
                if sign_bit.as_const()? != 0x8000_0000 {
                    return None;
                }
                // The flipped interval is only as tight as the operand's. A
                // premise bounding the operand directly on one side only
                // leaves the other side open; its operands may still close it.
                let mut operand = operand;
                let mut op = self.interval_at(operand)?;
                if (op.lower == SIGNED_MIN || op.upper == SIGNED_MAX)
                    && matches!(
                        self.nodes.get(operand),
                        Some(SignedArithmeticNode::IntervalFromAffineDirect { .. })
                    )
                {
                    operand = self.tighten_one_sided_direct_interval(operand_term, operand);
                    op = self.interval_at(operand)?;
                }
                let (lower, upper) = if op.lower >= 0 {
                    (op.lower + SIGNED_MIN, op.upper + SIGNED_MIN)
                } else if op.upper < 0 {
                    (op.lower - SIGNED_MIN, op.upper - SIGNED_MIN)
                } else {
                    (SIGNED_MIN, SIGNED_MAX)
                };
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalSignBitFlip {
                        operand,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            _ => None,
        }
    }
}

fn exact_definedness(proposition: &Proposition, term: &Bitvector32Term) -> bool {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return false;
    };
    match (condition, term) {
        (ConditionTerm::Bitvector32SignedAddOverflows(left, right), Bitvector32Term::Add(a, b))
        | (
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right),
            Bitvector32Term::Subtract(a, b),
        )
        | (
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right),
            Bitvector32Term::Multiply(a, b),
        )
        | (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right),
            Bitvector32Term::ShiftLeft(a, b),
        )
        | (
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right),
            Bitvector32Term::Remainder(a, b),
        ) => terms_equal(left, a) && terms_equal(right, b),
        _ => false,
    }
}

fn terms_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let (Some(left), Some(right)) = (
        SignedArithmeticAtom::from_term(left),
        SignedArithmeticAtom::from_term(right),
    ) else {
        return false;
    };
    charge_work(left.work().saturating_add(right.work()).saturating_add(1)).is_some()
        && left == right
}

fn plan_interval_goal(
    goal: &Proposition,
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
    int32_range_fallback: bool,
) -> Option<SignedArithmeticCertificate> {
    let (left, right, comparison) = comparison_terms(goal)?;
    let mut planner = Planner::new(premises, claims, int32_range_fallback);
    let left_node = planner.build_interval(left)?;
    let right_node = planner.build_interval(right)?;
    let result = SignedArithmeticComparison::from_comparison(comparison);
    let left_interval = planner.interval_at(left_node)?;
    let right_interval = planner.interval_at(right_node)?;
    if !interval_proves(&left_interval, &right_interval, comparison)
        && !term_interval_proves(left, right, comparison, &left_interval)
    {
        return None;
    }
    let conclusion = planner.push(SignedArithmeticNode::IntervalCompare {
        left: left_node,
        right: right_node,
        comparison: result,
        result: goal.clone(),
    })?;
    Some(certificate(planner.nodes, conclusion))
}

fn term_interval_proves(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    comparison: Comparison,
    left_interval: &SignedArithmeticInterval,
) -> bool {
    if !matches!(comparison, Comparison::LessEqual) || left_interval.lower < 0 {
        return false;
    }
    let Bitvector32Term::ArithmeticShiftRight(operand, shift) = left else {
        return false;
    };
    terms_equal(operand, right) && shift.as_const().is_some_and(|value| value <= 31)
}

fn comparison_terms(
    proposition: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term, Comparison)> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        _ => return None,
    };
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::LessThan))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::LessEqual))
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::Equal))
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            Some((left.as_ref(), right.as_ref(), Comparison::Disequal))
        }
        // The remaining orderings are the same comparisons read from the
        // other side, in the orientation the kernel's evidence check uses.
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedLessEqual(left, right), false)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(right, left), false) => {
            Some((right.as_ref(), left.as_ref(), Comparison::LessThan))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedLessThan(left, right), false)
        | (ConditionTerm::Bitvector32SignedGreaterThan(right, left), false) => {
            Some((right.as_ref(), left.as_ref(), Comparison::LessEqual))
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum Comparison {
    LessThan,
    LessEqual,
    Equal,
    Disequal,
}

impl SignedArithmeticComparison {
    fn from_comparison(comparison: Comparison) -> Self {
        match comparison {
            Comparison::LessThan => Self::LessThan,
            Comparison::LessEqual => Self::LessEqual,
            Comparison::Equal => Self::Equal,
            Comparison::Disequal => Self::Disequal,
        }
    }
}

fn interval_proves(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    comparison: Comparison,
) -> bool {
    match comparison {
        Comparison::LessThan => left.upper < right.lower,
        Comparison::LessEqual => left.upper <= right.lower,
        Comparison::Equal => {
            left.lower == left.upper && left.lower == right.lower && right.lower == right.upper
        }
        Comparison::Disequal => left.upper < right.lower || right.upper < left.lower,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;

    #[test]
    fn remainder_add_transports_checked_residue_and_rejects_forgery() {
        let remainder = Bitvector32Term::Remainder(Box::new(var(1)), Box::new(constant(2)));
        let successor = Bitvector32Term::Remainder(
            Box::new(Bitvector32Term::Add(
                Box::new(var(1)),
                Box::new(constant(1)),
            )),
            Box::new(constant(2)),
        );
        for residue in [0, 1] {
            let premises = [
                le(constant(0), var(1)),
                lt(var(1), constant(i32::MAX)),
                le(constant(residue), remainder.clone()),
                le(remainder.clone(), constant(residue)),
            ];
            let goal = proposition(
                ConditionTerm::Bitvector32Equal(
                    Box::new(successor.clone()),
                    Box::new(constant(1 - residue)),
                ),
                true,
            );
            let plan = plan_signed_arithmetic_certificate(&goal, &premises).expect("parity plan");
            plan.check(&goal, &premises).unwrap();
            for mutation in 0..7 {
                let mut forged = plan.clone();
                let node = forged
                    .nodes
                    .iter_mut()
                    .find(|n| matches!(n, SignedArithmeticNode::IntervalRemainderAdd { .. }))
                    .unwrap();
                if let SignedArithmeticNode::IntervalRemainderAdd {
                    operand,
                    remainder,
                    addend,
                    divisor,
                    result,
                } = node
                {
                    match mutation {
                        0 => *operand = usize::MAX,
                        1 => *remainder = *operand,
                        2 => *divisor = 0,
                        3 => *divisor = -2,
                        4 => *divisor = 3,
                        5 => *addend = i32::MAX,
                        6 => result.lower = 7,
                        _ => unreachable!(),
                    }
                }
                assert!(
                    forged.check(&goal, &premises).is_err(),
                    "mutation {mutation}"
                );
            }
            let mut negative = premises.clone();
            negative[0] = le(constant(-10), var(1));
            assert!(plan.check(&goal, &negative).is_err());
            let mut overflow = premises.clone();
            overflow[1] = le(var(1), constant(i32::MAX));
            assert!(plan.check(&goal, &overflow).is_err());
        }
    }

    // An equality of one atom bounds it on both sides, so `x == 5` gives the
    // interval that proves `x - 1` defined and closes goals over it.
    #[test]
    fn equality_premise_bounds_its_atom_on_both_sides() {
        let eq = |left: Bitvector32Term, right: Bitvector32Term| {
            proposition(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
                true,
            )
        };
        let decrement = Bitvector32Term::Subtract(Box::new(var(1)), Box::new(constant(1)));
        let premises = [eq(var(1), constant(5))];
        for goal in [
            eq(decrement.clone(), constant(4)),
            le(decrement.clone(), constant(4)),
            ge(decrement.clone(), constant(4)),
        ] {
            let plan = plan_signed_arithmetic_certificate(&goal, &premises).expect("plan");
            plan.check(&goal, &premises).unwrap();
        }
        assert!(
            plan_signed_arithmetic_certificate(&eq(decrement, constant(5)), &premises).is_none()
        );
    }

    fn equal(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn plus(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
        Bitvector32Term::Add(Box::new(left), Box::new(right))
    }

    fn checked_plan(goal: &Proposition, premises: &[Proposition]) {
        for plan in [
            plan_signed_arithmetic_certificate(goal, premises).expect("automatic plan"),
            plan_signed_arithmetic_certificate_with_weakening(goal, premises)
                .expect("explicit plan"),
        ] {
            plan.check(goal, premises).unwrap();
        }
    }

    // A call's `a == b + 1`, with `b` bounded, bounds `a`: the goal's own
    // operation `a - 1` is defined from the converted premise.
    #[test]
    fn converted_equality_bounds_a_goal_operation() {
        let premises = [
            equal(var(1), plus(var(2), constant(1))),
            le(constant(0), var(2)),
            le(var(2), constant(500)),
        ];
        checked_plan(
            &equal(
                Bitvector32Term::Subtract(Box::new(var(1)), Box::new(constant(1))),
                var(2),
            ),
            &premises,
        );
    }

    // Two calls: `m == b + 1` converts first and bounds `m`, so `c == m + 1`
    // converts next; the goal's operands are bounded two equalities deep.
    #[test]
    fn equalities_convert_in_turn_and_chain() {
        let premises = [
            equal(var(3), plus(var(1), constant(1))),
            equal(var(1), plus(var(2), constant(1))),
            le(constant(0), var(2)),
            le(var(2), constant(500)),
        ];
        checked_plan(&equal(var(3), plus(var(2), constant(2))), &premises);
        checked_plan(
            &equal(
                Bitvector32Term::Subtract(Box::new(var(3)), Box::new(constant(2))),
                var(2),
            ),
            &premises,
        );
        assert!(
            plan_signed_arithmetic_certificate(
                &equal(var(3), plus(var(2), constant(3))),
                &premises
            )
            .is_none()
        );
    }

    // A bound through two equalities, and through one equality whose other
    // side is a sum of bounded atoms.
    #[test]
    fn bounds_substitute_through_equalities() {
        let premises = [
            equal(var(3), plus(var(1), constant(1))),
            equal(var(1), plus(var(2), constant(1))),
            le(constant(0), var(2)),
            le(var(2), constant(500)),
            le(constant(0), var(1)),
            le(var(1), constant(1000)),
        ];
        checked_plan(&le(var(3), constant(502)), &premises);
        assert!(
            plan_signed_arithmetic_certificate(&le(var(3), constant(501)), &premises).is_none()
        );
        let premises = [
            equal(var(3), plus(var(1), var(2))),
            le(constant(0), var(1)),
            le(var(1), constant(500)),
            le(constant(0), var(2)),
            le(var(2), constant(100)),
        ];
        checked_plan(&le(var(3), constant(1000)), &premises);
        assert!(
            plan_signed_arithmetic_certificate(&le(var(3), constant(599)), &premises).is_none()
        );
    }

    fn var(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(index))
    }

    fn constant(value: i32) -> Bitvector32Term {
        Bitvector32Term::Constant(value as u32)
    }

    fn proposition(condition: ConditionTerm, value: bool) -> Proposition {
        Proposition::ConditionIs(condition, value)
    }

    fn le(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn lt(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn ge(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn neq(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            false,
        )
    }

    fn defined_add(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedAddOverflows(Box::new(left), Box::new(right)),
            false,
        )
    }

    fn check_plan(goal: &Proposition, premises: &[Proposition]) -> SignedArithmeticCertificate {
        let plan =
            plan_signed_arithmetic_certificate(goal, premises).expect("planner should find proof");
        plan.check(goal, premises)
            .expect("independent checker should accept planner output");
        plan
    }

    #[test]
    fn symbolic_upper_premises_require_checked_operation_evidence() {
        let difference = Bitvector32Term::Subtract(Box::new(constant(1000)), Box::new(var(2)));
        let sum = Bitvector32Term::Add(Box::new(var(1)), Box::new(var(2)));
        let goal = le(var(1), constant(999));
        for premise in [
            le(var(1), difference.clone()),
            proposition(
                ConditionTerm::Bitvector32Equal(Box::new(var(1)), Box::new(difference)),
                true,
            ),
            le(sum, constant(1000)),
        ] {
            let premises = [
                premise,
                le(constant(1), var(2)),
                le(var(2), constant(1000)),
                le(constant(0), var(1)),
                le(var(1), constant(1000)),
            ];
            let plan = check_plan(&goal, &premises);
            assert!(
                plan_signed_arithmetic_certificate(&le(var(1), constant(998)), &premises).is_none()
            );
            let conversion = plan
                .nodes
                .iter()
                .position(|node| matches!(node, SignedArithmeticNode::AffinePremise { .. }))
                .expect("compound premise needs a checked conversion");
            for mutation in 0..5 {
                let mut forged = plan.clone();
                if let SignedArithmeticNode::AffinePremise {
                    source,
                    left_evidence,
                    right_evidence,
                    result,
                } = &mut forged.nodes[conversion]
                {
                    match mutation {
                        0 => *source = conversion,
                        1 => *left_evidence = conversion,
                        2 => *right_evidence = usize::MAX,
                        3 => *source = *left_evidence,
                        4 => result.constant -= 1,
                        _ => unreachable!(),
                    }
                }
                assert!(
                    forged.check(&goal, &premises).is_err(),
                    "mutation {mutation}"
                );
            }
            let mut overflowing = premises.clone();
            overflowing[1] = le(constant(i32::MIN), var(2));
            overflowing[2] = le(var(2), constant(i32::MAX));
            assert!(plan.check(&goal, &overflowing).is_err());
        }
        // A bound on the opaque operation itself is not recursive evidence
        // that the operation was defined.
        let overflowing_sum = Bitvector32Term::Add(Box::new(var(1)), Box::new(var(2)));
        let premises = [le(overflowing_sum, constant(1000)), le(constant(1), var(2))];
        assert!(plan_signed_arithmetic_certificate(&goal, &premises).is_none());
    }

    #[test]
    fn compound_premises_and_goal_share_checked_affine_evidence() {
        let cap = constant(i32::MAX - 1);
        let difference = Bitvector32Term::Subtract(Box::new(cap.clone()), Box::new(var(2)));
        let goal = le(
            Bitvector32Term::add(constant(1), var(1)),
            Bitvector32Term::Subtract(Box::new(constant(i32::MAX)), Box::new(var(2))),
        );
        let premises = [
            le(constant(0), var(1)),
            le(var(1), cap.clone()),
            le(constant(0), var(2)),
            le(var(2), cap),
            le(var(1), difference),
        ];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffinePremise { .. }))
        );
        assert!(matches!(
            plan.nodes[plan.conclusion],
            SignedArithmeticNode::AffineConclusionWithEvidence { .. }
        ));
        // A valid affine consequence cannot supply its own missing machine
        // definedness. The same certificate must reject changed bounds.
        let mut unsafe_goal = premises.clone();
        unsafe_goal[1] = le(var(1), constant(i32::MAX));
        unsafe_goal[4] = le(
            var(1),
            Bitvector32Term::Subtract(Box::new(constant(i32::MAX)), Box::new(var(2))),
        );
        assert!(plan_signed_arithmetic_certificate(&goal, &unsafe_goal).is_none());
        assert!(plan.check(&goal, &unsafe_goal).is_err());

        let unsafe_premise_goal = le(
            Bitvector32Term::add(constant(1), var(1)),
            Bitvector32Term::Subtract(Box::new(constant(i32::MIN + 1)), Box::new(var(2))),
        );
        let unsafe_premise = [
            le(constant(0), var(1)),
            le(var(1), constant(i32::MAX - 1)),
            le(constant(0), var(2)),
            le(var(2), constant(1)),
            le(
                var(1),
                Bitvector32Term::Subtract(Box::new(constant(i32::MIN)), Box::new(var(2))),
            ),
        ];
        // At x=0, y=1 the wrapped premise is true and the goal false.
        assert!(
            plan_signed_arithmetic_certificate(&unsafe_premise_goal, &unsafe_premise).is_none()
        );
    }

    fn biased_extent_bound(term: Bitvector32Term) -> Proposition {
        le(
            Bitvector32Term::BitwiseXor(Box::new(constant(i32::MIN)), Box::new(term)),
            constant(-1073741825),
        )
    }

    #[test]
    fn sign_bit_flip_on_either_comparison_side_rechecks() {
        let bounds = [lt(constant(0), var(1)), le(var(1), constant(4))];
        for constant_first in [false, true] {
            let flipped = if constant_first {
                Bitvector32Term::BitwiseXor(Box::new(constant(i32::MIN)), Box::new(var(1)))
            } else {
                Bitvector32Term::BitwiseXor(Box::new(var(1)), Box::new(constant(i32::MIN)))
            };
            for goal in [
                le(constant(i32::MIN + 1), flipped.clone()),
                le(flipped, constant(i32::MIN + 4)),
            ] {
                let plan = check_plan(&goal, &bounds);
                assert!(plan.check(&goal, &[]).is_err());
            }
        }
    }

    #[test]
    fn equality_from_bounds_through_a_pinned_constant_is_checked() {
        let goal = proposition(
            ConditionTerm::Bitvector32Equal(Box::new(var(1)), Box::new(var(2))),
            true,
        );
        let premises = vec![
            le(constant(0), var(1)),
            le(var(1), var(2)),
            proposition(
                ConditionTerm::Bitvector32Equal(Box::new(var(2)), Box::new(constant(0))),
                true,
            ),
        ];
        let plan = check_plan(&goal, &premises);
        for missing in 0..premises.len() {
            let mut unavailable = premises.clone();
            unavailable[missing] = le(constant(0), constant(1));
            assert!(plan.check(&goal, &unavailable).is_err());
            assert!(plan_signed_arithmetic_certificate(&goal, &unavailable).is_none());
        }
    }

    #[test]
    fn one_sided_direct_bound_does_not_hide_the_operand_bound() {
        // The back edge of `for (i = 0; i < n; i++)`: the new index is
        // `i0 + 1`, the invariant `0 <= i` bounds it directly from below
        // only, and the guard `i0 < n` with `n <= 1073741823` bounds its
        // operands from above. Citing the direct premise must not lose the
        // certificate the operands alone give.
        let i0 = var(10);
        let n = var(11);
        let next = Bitvector32Term::Add(Box::new(i0.clone()), Box::new(constant(1)));
        let goal = biased_extent_bound(next.clone());
        let without_direct = vec![
            le(constant(0), i0.clone()),
            lt(i0.clone(), n.clone()),
            le(n.clone(), constant(1073741823)),
        ];
        check_plan(&goal, &without_direct);
        let mut with_direct = vec![le(constant(0), next.clone())];
        with_direct.extend(without_direct);
        check_plan(&goal, &with_direct);
        // The bound is still owed: with `n` unbounded nothing derives it.
        let unbounded = vec![
            le(constant(0), next),
            le(constant(0), i0.clone()),
            lt(i0, n),
        ];
        assert!(plan_signed_arithmetic_certificate(&goal, &unbounded).is_none());
    }

    #[test]
    fn strict_transitive_bound_weakens_in_one_checked_certificate() {
        let j = var(93);
        let hi = var(94);
        let n = var(95);
        let goal = le(j.clone(), n.clone());
        let premises = vec![lt(j, hi.clone()), le(hi, n)];
        let plan = plan_signed_arithmetic_certificate_with_weakening(&goal, &premises)
            .expect("explicit arithmetic should find the weakened bound");
        plan.check(&goal, &premises)
            .expect("the kernel should accept the weakening certificate");
        assert!(
            plan.nodes
                .iter()
                .filter(|node| matches!(node, SignedArithmeticNode::Add { .. }))
                .count()
                >= 2
        );
    }

    #[test]
    fn predecessor_is_less_than_nonnegative_operand() {
        let n = var(90);
        let goal = lt(
            Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1))),
            n.clone(),
        );
        let plan = check_plan(&goal, &[le(constant(0), n)]);
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::AffineConclusion { .. }
                | SignedArithmeticNode::AffineConclusionWithEvidence { .. }
        )));
    }

    /// `x < 0` and `x >= 0` bound `x` into an empty interval. Planning an
    /// interval node for it produced a certificate the kernel then refused,
    /// which reached the user as `certificate rejected: DoesNotFollow`
    /// instead of the tactic's own prompt arithmetic failure. Declining is
    /// the honest answer: no interval exists.
    #[test]
    fn contradictory_bounds_plan_no_interval() {
        let x = var(91);
        let y = var(92);
        let goal = lt(
            y.clone(),
            Bitvector32Term::Subtract(Box::new(y), Box::new(x.clone())),
        );
        let premises = vec![lt(x.clone(), constant(0)), ge(x, constant(0))];
        assert!(
            plan_signed_arithmetic_certificate(&goal, &premises).is_none(),
            "an empty interval must not be planned as a certificate"
        );
    }

    #[test]
    fn predecessor_with_derived_leaf_and_extra_bounds() {
        let n = var(90);
        let predecessor = Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1)));
        let goal = lt(predecessor.clone(), n.clone());
        let premises = vec![
            le(constant(0), predecessor),
            le(constant(0), n.clone()),
            lt(constant(0), n),
        ];
        let plan = plan_signed_arithmetic_certificate(&goal, &premises);
        assert!(plan.is_some(), "{plan:?}");
        plan.expect("plan").check(&goal, &premises).expect("check");
    }

    #[test]
    fn predecessor_with_greater_equal_bound() {
        let n = var(90);
        let predecessor = Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1)));
        let goal = lt(predecessor.clone(), n.clone());
        let ge = proposition(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(n.clone()),
                Box::new(constant(0)),
            ),
            true,
        );
        let premises = vec![le(constant(0), predecessor), ge];
        let plan = plan_signed_arithmetic_certificate(&goal, &premises);
        assert!(plan.is_some(), "{plan:?}");
        plan.expect("plan").check(&goal, &premises).expect("check");
    }

    #[test]
    fn affine_equality_to_strict_bound_is_explicit() {
        let x = var(1);
        let equality = proposition(
            ConditionTerm::Bitvector32Equal(Box::new(x.clone()), Box::new(constant(1))),
            true,
        );
        let goal = lt(x, constant(1000));
        let plan = check_plan(&goal, std::slice::from_ref(&equality));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::EqualityToLessEqual { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::Add { .. }))
        );
    }

    #[test]
    fn bounded_addition_uses_exact_definedness_and_no_duplicate_premise() {
        let a = var(1);
        let b = var(2);
        let lower_a = le(constant(0), a.clone());
        let upper_a = le(a.clone(), constant(10));
        let lower_b = le(constant(0), b.clone());
        let upper_b = le(b.clone(), constant(20));
        let defined = defined_add(a.clone(), b.clone());
        let sum = Bitvector32Term::Add(Box::new(a), Box::new(b));
        let goal = le(sum, constant(30));
        let premises = vec![lower_a, upper_a, lower_b, upper_b, defined];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { index: 4, .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAdd { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::Add { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );
    }

    #[test]
    fn defined_addition_can_prove_a_lower_bound_without_upper_bounds() {
        let a = var(11);
        let b = var(12);
        let lower_a = le(constant(0), a.clone());
        let lower_b = le(constant(0), b.clone());
        let defined = defined_add(a.clone(), b.clone());
        let sum = Bitvector32Term::Add(Box::new(a), Box::new(b));
        let goal = le(constant(0), sum);
        let premises = vec![lower_a, lower_b, defined];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { index: 2, .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAdd { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .filter(|node| matches!(node, SignedArithmeticNode::Premise { .. }))
                .count()
                >= 2
        );

        let without_definedness = vec![premises[0].clone(), premises[1].clone()];
        assert!(plan_signed_arithmetic_certificate(&goal, &without_definedness).is_none());

        let mut tampered_definedness = plan.clone();
        let node = tampered_definedness
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::DefinedPremise { .. }))
            .expect("definedness node");
        if let SignedArithmeticNode::DefinedPremise { term, .. } = node {
            *term = Bitvector32Term::Add(Box::new(var(11)), Box::new(var(99)));
        }
        assert!(tampered_definedness.check(&goal, &premises).is_err());
    }

    #[test]
    fn bounded_doubling_reuses_bounds_without_definedness_or_duplicate_premises() {
        let n = var(13);
        let lower = le(constant(0), n.clone());
        let upper = le(n.clone(), constant(100));
        let doubled = Bitvector32Term::Add(Box::new(n.clone()), Box::new(n.clone()));
        let goal = le(doubled, constant(200));
        let plan = check_plan(&goal, &[lower, upper]);
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::IntervalAddBounded { left, right, .. } if left == right
        )));
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::Scale { coefficient, .. } if coefficient == &BigInt::from(2)
        )));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );
        assert!(
            !plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { .. }))
        );
        assert_eq!(
            plan.nodes
                .iter()
                .filter(|node| matches!(node, SignedArithmeticNode::Premise { .. }))
                .count(),
            2
        );

        let wide_upper = le(n.clone(), constant(i32::MAX));
        assert!(
            plan_signed_arithmetic_certificate(&goal, &[le(constant(0), n.clone()), wide_upper])
                .is_none()
        );

        let mut tampered = plan.clone();
        let node = tampered
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded { result, .. } = node {
            result.upper += 1;
        }
        assert!(
            tampered
                .check(
                    &goal,
                    &[le(constant(0), var(13)), le(var(13), constant(100))]
                )
                .is_err()
        );

        let mut tampered_scale = plan.clone();
        let node = tampered_scale
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::Scale { .. }))
            .expect("scale node");
        if let SignedArithmeticNode::Scale { coefficient, .. } = node {
            *coefficient = BigInt::from(3);
        }
        assert!(
            tampered_scale
                .check(
                    &goal,
                    &[le(constant(0), var(13)), le(var(13), constant(100))]
                )
                .is_err()
        );

        let premises = [le(constant(0), var(13)), le(var(13), constant(100))];
        let mut wrong_evidence_root = plan.clone();
        let node = wrong_evidence_root
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
            .expect("affine conclusion node");
        if let SignedArithmeticNode::AffineConclusion { evidence, .. } = node {
            *evidence = 0;
        }
        assert!(wrong_evidence_root.check(&goal, &premises).is_err());

        let mut wrong_child = plan.clone();
        let node = wrong_child
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded { left, .. } = node {
            *left = usize::MAX;
        }
        assert!(wrong_child.check(&goal, &premises).is_err());

        let mut wrong_operator = plan.clone();
        let node = wrong_operator
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded {
            left,
            right,
            result,
        } = node
        {
            let left = *left;
            let right = *right;
            let result = result.clone();
            *node = SignedArithmeticNode::IntervalSubtract {
                left,
                right,
                defined: 0,
                result,
            };
        }
        assert!(wrong_operator.check(&goal, &premises).is_err());

        let mut wrong_expression = plan.clone();
        let node = wrong_expression
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
            .expect("affine conclusion node");
        if let SignedArithmeticNode::AffineConclusion { result, .. } = node {
            *result = le(
                Bitvector32Term::Add(Box::new(var(13)), Box::new(var(14))),
                constant(200),
            );
        }
        assert!(wrong_expression.check(&goal, &premises).is_err());
    }

    #[test]
    fn bounded_remainder_shift_mask_product_and_sign_flip_are_planned() {
        let x = var(3);
        let lower = le(constant(0), x.clone());
        let upper = le(x.clone(), constant(10));

        let remainder = Bitvector32Term::Remainder(Box::new(x.clone()), Box::new(constant(7)));
        let remainder_goal = le(remainder.clone(), constant(6));
        let remainder_defined = proposition(
            ConditionTerm::Bitvector32SignedDivideOverflows(
                Box::new(x.clone()),
                Box::new(constant(7)),
            ),
            false,
        );
        let remainder_plan = check_plan(
            &remainder_goal,
            &[lower.clone(), upper.clone(), remainder_defined],
        );
        assert!(
            remainder_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalRemainder { .. }))
        );

        let shift = Bitvector32Term::ShiftLeft(Box::new(x.clone()), Box::new(constant(2)));
        let shift_goal = le(shift.clone(), constant(40));
        let shift_defined = proposition(
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(
                Box::new(x.clone()),
                Box::new(constant(2)),
            ),
            false,
        );
        let shift_plan = check_plan(&shift_goal, &[lower.clone(), upper.clone(), shift_defined]);
        assert!(
            shift_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalShiftLeft { .. }))
        );

        let mask = Bitvector32Term::BitwiseAnd(Box::new(x.clone()), Box::new(constant(255)));
        let mask_goal = le(mask, constant(255));
        let mask_plan = check_plan(&mask_goal, &[]);
        assert!(
            mask_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalBitwiseAnd { .. }))
        );

        let product = Bitvector32Term::Multiply(Box::new(x.clone()), Box::new(x.clone()));
        let product_goal = le(product.clone(), constant(100));
        let product_defined = proposition(
            ConditionTerm::Bitvector32SignedMultiplyOverflows(
                Box::new(x.clone()),
                Box::new(x.clone()),
            ),
            false,
        );
        let product_plan = check_plan(
            &product_goal,
            &[lower.clone(), upper.clone(), product_defined],
        );
        assert!(
            product_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalMultiply { .. }))
        );

        let flipped =
            Bitvector32Term::BitwiseXor(Box::new(x.clone()), Box::new(constant(i32::MIN)));
        let flip_goal = le(flipped, constant(-2_147_483_638));
        let flip_plan = check_plan(&flip_goal, &[lower, upper]);
        assert!(
            flip_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalSignBitFlip { .. }))
        );
    }

    #[test]
    fn deep_supported_addition_builds_iterative_interval_affine_evidence() {
        let x = var(9);
        let lower = le(constant(0), x.clone());
        let upper = le(x.clone(), constant(1));
        let mut term = x.clone();
        for _ in 0..127 {
            term = Bitvector32Term::Add(Box::new(term), Box::new(x.clone()));
        }
        let goal = le(term, constant(128));
        let plan = check_plan(&goal, &[lower, upper]);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
        );
        assert!(plan
            .nodes
            .iter()
            .any(|node| matches!(node, SignedArithmeticNode::Scale { coefficient, .. } if coefficient == &BigInt::from(128))));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );

        let overflowing_inner = Bitvector32Term::Add(Box::new(x.clone()), Box::new(constant(1)));
        let final_in_range =
            Bitvector32Term::Subtract(Box::new(overflowing_inner), Box::new(constant(1)));
        let final_goal = le(final_in_range, constant(i32::MAX));
        let bounds = [le(constant(0), x.clone()), le(x, constant(i32::MAX))];
        assert!(plan_signed_arithmetic_certificate(&final_goal, &bounds).is_none());
    }

    #[test]
    fn indexed_operation_lookup_scales_with_deep_terms_and_unrelated_facts() {
        let mut measurements = Vec::new();
        for (depth, unrelated) in [(8usize, 4usize), (16, 8), (32, 16), (64, 32)] {
            let x = var(72);
            let mut term = x.clone();
            for _ in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(x.clone()));
            }
            let goal = le(term, constant(depth as i32 + 1));
            let mut premises = vec![le(constant(0), x.clone()), le(x, constant(1))];
            premises
                .extend((0..unrelated).map(|index| le(var(10_000 + index as u64), constant(0))));
            let (plan, work) =
                crate::instrumentation::measure_deterministic_work(|| check_plan(&goal, &premises));
            assert!(plan.nodes.len() <= 12 * depth + 32);
            measurements.push(work);
        }
        assert!(
            measurements
                .windows(2)
                .all(|pair| pair[1] <= 3 * pair[0] + 256),
            "indexed operation lookup should avoid depth-by-fact rescans: {measurements:?}"
        );
    }

    #[test]
    fn nested_affine_bounds_have_linear_certificate_size() {
        for depth in [4usize, 8, 16, 32] {
            let x = var(73);
            let mut term = x.clone();
            let mut premises = vec![le(constant(0), x.clone()), le(x, constant(1))];
            for index in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(constant(1)));
                if index + 1 < depth {
                    premises.push(le(term.clone(), constant(index as i32 + 2)));
                }
            }
            let goal_term = Bitvector32Term::BitwiseAnd(Box::new(term), Box::new(constant(255)));
            let goal = le(goal_term, constant(255));
            let plan = plan_signed_arithmetic_certificate(&goal, &premises)
                .unwrap_or_else(|| panic!("no plan at depth {depth}"));
            plan.check(&goal, &premises)
                .expect("compact plan must check");
            let direct_nodes = plan
                .nodes
                .iter()
                .filter(|node| {
                    matches!(node, SignedArithmeticNode::IntervalFromAffineDirect { .. })
                })
                .count();
            assert!(
                direct_nodes <= 1,
                "a nested chain needs one direct root at most"
            );
            assert!(plan.nodes.len() <= 12 * depth + 32);
        }
    }

    #[test]
    fn a_nonnegative_nonzero_value_plans_a_strict_lower_bound() {
        let n = var(41);
        let goal = lt(constant(0), n.clone());
        let premises = [ge(n.clone(), constant(0)), neq(n, constant(0))];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::StrictFromDisequal { .. }))
        );
    }

    #[test]
    fn the_reversed_disequality_spelling_plans_the_same_strict_lower_bound() {
        let n = var(42);
        let goal = lt(constant(0), n.clone());
        let premises = [ge(n.clone(), constant(0)), neq(constant(0), n)];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::StrictFromDisequal { .. }))
        );
    }

    #[test]
    fn a_greater_equal_goal_over_a_subtraction_is_planned() {
        let n = var(43);
        let predecessor = Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1)));
        let goal = ge(predecessor, constant(0));
        let premises = [ge(n, constant(1))];
        check_plan(&goal, &premises);
    }

    #[test]
    fn a_disequality_on_another_value_plans_no_strict_lower_bound() {
        let n = var(44);
        let goal = lt(constant(0), n.clone());
        let premises = [ge(n.clone(), constant(0)), neq(n, constant(1))];
        assert!(plan_signed_arithmetic_certificate(&goal, &premises).is_none());
    }

    #[test]
    fn planner_rejects_node_count_above_the_certificate_bound() {
        let mut planner = Planner::new(&[], &[], false);
        let result = SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: SignedArithmeticRelation::LessEqual,
            terms: BTreeMap::new(),
            constant: BigInt::zero(),
        };
        for _ in 0..MAX_NODES {
            assert!(
                planner
                    .push(SignedArithmeticNode::Trivial {
                        result: result.clone(),
                    })
                    .is_some()
            );
        }
        assert!(
            planner
                .push(SignedArithmeticNode::Trivial { result })
                .is_none()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/surface/checking/signed_arithmetic_planner/tests.rs");
    }
}
