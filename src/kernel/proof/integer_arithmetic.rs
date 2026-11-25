//! Affine Integer claims and internal arithmetic search plans.
//! Plans are expanded into ordinary proof steps; they are not proof objects.
use super::fact_keys::retained_integer_fold_alpha_key;
pub(crate) use super::integer_affine_atoms::IntegerAffineAtom;
use super::integer_affine_atoms::{IntegerFoldAtomRecord, intern_integer_fold_key};

use crate::kernel::{
    IntegerComparisonOperator, IntegerTerm, KernelIntegerOperator, KernelTerm, KernelTermNode,
    OldConditionTerm, Proposition, SharedIntegerTerm, StoredConditionTerm,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// The normalized relation `sum(coeff * variable) + constant REL 0`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerAffineRelation {
    LessEqual,
    Equal,
}

/// A normalized affine result used while selecting an ordinary derivation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerAffineClaim {
    pub(crate) relation: IntegerAffineRelation,
    pub(crate) terms: BTreeMap<IntegerAffineAtom, BigInt>,
    pub(crate) constant: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerArithmeticNode {
    Premise {
        index: usize,
        result: IntegerAffineClaim,
    },
    Scale {
        source: usize,
        coefficient: BigInt,
        result: IntegerAffineClaim,
    },
    Add {
        left: usize,
        right: usize,
        result: IntegerAffineClaim,
    },
    /// Turn an equality into one of its two non-strict directions.
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: IntegerAffineClaim,
    },
    /// Close an equality from opposite non-strict bounds.
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: IntegerAffineClaim,
    },
    /// Context-free tautologies such as `x + 1 > x` and `x - x == 0`.
    Trivial { result: IntegerAffineClaim },
    /// Assume the integer negation of a non-strict goal: from the goal
    /// `t <= 0`, the claim `-t + 1 <= 0`. A certificate that uses it must
    /// conclude with the goal or with a contradiction.
    NegatedGoal { result: IntegerAffineClaim },

    /// A machine value lies in its type's range: `MIN <= to_integer(v)`,
    /// or with `upper`, `to_integer(v) <= MAX`. `value` is the machine
    /// observation `to_integer(v)`; any other term is refused.
    TypeRange {
        value: IntegerTerm,
        upper: bool,
        result: IntegerAffineClaim,
    },
    /// An unsigned machine quotient, shift, or remainder by a constant is
    /// bounded by its operand ([`operation_bound`]): for `q = x / c`, or
    /// `q = x >> k` with `c = 2^k`, `c * q <= x`, or with `upper`,
    /// `x <= c * q + (c - 1)`; for `r = x % c`, with `upper`, `r <= c - 1`.
    /// `value` is the observation `to_integer(q)` or `to_integer(r)`.
    OperationBound {
        value: IntegerTerm,
        upper: bool,
        result: IntegerAffineClaim,
    },
    /// A premise `v != m`, where `m` is the minimum of `v`'s machine type,
    /// gives `m + 1 <= v`; at the type's maximum it gives `v <= m - 1`
    /// ([`excluded_type_bound`]).
    ExcludedTypeBound {
        index: usize,
        result: IntegerAffineClaim,
    },
    /// A non-strict bound and a disequality of the same difference give the
    /// strict bound: from node `bound`, `t <= 0`, and premise `disequal`,
    /// `l != r` with `l - r` equal to `t` or `-t`, the claim `t + 1 <= 0`
    /// ([`integer_disequality_claims`]). Over the integers `t <= 0` and
    /// `t != 0` leave `t <= -1`. The Integer counterpart of the
    /// `signed_int32` certificate's `less_than_from_not_equal`, stated once
    /// for every format and for plain `Integer`.
    StrictFromDisequal {
        bound: usize,
        disequal: usize,
        result: IntegerAffineClaim,
    },
}

/// A flat Integer arithmetic search plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerArithmeticPlan {
    pub(crate) nodes: Vec<IntegerArithmeticNode>,
    pub(crate) conclusion: usize,
}

fn charge_integer_product(left: &BigInt, right: &BigInt) -> bool {
    let units = (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1);
    if crate::instrumentation::deadline_exceeded_with_work(units) {
        return false;
    }
    true
}

pub(crate) fn scale_claim(
    claim: &IntegerAffineClaim,
    coefficient: &BigInt,
) -> Option<IntegerAffineClaim> {
    let mut terms = Vec::with_capacity(claim.terms.len());
    for (term, value) in &claim.terms {
        if !charge_integer_product(value, coefficient) {
            return None;
        }
        let value = value * coefficient;
        if !value.is_zero() {
            terms.push((term.clone(), value));
        }
    }
    if !charge_integer_product(&claim.constant, coefficient) {
        return None;
    }
    Some(IntegerAffineClaim {
        relation: claim.relation.clone(),
        terms: terms.into_iter().collect(),
        constant: &claim.constant * coefficient,
    })
}

pub(crate) fn add_claim(
    left: &IntegerAffineClaim,
    right: &IntegerAffineClaim,
) -> IntegerAffineClaim {
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        let value = terms.get(term).cloned().unwrap_or_else(BigInt::zero) + coefficient;
        if value.is_zero() {
            terms.remove(term);
        } else {
            terms.insert(term.clone(), value);
        }
    }
    IntegerAffineClaim {
        relation: left.relation.clone(),
        terms,
        constant: &left.constant + &right.constant,
    }
}

pub(crate) fn negate_claim(
    claim: &IntegerAffineClaim,
    relation: IntegerAffineRelation,
) -> IntegerAffineClaim {
    let terms = claim
        .terms
        .iter()
        .map(|(term, coefficient)| (term.clone(), -coefficient))
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .collect();
    IntegerAffineClaim {
        relation,
        terms,
        constant: -&claim.constant,
    }
}

/// The machine value and constant of a disequality `v != m`, read as an
/// Integer comparison: natively, `x != 0u64`, or as written,
/// `to_integer(v) != m`, either side first.
fn integer_disequality(
    proposition: &Proposition,
) -> Option<(crate::kernel::SharedMachineIntegerTerm, BigInt)> {
    let (condition, _) = affine_condition(proposition)?;
    if let Some((_, arguments)) = retained_integer_comparison(condition)
        && arguments.iter().all(|operand| {
            matches!(
                operand.node(),
                KernelTermNode::Fold(_)
                    | KernelTermNode::Variable(_)
                    | KernelTermNode::IntegerLiteral(_)
                    | KernelTermNode::IntegerOperation { .. }
            )
        })
    {
        // A machine type endpoint requires a top-level machine observation.
        return None;
    }
    let readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            proposition,
        );
    let reading = readings.first().unwrap_or(proposition);
    let (left, right) = match reading {
        condition_source @ Proposition::ConditionIs(_, _)
            if let Some(
                (OldConditionTerm::IntegerEqual(left, right), false)
                | (OldConditionTerm::IntegerNotEqual(left, right), true),
            ) = condition_source.old_condition() =>
        {
            (left, right)
        }
        Proposition::Not(body) => match body.as_ref() {
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((OldConditionTerm::IntegerEqual(left, right), _)) =
                    condition_source_0.old_condition() =>
            {
                (left, right)
            }
            _ => return None,
        },
        _ => return None,
    };
    // The written constant may be literal arithmetic, such as INT_MIN spelled
    // `-2147483647 - 1`. Read its value from this selected premise; do not rely
    // on admission having filed a folded native copy of the disequality.
    match (left.as_ref(), right.as_ref()) {
        (IntegerTerm::Machine(value), _) => Some((value.clone(), literal_integer_value(right)?)),
        (_, IntegerTerm::Machine(value)) => Some((value.clone(), literal_integer_value(left)?)),
        _ => None,
    }
}

/// The differences `l - r` of a disequality `l != r`, as `Equal` claims
/// whose terms and constant are the difference's, one per exact reading (a
/// native disequality of 32- or 64-bit words has two, as for
/// [`integer_affine_claims`]). Empty when the proposition is no
/// disequality, or one whose difference has no atom: a disequality of
/// constants is already a claim. `StrictFromDisequal` reads it.
pub(crate) fn integer_disequality_claims(proposition: &Proposition) -> Vec<IntegerAffineClaim> {
    let Some((condition, value)) = affine_condition(proposition) else {
        return Vec::new();
    };
    if let Some((operator, _)) = retained_integer_comparison(condition)
        && !matches!(
            (operator, value),
            (IntegerComparisonOperator::NotEqual, true) | (IntegerComparisonOperator::Equal, false)
        )
    {
        return Vec::new();
    }
    let mut context = IntegerAffineCollectionContext::default();
    if let Some((_, arguments)) = retained_integer_comparison(condition)
        && let Some(difference) =
            affine_difference(arguments.each_ref(), |operand, weight, terms, constant| {
                collect_retained_affine_operand(operand, weight, terms, constant, &mut context)
            })
    {
        return (!difference.terms.is_empty())
            .then_some(difference)
            .into_iter()
            .collect();
    }
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return Vec::new();
    }
    let readings = if condition.operand_view().is_integer_comparison() {
        vec![Proposition::condition_is(condition.clone(), value)]
    } else {
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(condition.clone(), value),
        )
    };
    let mut differences = Vec::with_capacity(readings.len());
    for reading in &readings {
        let (left, right) = match reading {
            condition_source @ Proposition::ConditionIs(_, _)
                if let Some(
                    (OldConditionTerm::IntegerNotEqual(left, right), true)
                    | (OldConditionTerm::IntegerEqual(left, right), false),
                ) = condition_source.old_condition() =>
            {
                (left, right)
            }
            _ => continue,
        };
        if let Some(difference) =
            affine_difference([left, right], |operand, weight, terms, constant| {
                collect_retained_affine_operand(
                    operand.root(),
                    weight,
                    terms,
                    constant,
                    &mut context,
                )
            })
            && !difference.terms.is_empty()
            && !differences.contains(&difference)
        {
            differences.push(difference);
        }
    }
    differences
}

/// The bound a disequality with a machine type's endpoint gives:
/// `v != MIN` is `MIN + 1 <= v`, and `v != MAX` is `v <= MAX - 1`. A
/// disequality with any other constant is no bound.
pub(crate) fn excluded_type_bound(premise: &Proposition) -> Option<Proposition> {
    let (value, constant) = integer_disequality(premise)?;
    let (min, max) = value.ty().format().bounds();
    let observed = IntegerTerm::Machine(value);
    let condition = if constant == min {
        OldConditionTerm::integer_less_equal(IntegerTerm::constant(min + BigInt::one()), observed)
    } else if constant == max {
        OldConditionTerm::integer_less_equal(observed, IntegerTerm::constant(max - BigInt::one()))
    } else {
        return None;
    };
    Some(Proposition::condition_is(condition, true))
}

pub(crate) fn machine_type_range_claim(
    value: &crate::kernel::SharedMachineIntegerTerm,
    upper: bool,
) -> Option<IntegerAffineClaim> {
    integer_affine_claim(&crate::kernel::machine_integer::range::range_fact(
        value, upper,
    ))
}

/// The machine values that are atoms of `proposition`'s affine claim, each
/// once, in first-occurrence order.
pub(crate) fn integer_affine_machine_values(
    proposition: &Proposition,
) -> Vec<crate::kernel::SharedMachineIntegerTerm> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    if let Some((operator, operands)) = retained_integer_comparison(condition) {
        return if *operator == IntegerComparisonOperator::NotEqual {
            Vec::new()
        } else {
            retained_affine_machine_values(operands.each_ref())
        };
    }
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return Vec::new();
    }
    // A native comparison observes the machine values its Integer reading
    // does, as `integer_affine_claim` reads it.
    if !matches!(
        condition.old_form(),
        crate::kernel::integer_comparison_condition!(_, _)
    ) && let Some(reading) =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(condition.clone(), value),
        )
        .into_iter()
        .next()
    {
        return integer_affine_machine_values(&reading);
    }
    let (left, right) = match condition.old_form() {
        OldConditionTerm::IntegerLessThan(left, right)
        | OldConditionTerm::IntegerLessEqual(left, right)
        | OldConditionTerm::IntegerGreaterThan(left, right)
        | OldConditionTerm::IntegerGreaterEqual(left, right)
        | OldConditionTerm::IntegerEqual(left, right) => (left, right),
        _ => return Vec::new(),
    };
    retained_affine_machine_values([left.root(), right.root()])
}

fn retained_affine_machine_values(
    [left, right]: [&KernelTerm; 2],
) -> Vec<crate::kernel::SharedMachineIntegerTerm> {
    let mut seen = HashSet::new();
    let mut values = Vec::new();
    let mut pending = vec![right, left];
    while let Some(root) = pending.pop() {
        if !seen.insert(root.id()) {
            continue;
        }
        match root.node() {
            KernelTermNode::MachineObservation { .. } => {
                if let Some(observation) = root.exact_shared_integer_observation() {
                    values.push(observation);
                }
            }
            KernelTermNode::IntegerOperation {
                operator: KernelIntegerOperator::Multiply,
                arguments,
            } => match (arguments[0].node(), arguments[1].node()) {
                (KernelTermNode::IntegerLiteral(_), _) => pending.push(&arguments[1]),
                (_, KernelTermNode::IntegerLiteral(_)) => pending.push(&arguments[0]),
                _ => {}
            },
            KernelTermNode::IntegerOperation {
                operator:
                    KernelIntegerOperator::Negate
                    | KernelIntegerOperator::Add
                    | KernelIntegerOperator::Subtract,
                arguments,
            } => pending.extend(arguments.iter().rev()),
            _ => {}
        }
    }
    values
}

/// Per-claim cache for fold identities.  This is deliberately scoped to one
/// normalization: a shared source node is never alpha-keyed once for each
/// occurrence in the same claim, while load-registry epochs cannot make a
/// process-wide source-id cache stale.
#[derive(Default)]
struct IntegerAffineCollectionContext {
    constants: HashMap<u64, Option<BigInt>>,
    retained_fold_atoms: HashMap<u64, Arc<IntegerFoldAtomRecord>>,
}

/// Normalize one integer proposition for use in a certificate node.
///
/// This is intentionally a small, context-free conversion. The returned
/// atom map contains only checked source identities: variables, machine
/// observations, pure applications, state-aware opaque folds, and complete
/// symbolic products and truncating terms. An
/// arbitrary deep Integer term is never used directly as a map key.
/// Every Integer affine claim `proposition` holds exactly when. A native
/// equality of 32- or 64-bit words does not say whether its operands are
/// signed, and both readings are exact, so it has two; any other proposition
/// has at most one. A promoted `int32` comparison of widenings (C's
/// comparison of an 8- or 16-bit value) is the Integer comparison of its
/// sides' values. The kernel accepts a premise or goal as any of them.
pub(crate) fn integer_affine_claims(proposition: &Proposition) -> Vec<IntegerAffineClaim> {
    let mut context = IntegerAffineCollectionContext::default();
    integer_affine_claims_with_context(proposition, &mut context)
}

fn integer_affine_claims_with_context(
    proposition: &Proposition,
    context: &mut IntegerAffineCollectionContext,
) -> Vec<IntegerAffineClaim> {
    let readings = match proposition {
        Proposition::ConditionIs(condition, _)
            if !condition.operand_view().is_integer_comparison() =>
        {
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                proposition,
            )
        }
        _ => Vec::new(),
    };
    if readings.is_empty() {
        return integer_affine_claim_with_context(proposition, context)
            .into_iter()
            .collect();
    }
    let mut claims = Vec::with_capacity(readings.len());
    for reading in &readings {
        if let Some(claim) = integer_affine_claim_with_context(reading, context)
            && !claims.contains(&claim)
        {
            claims.push(claim);
        }
    }
    claims
}

/// Whether `proposition` is an Integer affine claim as written, rather than
/// a native comparison read as one. Diagnostics name the fragment a goal is
/// written in.
pub(crate) fn written_integer_affine_claim(proposition: &Proposition) -> bool {
    let native = match proposition {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value)
                if !condition.operand_view().is_integer_comparison() =>
            {
                !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    &Proposition::condition_is(condition.clone(), !value),
                )
                .is_empty()
            }
            _ => false,
        },
        Proposition::ConditionIs(condition, _)
            if !condition.operand_view().is_integer_comparison() =>
        {
            !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                proposition,
            )
            .is_empty()
        }
        _ => false,
    };
    !native && integer_affine_claim(proposition).is_some()
}

pub(crate) fn integer_affine_claim(proposition: &Proposition) -> Option<IntegerAffineClaim> {
    let mut context = IntegerAffineCollectionContext::default();
    integer_affine_claim_with_context(proposition, &mut context)
}

fn integer_affine_claim_with_context(
    proposition: &Proposition,
    context: &mut IntegerAffineCollectionContext,
) -> Option<IntegerAffineClaim> {
    let (condition, value) = affine_condition(proposition)?;
    if let Some((operator, arguments)) = retained_integer_comparison(condition)
        && let Some(claim) = integer_affine_comparison_claim(
            *operator,
            value,
            arguments.each_ref(),
            |operand, weight, terms, constant| {
                collect_retained_affine_operand(operand, weight, terms, constant, context)
            },
        )
    {
        return claim;
    }
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
    }
    // A native comparison of machine values holds exactly when the Integer
    // comparison of their exact observations does, so it is that Integer
    // claim. One constant-size reading; nothing else is consulted.
    if !matches!(
        condition.old_form(),
        crate::kernel::integer_comparison_condition!(_, _) | OldConditionTerm::Constant(_)
    ) && let Some(reading) =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(condition.clone(), value),
        )
        .into_iter()
        .next()
    {
        return integer_affine_claim_with_context(&reading, context);
    }
    if let OldConditionTerm::Constant(actual) = condition.old_form() {
        return Some(IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms: BTreeMap::new(),
            constant: if *actual == value {
                BigInt::zero()
            } else {
                BigInt::one()
            },
        });
    }
    use IntegerComparisonOperator as Op;
    let (operator, operands) = match condition.old_form() {
        OldConditionTerm::IntegerLessThan(left, right) => (Op::LessThan, [left, right]),
        OldConditionTerm::IntegerLessEqual(left, right) => (Op::LessEqual, [left, right]),
        OldConditionTerm::IntegerGreaterThan(left, right) => (Op::GreaterThan, [left, right]),
        OldConditionTerm::IntegerGreaterEqual(left, right) => (Op::GreaterEqual, [left, right]),
        OldConditionTerm::IntegerEqual(left, right) => (Op::Equal, [left, right]),
        OldConditionTerm::IntegerNotEqual(left, right) => (Op::NotEqual, [left, right]),
        _ => return None,
    };
    integer_affine_comparison_claim(
        operator,
        value,
        operands,
        |operand, weight, terms, constant| {
            collect_retained_affine_operand(operand.root(), weight, terms, constant, context)
        },
    )?
}

fn retained_integer_comparison(
    condition: &StoredConditionTerm,
) -> Option<(&IntegerComparisonOperator, &[KernelTerm; 2])> {
    let KernelTermNode::IntegerCompare {
        operator,
        arguments,
    } = condition.root()?.node()
    else {
        return None;
    };
    Some((operator, arguments))
}

fn affine_condition(proposition: &Proposition) -> Option<(&StoredConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition, *value)),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => Some((condition, !value)),
            _ => None,
        },
        _ => None,
    }
}

fn affine_difference<T>(
    [left, right]: [T; 2],
    mut collect: impl FnMut(
        T,
        &BigInt,
        &mut BTreeMap<IntegerAffineAtom, BigInt>,
        &mut BigInt,
    ) -> Option<()>,
) -> Option<IntegerAffineClaim> {
    let mut terms = BTreeMap::new();
    let mut constant = BigInt::zero();
    collect(left, &BigInt::one(), &mut terms, &mut constant)?;
    collect(right, &BigInt::from(-1), &mut terms, &mut constant)?;
    Some(IntegerAffineClaim {
        relation: IntegerAffineRelation::Equal,
        terms,
        constant,
    })
}

/// The outer option reports whether both operands could be read. The inner
/// option reports whether the comparison has an affine claim.
fn integer_affine_comparison_claim<T>(
    operator: IntegerComparisonOperator,
    value: bool,
    [left, right]: [T; 2],
    collect: impl FnMut(T, &BigInt, &mut BTreeMap<IntegerAffineAtom, BigInt>, &mut BigInt) -> Option<()>,
) -> Option<Option<IntegerAffineClaim>> {
    use IntegerComparisonOperator as Op;
    let (reverse, strict) = match (operator, value) {
        (Op::LessThan, true) | (Op::GreaterEqual, false) => (false, true),
        (Op::GreaterThan, true) | (Op::LessEqual, false) => (true, true),
        (Op::GreaterEqual, true) | (Op::LessThan, false) => (true, false),
        _ => (false, false),
    };
    let operands = if reverse {
        [right, left]
    } else {
        [left, right]
    };
    let mut difference = affine_difference(operands, collect)?;

    let relation = match (operator, value) {
        (Op::Equal, true) | (Op::NotEqual, false) => IntegerAffineRelation::Equal,
        (Op::Equal, false) | (Op::NotEqual, true) => {
            return Some(
                (difference.terms.is_empty() && !difference.constant.is_zero()).then_some(
                    IntegerAffineClaim {
                        relation: IntegerAffineRelation::LessEqual,
                        terms: difference.terms,
                        constant: BigInt::from(-1),
                    },
                ),
            );
        }
        _ => IntegerAffineRelation::LessEqual,
    };
    if strict {
        if crate::instrumentation::deadline_exceeded_with_work(
            difference.constant.bits() as usize + 1,
        ) {
            return None;
        }
        difference.constant += BigInt::one();
    }
    difference.relation = relation;
    Some(Some(difference))
}

fn collect_retained_affine_operand(
    root: &KernelTerm,
    coefficient: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
    context: &mut IntegerAffineCollectionContext,
) -> Option<()> {
    let mut scheduled = HashSet::new();
    let mut pending = vec![(root, false)];
    let mut order = Vec::new();
    while let Some((node, expanded)) = pending.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        if !scheduled.insert(node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        pending.push((node, true));
        if node.is_literal_integer_arithmetic() {
            collect_integer_constants(node, &mut context.constants)?;
            if context
                .constants
                .get(&node.id())
                .and_then(Option::as_ref)
                .is_some()
            {
                continue;
            }
        }
        if let KernelTermNode::IntegerOperation {
            operator,
            arguments,
        } = node.node()
        {
            match operator {
                KernelIntegerOperator::Negate
                | KernelIntegerOperator::Add
                | KernelIntegerOperator::Subtract => {
                    pending.extend(arguments.iter().rev().map(|child| (child, false)));
                }
                KernelIntegerOperator::Multiply => {
                    for child in arguments {
                        if child.is_literal_integer_arithmetic() {
                            collect_integer_constants(child, &mut context.constants)?;
                        }
                    }
                    if let Some((_, child)) = affine_factor(arguments, &context.constants) {
                        pending.push((child, false));
                    }
                }
                _ => {}
            }
        }
    }

    let mut weights = HashMap::from([(root.id(), coefficient.clone())]);
    for term in order.into_iter().rev() {
        let Some(weight) = weights.remove(&term.id()) else {
            continue;
        };
        if crate::instrumentation::deadline_exceeded_with_work(weight.bits() as usize + 1) {
            return None;
        }
        if weight.is_zero() {
            continue;
        }
        if let Some(value) = context.constants.get(&term.id()).and_then(Option::as_ref) {
            if !charge_integer_product(&weight, value)
                || crate::instrumentation::deadline_exceeded_with_work(
                    constant.bits() as usize + value.bits() as usize + weight.bits() as usize + 1,
                )
            {
                return None;
            }
            *constant += weight * value;
            continue;
        }
        let KernelTermNode::IntegerOperation {
            operator,
            arguments,
        } = term.node()
        else {
            collect_retained_affine_leaf(term, &weight, terms, constant, context)?;
            continue;
        };
        let ok = match operator {
            KernelIntegerOperator::Negate => add_weight(&mut weights, arguments[0].id(), -weight),
            KernelIntegerOperator::Add | KernelIntegerOperator::Subtract => {
                add_weight(&mut weights, arguments[0].id(), weight.clone())
                    && add_weight(
                        &mut weights,
                        arguments[1].id(),
                        if *operator == KernelIntegerOperator::Subtract {
                            -weight
                        } else {
                            weight
                        },
                    )
            }
            KernelIntegerOperator::Multiply
                if let Some((factor, child)) = affine_factor(arguments, &context.constants) =>
            {
                charge_integer_product(&weight, factor)
                    && add_weight(&mut weights, child.id(), weight * factor)
            }
            _ => {
                let reading = SharedIntegerTerm::from_root(term.clone()).read_through();
                add_atom_weight(terms, IntegerAffineAtom::Nonlinear(reading.id()), weight)?;
                true
            }
        };
        if !ok {
            return None;
        }
    }
    Some(())
}

fn affine_factor<'term, 'constant>(
    arguments: &'term [KernelTerm],
    constants: &'constant HashMap<u64, Option<BigInt>>,
) -> Option<(&'constant BigInt, &'term KernelTerm)> {
    let [left, right] = arguments else {
        return None;
    };
    constants
        .get(&left.id())
        .and_then(Option::as_ref)
        .map(|factor| (factor, right))
        .or_else(|| {
            constants
                .get(&right.id())
                .and_then(Option::as_ref)
                .map(|factor| (factor, left))
        })
}

fn collect_retained_affine_leaf(
    operand: &KernelTerm,
    coefficient: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
    context: &mut IntegerAffineCollectionContext,
) -> Option<()> {
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return None;
    }
    match operand.node() {
        KernelTermNode::Fold(fold) => {
            let atom = if let Some(atom) = context.retained_fold_atoms.get(&operand.id()) {
                atom.clone()
            } else {
                let atom = intern_integer_fold_key(retained_integer_fold_alpha_key(fold)?)?;
                context
                    .retained_fold_atoms
                    .insert(operand.id(), atom.clone());
                atom
            };
            add_atom_weight(terms, IntegerAffineAtom::Fold(atom), coefficient.clone())
        }
        KernelTermNode::Variable(variable) => add_atom_weight(
            terms,
            IntegerAffineAtom::Variable(*variable),
            coefficient.clone(),
        ),
        KernelTermNode::MachineObservation { .. } => {
            let observation = operand.exact_shared_integer_observation()?;
            collect_affine_observation(&observation, coefficient, terms, constant)
        }
        KernelTermNode::IntegerIf { .. } => add_atom_weight(
            terms,
            IntegerAffineAtom::Nonlinear(SharedIntegerTerm::from_root(operand.clone()).id()),
            coefficient.clone(),
        ),
        KernelTermNode::Call { .. } => add_atom_weight(
            terms,
            IntegerAffineAtom::Application(operand.integer_application()?.id()),
            coefficient.clone(),
        ),
        _ => None,
    }
}

fn collect_affine_observation(
    source: &crate::kernel::SharedMachineIntegerTerm,
    weight: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
) -> Option<()> {
    let atom = match source.value_reading() {
        Some(IntegerTerm::Machine(read)) => read.clone(),
        Some(IntegerTerm::Constant(value)) => {
            if !charge_integer_product(weight, value) {
                return None;
            }
            *constant += weight * value;
            return Some(());
        }
        _ => source.clone(),
    };
    add_atom_weight(terms, IntegerAffineAtom::Machine(atom), weight.clone())
}

/// A constant value for checking, with a shallow refusal for symbolic terms.
pub(crate) fn literal_integer_value(term: &crate::kernel::SharedIntegerTerm) -> Option<BigInt> {
    if !term.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(term.root(), &mut cache)?;
    cache.remove(&term.root().id())?
}

/// Literal arithmetic is builtin proof checking, not a lowering rewrite.
/// Cached shape flags refuse symbolic operands in constant time.
pub(crate) fn literal_integer_comparison_value(condition: &OldConditionTerm) -> Option<bool> {
    let (left, right) = match condition {
        OldConditionTerm::IntegerEqual(left, right)
        | OldConditionTerm::IntegerNotEqual(left, right)
        | OldConditionTerm::IntegerLessThan(left, right)
        | OldConditionTerm::IntegerLessEqual(left, right)
        | OldConditionTerm::IntegerGreaterThan(left, right)
        | OldConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    if !left.is_literal_arithmetic() || !right.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(left.root(), &mut cache)?;
    collect_integer_constants(right.root(), &mut cache)?;
    let left = cache.get(&left.root().id())?.as_ref()?;
    let right = cache.get(&right.root().id())?.as_ref()?;
    if crate::instrumentation::deadline_exceeded_with_work(
        left.bits() as usize + right.bits() as usize + 1,
    ) {
        return None;
    }
    Some(match condition {
        OldConditionTerm::IntegerEqual(..) => left == right,
        OldConditionTerm::IntegerNotEqual(..) => left != right,
        OldConditionTerm::IntegerLessThan(..) => left < right,
        OldConditionTerm::IntegerLessEqual(..) => left <= right,
        OldConditionTerm::IntegerGreaterThan(..) => left > right,
        OldConditionTerm::IntegerGreaterEqual(..) => left >= right,
        _ => unreachable!(),
    })
}

/// Evaluate only the explicit arithmetic DAG, once per node and under the
/// checker's numeric budget. None in the cache means a symbolic or undefined
/// value, not zero. Lowering and rewriting never call this evaluator.
fn collect_integer_constants(
    root: &KernelTerm,
    cache: &mut HashMap<u64, Option<BigInt>>,
) -> Option<()> {
    let mut stack = vec![(root, false)];
    while let Some((node, expanded)) = stack.pop() {
        if cache.contains_key(&node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if !node.is_literal_integer_arithmetic() {
            cache.insert(node.id(), None);
            continue;
        }
        if !expanded && let KernelTermNode::IntegerOperation { arguments, .. } = node.node() {
            stack.push((node, true));
            stack.extend(arguments.iter().rev().map(|child| (child, false)));
            continue;
        }
        use KernelIntegerOperator as Op;
        let value = match node.node() {
            KernelTermNode::IntegerLiteral(value) => {
                if crate::instrumentation::deadline_exceeded_with_work(value.bits() as usize + 1) {
                    return None;
                }
                Some(value.clone())
            }
            KernelTermNode::MachineObservation { .. } => node
                .exact_shared_integer_observation()?
                .literal_conversion_value()
                .map(|value| value.to_integer()),
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            } => {
                let value =
                    |index: usize| cache.get(&arguments[index].id()).and_then(Option::as_ref);
                let left = value(0);
                if *operator == Op::Negate {
                    if let Some(value) = left {
                        if crate::instrumentation::deadline_exceeded_with_work(
                            value.bits() as usize + 1,
                        ) {
                            return None;
                        }
                        Some(-value)
                    } else {
                        None
                    }
                } else if let (Some(left), Some(right)) = (left, value(1)) {
                    let left_work = left.bits() as usize + 1;
                    let right_work = right.bits() as usize + 1;
                    let work = if matches!(operator, Op::Add | Op::Subtract) {
                        left_work.saturating_add(right_work)
                    } else {
                        left_work.saturating_mul(right_work)
                    };
                    if crate::instrumentation::numeric_operation_work_exceeded(work) {
                        return None;
                    }
                    match operator {
                        Op::Add => Some(left + right),
                        Op::Subtract => Some(left - right),
                        Op::Multiply => Some(left * right),
                        Op::TruncatingQuotient if !right.is_zero() => Some(left / right),
                        Op::TruncatingRemainder if !right.is_zero() => Some(left % right),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            _ => None,
        };
        cache.insert(node.id(), value);
    }
    Some(())
}

fn add_atom_weight(
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    atom: IntegerAffineAtom,
    weight: BigInt,
) -> Option<()> {
    let existing = terms.get(&atom).map_or(0, |value| value.bits() as usize);
    if crate::instrumentation::deadline_exceeded_with_work(existing + weight.bits() as usize + 1) {
        return None;
    }
    let merged = terms.remove(&atom).unwrap_or_else(BigInt::zero) + weight;
    if !merged.is_zero() {
        terms.insert(atom, merged);
    }
    Some(())
}

fn add_weight(weights: &mut HashMap<u64, BigInt>, id: u64, weight: BigInt) -> bool {
    let existing = weights.get(&id).map_or(0, |value| value.bits() as usize);
    if crate::instrumentation::deadline_exceeded_with_work(existing + weight.bits() as usize + 1) {
        return false;
    }
    let merged = weights.remove(&id).unwrap_or_else(BigInt::zero) + weight;
    if !merged.is_zero() {
        weights.insert(id, merged);
    }
    true
}

#[cfg(test)]
mod tests {

    use crate::kernel::Variable;

    use super::*;

    #[test]
    fn integer_affine_graph_collection_stops_at_the_active_budget() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};
        let mut expression = IntegerTerm::var(Variable(30_000));
        for _ in 0..64 {
            expression = IntegerTerm::add(expression.clone(), expression.clone());
        }
        let goal = proposition(OldConditionTerm::integer_less_equal(
            expression,
            IntegerTerm::constant_i64(0),
        ));
        instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 16,
                smart: 16,
                control: 16,
            },
            || {
                let tactic = TacticEvent {
                    source_tactic_path: None,
                    claim: "integer budget".into(),
                    tactic_index: 0,
                    tactic_name: "normalize".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(integer_affine_claim(&goal).is_none());
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
            },
        );
    }

    fn variable(id: u64) -> IntegerTerm {
        IntegerTerm::Variable(Variable(id))
    }

    fn proposition(condition: OldConditionTerm) -> Proposition {
        Proposition::condition_is(condition, true)
    }

    fn claim(proposition: &Proposition) -> IntegerAffineClaim {
        integer_affine_claim(proposition).expect("integer proposition should be affine")
    }

    fn int32_fold(
        start: u32,
        end: u32,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::{IntegerRangeFoldIndex, SharedIntegerRangeEndpoint};
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(crate::kernel::OldMachineTerm::constant(
                    start,
                )),
                end: SharedIntegerRangeEndpoint::intern(crate::kernel::OldMachineTerm::constant(
                    end,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn integer_fold(
        start: i64,
        end: i64,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::IntegerRangeFoldIndex;
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(start).into(),
                end: IntegerTerm::constant_i64(end).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(
            IntegerTerm::var(Variable(accumulator)),
            IntegerTerm::var(Variable(item)),
        )
    }

    fn machine_item(item: u64) -> IntegerTerm {
        IntegerTerm::from_machine(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::OldMachineTerm::Variable(Variable(item)),
        )
        .expect("a symbolic Int32 item should be a machine observation")
    }

    fn machine_fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(IntegerTerm::var(Variable(accumulator)), machine_item(item))
    }

    #[test]
    fn fold_atom_identity_keeps_endpoints_body_and_carrier_distinct() {
        let baseline = int32_fold(0, 8, 300, 301, machine_fold_body(300, 301));
        let changed_end = int32_fold(0, 9, 300, 301, machine_fold_body(300, 301));
        let changed_body = int32_fold(
            0,
            8,
            300,
            301,
            IntegerTerm::subtract(IntegerTerm::var(Variable(300)), machine_item(301)),
        );
        let changed_carrier = integer_fold(0, 8, 300, 301, fold_body(300, 301));

        for other in [changed_end, changed_body, changed_carrier] {
            let goal = proposition(OldConditionTerm::IntegerEqual(
                baseline.clone().into(),
                other.into(),
            ));
            assert_eq!(claim(&goal).terms.len(), 2);
        }
    }

    #[test]
    fn fold_atom_identity_retains_the_exact_memory_state() {
        use crate::kernel::{
            Address, AddressOffset, IntegerRangeFoldIndex, MachineIntegerType, OldMachineTerm,
            ProgramValue, SharedIntegerRangeEndpoint, SharedMachineIntegerTerm, SymbolicMemory,
        };
        let pointer = Address {
            base: "affine-fold-retained_state".into(),
            offset: AddressOffset::Constant(0),
        };
        let before = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block("affine-fold-retained_state", 8),
        );
        let after = crate::kernel::intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let load_fold =
            |memory: &crate::kernel::SharedMemory, accumulator: u64, item: u64| -> IntegerTerm {
                IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Int32 {
                        start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
                        end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
                    },
                    IntegerTerm::constant_i64(0),
                    Variable(accumulator),
                    Variable(item),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        OldMachineTerm::read_named(
                            crate::kernel::ProgramPoint::at(memory),
                            Box::new(pointer.clone()),
                            crate::kernel::LoadKind::Int32,
                        ),
                    )),
                )
            };
        let before_fold = load_fold(&before, 700, 701);
        let renamed_before_fold = load_fold(&before, 800, 801);
        let after_fold = load_fold(&after, 800, 801);

        let renamed_goal = proposition(OldConditionTerm::IntegerEqual(
            before_fold.clone().into(),
            renamed_before_fold.into(),
        ));
        assert!(claim(&renamed_goal).terms.is_empty());

        let changed_state_goal = proposition(OldConditionTerm::IntegerEqual(
            before_fold.into(),
            after_fold.into(),
        ));
        assert_eq!(claim(&changed_state_goal).terms.len(), 2);
    }

    #[test]
    fn negated_integer_disequality_keeps_its_affine_equality() {
        let left = crate::kernel::SharedIntegerTerm::from(variable(995480));
        let right = crate::kernel::SharedIntegerTerm::from(variable(995481));
        let equality = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(left.clone(), right.clone()),
            true,
        );
        let unequal = OldConditionTerm::IntegerNotEqual(left, right);
        let expected = integer_affine_claim(&equality).unwrap();
        for premise in [
            Proposition::condition_is(unequal.clone(), false),
            Proposition::Not(Box::new(Proposition::condition_is(unequal.clone(), true))),
        ] {
            assert_eq!(integer_affine_claim(&premise), Some(expected.clone()));
        }
        assert!(integer_affine_claim(&Proposition::condition_is(unequal, true)).is_none());
    }

    #[test]
    fn deep_integer_terms_are_collected_iteratively() {
        let x = variable(8);
        let mut expression = x.clone();
        for _ in 0..2_048 {
            expression = IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(expression),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            );
        }
        let goal = proposition(OldConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(x),
        ));
        let result = claim(&goal);
        assert!(result.terms.is_empty());
        assert_eq!(result.constant, BigInt::from(2_048));
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        proposition(OldConditionTerm::integer_less_equal(left, right))
    }

    #[test]
    fn a_disequality_bounds_only_at_a_type_endpoint() {
        use crate::kernel::{MachineIntegerType, OldMachineTerm, SharedMachineIntegerTerm};
        let value =
            |ty| SharedMachineIntegerTerm::intern(ty, OldMachineTerm::Variable(Variable(97301)));
        let differs = |ty, constant: i64| {
            Proposition::condition_is(
                OldConditionTerm::integer_equal(
                    IntegerTerm::Machine(value(ty)),
                    IntegerTerm::constant_i64(constant),
                ),
                false,
            )
        };
        let observed = |ty| IntegerTerm::Machine(value(ty));
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::UInt64, 0)),
            Some(less_equal(
                IntegerTerm::constant_i64(1),
                observed(MachineIntegerType::UInt64)
            ))
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::Int32, 2_147_483_647)),
            Some(less_equal(
                observed(MachineIntegerType::Int32),
                IntegerTerm::constant_i64(2_147_483_646)
            ))
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::UInt64, 5)),
            None
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::Int32, 0)),
            None
        );
        let minimum = IntegerTerm::Subtract(
            IntegerTerm::constant_i64(-2147483647).into(),
            IntegerTerm::constant_i64(1).into(),
        );
        for reversed in [false, true] {
            let mut sides = [observed(MachineIntegerType::Int32), minimum.clone()];
            if reversed {
                sides.swap(0, 1);
            }
            let [left, right] = sides;
            let premise = Proposition::condition_is(
                OldConditionTerm::IntegerNotEqual(left.into(), right.into()),
                true,
            );
            assert_eq!(
                excluded_type_bound(&premise),
                Some(less_equal(
                    IntegerTerm::constant_i64(-2147483647),
                    observed(MachineIntegerType::Int32),
                ))
            );
        }
        // An equality is no disequality.
        let equal = Proposition::condition_is(
            OldConditionTerm::integer_equal(
                observed(MachineIntegerType::UInt64),
                IntegerTerm::constant_i64(0),
            ),
            true,
        );
        assert_eq!(excluded_type_bound(&equal), None);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/integer_arithmetic/tests.rs");
    }
}
