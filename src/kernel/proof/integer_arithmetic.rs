//! Affine Integer claims and internal arithmetic search plans.
//! Plans are expanded into ordinary proof steps; they are not proof objects.
pub(crate) use super::integer_affine_atoms::IntegerAffineAtom;
use super::integer_affine_atoms::{IntegerFoldAtomRecord, intern_integer_fold_atom};

use crate::kernel::{
    ConditionTerm, IntegerTerm, KernelTerm, KernelTermNode, MachineTerm, ProgramPoint, Proposition,
    SharedMachineIntegerTerm,
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
    let readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            proposition,
        );
    let reading = readings.first().unwrap_or(proposition);
    let (left, right) = match reading {
        condition_source @ Proposition::ConditionIs(_, _)
            if let Some(
                (ConditionTerm::IntegerEqual(left, right), false)
                | (ConditionTerm::IntegerNotEqual(left, right), true),
            ) = condition_source.condition_native() =>
        {
            (left, right)
        }
        Proposition::Not(body) => match body.as_ref() {
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((ConditionTerm::IntegerEqual(left, right), _)) =
                    condition_source_0.condition_native() =>
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
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    let readings = if matches!(
        condition.native_compat(),
        crate::kernel::integer_comparison_condition!(_, _)
    ) {
        vec![Proposition::condition_is(condition.clone(), value)]
    } else {
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(condition.clone(), value),
        )
    };
    let mut context = IntegerAffineCollectionContext::default();
    let mut differences = Vec::with_capacity(readings.len());
    for reading in &readings {
        let (left, right) = match reading {
            condition_source @ Proposition::ConditionIs(_, _)
                if let Some(
                    (ConditionTerm::IntegerNotEqual(left, right), true)
                    | (ConditionTerm::IntegerEqual(left, right), false),
                ) = condition_source.condition_native() =>
            {
                (left, right)
            }
            _ => continue,
        };
        let mut terms = BTreeMap::new();
        let mut constant = BigInt::zero();
        if collect_integer_affine_terms(
            left,
            &BigInt::one(),
            &mut terms,
            &mut constant,
            &mut context,
        )
        .is_none()
            || collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                &mut context,
            )
            .is_none()
            || terms.is_empty()
        {
            continue;
        }
        let difference = IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms,
            constant,
        };
        if !differences.contains(&difference) {
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
        ConditionTerm::integer_less_equal(IntegerTerm::constant(min + BigInt::one()), observed)
    } else if constant == max {
        ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(max - BigInt::one()))
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
    // A native comparison observes the machine values its Integer reading
    // does, as `integer_affine_claim` reads it.
    if !matches!(
        condition.native_compat(),
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
    let (left, right) = match condition.native_compat() {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right) => (left, right),
        _ => return Vec::new(),
    };
    let mut seen = HashSet::new();
    let mut values = Vec::new();
    let mut stack = vec![right.clone(), left.clone()];
    while let Some(node) = stack.pop() {
        if !seen.insert(node.id()) {
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Machine(value) => values.push(value.clone()),
            IntegerTerm::Negate(child) => stack.push(child.clone()),
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push(right.clone());
                stack.push(left.clone());
            }
            IntegerTerm::Multiply(left, right) => {
                if left.as_const().is_some() {
                    stack.push(right.clone());
                } else if right.as_const().is_some() {
                    stack.push(left.clone());
                }
            }
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
    fold_atoms: HashMap<crate::kernel::SharedIntegerTerm, Arc<IntegerFoldAtomRecord>>,
}

#[cfg(test)]
thread_local! {
    static INTEGER_FOLD_ALPHA_CONSTRUCTIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

fn fold_atom_for_claim(
    context: &mut IntegerAffineCollectionContext,
    term: &crate::kernel::SharedIntegerTerm,
) -> Option<Arc<IntegerFoldAtomRecord>> {
    if let Some(atom) = context.fold_atoms.get(term) {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        return Some(atom.clone());
    }
    #[cfg(test)]
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(|count| count.set(count.get() + 1));
    let atom = intern_integer_fold_atom(term)?;
    context.fold_atoms.insert(term.clone(), atom.clone());
    Some(atom)
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
            if !matches!(
                condition.native_compat(),
                crate::kernel::integer_comparison_condition!(_, _)
            ) =>
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
            Proposition::ConditionIs(condition, value) => {
                !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    &Proposition::condition_is(condition.clone(), !value),
                )
                .is_empty()
            }
            _ => false,
        },
        _ => !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            proposition,
        )
        .is_empty(),
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
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return None,
        },
        _ => return None,
    };
    // A native comparison of machine values holds exactly when the Integer
    // comparison of their exact observations does, so it is that Integer
    // claim. One constant-size reading; nothing else is consulted.
    if !matches!(
        condition.native_compat(),
        crate::kernel::integer_comparison_condition!(_, _) | ConditionTerm::Constant(_)
    ) && let Some(reading) =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(condition.clone(), value),
        )
        .into_iter()
        .next()
    {
        return integer_affine_claim_with_context(&reading, context);
    }
    if let ConditionTerm::Constant(actual) = condition.native_compat() {
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
    let (left, right, relation, strict) = match condition.native_compat() {
        ConditionTerm::IntegerLessThan(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerLessEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterThan(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::Equal, false)
        }
        ConditionTerm::IntegerLessThan(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            // Disequality is outside this fragment, except for constants.
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) if value => {
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            // A false disequality is the same affine equality as a true
            // IntegerEqual, including under a negated branch premise.
            (left, right, IntegerAffineRelation::Equal, false)
        }
        _ => return None,
    };
    let mut terms = BTreeMap::new();
    let mut constant = BigInt::zero();
    collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
    collect_integer_affine_terms(right, &BigInt::from(-1), &mut terms, &mut constant, context)?;
    if strict {
        if crate::instrumentation::deadline_exceeded_with_work(constant.bits() as usize + 1) {
            return None;
        }
        constant += BigInt::one();
    }
    Some(IntegerAffineClaim {
        relation,
        terms,
        constant,
    })
}

/// A constant value for checking, with a shallow refusal for symbolic terms.
pub(crate) fn literal_integer_value(term: &crate::kernel::SharedIntegerTerm) -> Option<BigInt> {
    if !term.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(term, &mut cache)?;
    cache.remove(&term.id())?
}

/// Literal arithmetic is builtin proof checking, not a lowering rewrite.
/// Cached shape flags refuse symbolic operands in constant time.
pub(crate) fn literal_integer_comparison_value(condition: &ConditionTerm) -> Option<bool> {
    let (left, right) = match condition {
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    if !left.is_literal_arithmetic() || !right.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(left, &mut cache)?;
    collect_integer_constants(right, &mut cache)?;
    let left = cache.get(&left.id())?.as_ref()?;
    let right = cache.get(&right.id())?.as_ref()?;
    if crate::instrumentation::deadline_exceeded_with_work(
        left.bits() as usize + right.bits() as usize + 1,
    ) {
        return None;
    }
    Some(match condition {
        ConditionTerm::IntegerEqual(..) => left == right,
        ConditionTerm::IntegerNotEqual(..) => left != right,
        ConditionTerm::IntegerLessThan(..) => left < right,
        ConditionTerm::IntegerLessEqual(..) => left <= right,
        ConditionTerm::IntegerGreaterThan(..) => left > right,
        ConditionTerm::IntegerGreaterEqual(..) => left >= right,
        _ => unreachable!(),
    })
}

/// Evaluate only the explicit arithmetic DAG, once per node and under the
/// checker's numeric budget. None in the cache means a symbolic or undefined
/// value, not zero. Lowering and rewriting never call this evaluator.
fn collect_integer_constants(
    root: &crate::kernel::SharedIntegerTerm,
    cache: &mut HashMap<u64, Option<BigInt>>,
) -> Option<()> {
    let mut stack = vec![(root.clone(), false)];
    while let Some((node, expanded)) = stack.pop() {
        if cache.contains_key(&node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if !node.is_literal_arithmetic() {
            cache.insert(node.id(), None);
            continue;
        }
        if !expanded {
            stack.push((node.clone(), true));
            match node.as_ref() {
                IntegerTerm::Negate(child) => stack.push((child.clone(), false)),
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right)
                | IntegerTerm::TruncatingQuotient(left, right)
                | IntegerTerm::TruncatingRemainder(left, right) => {
                    stack.push((right.clone(), false));
                    stack.push((left.clone(), false));
                }
                _ => {}
            }
            continue;
        }
        let value = match node.as_ref() {
            IntegerTerm::Constant(value) => {
                if crate::instrumentation::deadline_exceeded_with_work(value.bits() as usize + 1) {
                    return None;
                }
                Some(value.clone())
            }
            IntegerTerm::Machine(value) => value
                .literal_conversion_value()
                .map(|value| value.to_integer()),
            IntegerTerm::Negate(child) => match cache.get(&child.id()).and_then(Option::as_ref) {
                Some(value) => {
                    if crate::instrumentation::deadline_exceeded_with_work(
                        value.bits() as usize + 1,
                    ) {
                        return None;
                    }
                    Some(-value)
                }
                None => None,
            },
            IntegerTerm::Add(left, right)
            | IntegerTerm::Subtract(left, right)
            | IntegerTerm::Multiply(left, right)
            | IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => {
                match (
                    cache.get(&left.id()).and_then(Option::as_ref),
                    cache.get(&right.id()).and_then(Option::as_ref),
                ) {
                    (Some(left), Some(right)) => {
                        let work = if matches!(
                            node.as_ref(),
                            IntegerTerm::Add(..) | IntegerTerm::Subtract(..)
                        ) {
                            (left.bits() as usize + 1).saturating_add(right.bits() as usize + 1)
                        } else {
                            (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1)
                        };
                        if crate::instrumentation::numeric_operation_work_exceeded(work) {
                            return None;
                        }
                        match node.as_ref() {
                            IntegerTerm::Add(..) => Some(left + right),
                            IntegerTerm::Subtract(..) => Some(left - right),
                            IntegerTerm::Multiply(..) => Some(left * right),
                            IntegerTerm::TruncatingQuotient(..) if !right.is_zero() => {
                                Some(left / right)
                            }
                            IntegerTerm::TruncatingRemainder(..) if !right.is_zero() => {
                                Some(left % right)
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        cache.insert(node.id(), value);
    }
    Some(())
}

/// Integer observations use the same empty-entry compatibility as scalar
/// congruence. The arithmetic atom may be shared with a legacy fold read;
/// the checked proposition still retains the point on its operand.
fn affine_machine_atom(value: &SharedMachineIntegerTerm) -> IntegerAffineAtom {
    let reading = if let Some(root) = value.shared_operand() {
        match root.node() {
            KernelTermNode::MemoryLoad {
                point,
                address,
                kind,
            } if point.is_entry_read() => {
                let entry = ProgramPoint::at(point.shared_memory());
                let read =
                    KernelTerm::shared_scalar_read_descriptor(value.ty(), &entry, address, *kind);
                SharedMachineIntegerTerm::from_shared(value.ty(), read)
            }
            _ => None,
        }
    } else if let Some(MachineTerm::MemoryLoad(point, address, kind)) =
        value.retained_written_operand()
        && point.is_entry_read()
    {
        let read = MachineTerm::memory_read(
            point.shared_memory().clone(),
            address.as_ref().clone(),
            *kind,
        );
        Some(SharedMachineIntegerTerm::intern(value.ty(), read))
    } else {
        None
    };
    IntegerAffineAtom::Machine(reading.unwrap_or_else(|| value.clone()))
}

fn collect_integer_affine_terms(
    term: &crate::kernel::SharedIntegerTerm,
    coefficient: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
    context: &mut IntegerAffineCollectionContext,
) -> Option<()> {
    collect_integer_constants(term, &mut context.constants)?;
    // First collect the reachable DAG in postorder.  The interner gives each
    // node a stable identity, so this schedules a shared node exactly once.
    let mut scheduled = HashSet::new();
    let mut stack = vec![(term.clone(), false)];
    let mut order = Vec::new();
    while let Some((node, expanded)) = stack.pop() {
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
        stack.push((node.clone(), true));
        collect_integer_constants(&node, &mut context.constants)?;
        if context
            .constants
            .get(&node.id())
            .and_then(Option::as_ref)
            .is_some()
        {
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Negate(child) => stack.push((child.clone(), false)),
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push((right.clone(), false));
                stack.push((left.clone(), false));
            }
            IntegerTerm::Multiply(left, right) => {
                // A symbolic product is one opaque atom. Cached shape flags
                // let constant coefficients be checked without walking a
                // symbolic operand's DAG.
                if left.is_literal_arithmetic() {
                    collect_integer_constants(left, &mut context.constants)?;
                }
                if right.is_literal_arithmetic() {
                    collect_integer_constants(right, &mut context.constants)?;
                }
                if context.constants.get(&left.id()).and_then(Option::as_ref).is_some() {
                    stack.push((right.clone(), false));
                } else if context.constants.get(&right.id()).and_then(Option::as_ref).is_some() {
                    stack.push((left.clone(), false));
                }
            }
            IntegerTerm::TruncatingQuotient(_, _) | IntegerTerm::TruncatingRemainder(_, _) => {}
            IntegerTerm::Constant(_)
            | IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. }
            // An unresolved conditional is an opaque atom, as a machine
            // conditional's observation is.
            | IntegerTerm::If { .. } => {}
            // A RangeFold is a checked opaque atom.  Its body and endpoints
            // are represented by the kernel-issued alpha key below; affine
            // normalization must never enumerate or lower the range here.
            IntegerTerm::RangeFold { .. } => {}
        }
    }

    // Propagate the coefficient from each root toward the leaves.  This
    // keeps only one scalar per reachable node; no internal node constructs
    // or clones a complete affine map.
    let mut weights = HashMap::new();
    weights.insert(term.id(), coefficient.clone());
    for node in order.into_iter().rev() {
        let Some(weight) = weights.remove(&node.id()) else {
            continue;
        };
        if crate::instrumentation::deadline_exceeded_with_work(weight.bits() as usize + 1) {
            return None;
        }
        if weight.is_zero() {
            continue;
        }
        if let Some(value) = context.constants.get(&node.id()).and_then(Option::as_ref) {
            if !charge_integer_product(&weight, value)
                || crate::instrumentation::deadline_exceeded_with_work(
                    constant.bits() as usize + weight.bits() as usize + value.bits() as usize + 1,
                )
            {
                return None;
            }
            *constant += &weight * value;
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Constant(_) => unreachable!("constants were evaluated above"),
            IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. }
            | IntegerTerm::If { .. }
            | IntegerTerm::TruncatingQuotient(_, _)
            | IntegerTerm::TruncatingRemainder(_, _) => {
                let atom = match node.as_ref() {
                    IntegerTerm::Variable(variable) => IntegerAffineAtom::Variable(*variable),
                    // An observation is the atom of its value reading
                    // (rule W): `to_integer(widen(v))` and `to_integer(v)`
                    // are one atom. One cached lookup per observation.
                    IntegerTerm::Machine(source) => match source.value_reading() {
                        Some(IntegerTerm::Machine(read)) => affine_machine_atom(read),
                        Some(IntegerTerm::Constant(value)) => {
                            if !charge_integer_product(&weight, value) {
                                return None;
                            }
                            *constant += &weight * value;
                            continue;
                        }
                        _ => affine_machine_atom(source),
                    },
                    IntegerTerm::AlgebraicMatch { .. } => return None,
                    // An unresolved conditional is an opaque atom by its
                    // shared identity, as a quotient is.
                    IntegerTerm::If { .. } => IntegerAffineAtom::Nonlinear(node.id()),
                    // A quotient or remainder is keyed by its reading through
                    // its observations' value relations (rule W), so its two
                    // spellings are one atom.
                    IntegerTerm::TruncatingQuotient(_, _)
                    | IntegerTerm::TruncatingRemainder(_, _) => {
                        IntegerAffineAtom::Nonlinear(node.read_through().id())
                    }
                    IntegerTerm::PureFunctionApplication(application) => {
                        IntegerAffineAtom::Application(application.id())
                    }
                    _ => unreachable!(),
                };
                add_atom_weight(terms, atom, weight)?;
            }
            IntegerTerm::RangeFold { .. } => {
                let atom = IntegerAffineAtom::Fold(fold_atom_for_claim(context, &node)?);
                add_atom_weight(terms, atom, weight)?;
            }
            IntegerTerm::Negate(child) => {
                if !add_weight(&mut weights, child.id(), -weight) {
                    return None;
                }
            }
            IntegerTerm::Add(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), weight)
                {
                    return None;
                }
            }
            IntegerTerm::Subtract(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), -weight)
                {
                    return None;
                }
            }
            IntegerTerm::Multiply(left, right) => {
                let (child, factor) = if let Some(value) =
                    context.constants.get(&left.id()).and_then(Option::as_ref)
                {
                    (right, value)
                } else if let Some(value) =
                    context.constants.get(&right.id()).and_then(Option::as_ref)
                {
                    (left, value)
                } else {
                    // A symbolic product is keyed by its reading (rule W).
                    add_atom_weight(
                        terms,
                        IntegerAffineAtom::Nonlinear(node.read_through().id()),
                        weight,
                    )?;
                    continue;
                };
                if !charge_integer_product(&weight, factor) {
                    return None;
                }
                if !add_weight(&mut weights, child.id(), weight * factor) {
                    return None;
                }
            }
        }
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
        let goal = proposition(ConditionTerm::integer_less_equal(
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

    fn proposition(condition: ConditionTerm) -> Proposition {
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
                start: SharedIntegerRangeEndpoint::intern(crate::kernel::MachineTerm::constant(
                    start,
                )),
                end: SharedIntegerRangeEndpoint::intern(crate::kernel::MachineTerm::constant(end)),
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
            crate::kernel::MachineTerm::Variable(Variable(item)),
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
            let goal = proposition(ConditionTerm::IntegerEqual(
                baseline.clone().into(),
                other.into(),
            ));
            assert_eq!(claim(&goal).terms.len(), 2);
        }
    }

    #[test]
    fn fold_atom_identity_retains_the_exact_memory_state() {
        use crate::kernel::{
            Address, AddressOffset, IntegerRangeFoldIndex, MachineIntegerType, MachineTerm,
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
            ProgramValue::Int32(MachineTerm::constant(7)),
        ));
        let load_fold =
            |memory: &crate::kernel::SharedMemory, accumulator: u64, item: u64| -> IntegerTerm {
                IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Int32 {
                        start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                        end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(2)),
                    },
                    IntegerTerm::constant_i64(0),
                    Variable(accumulator),
                    Variable(item),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        MachineTerm::MemoryLoad(
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

        let renamed_goal = proposition(ConditionTerm::IntegerEqual(
            before_fold.clone().into(),
            renamed_before_fold.into(),
        ));
        assert!(claim(&renamed_goal).terms.is_empty());

        let changed_state_goal = proposition(ConditionTerm::IntegerEqual(
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
            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
            true,
        );
        let unequal = ConditionTerm::IntegerNotEqual(left, right);
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
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(x),
        ));
        let result = claim(&goal);
        assert!(result.terms.is_empty());
        assert_eq!(result.constant, BigInt::from(2_048));
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        proposition(ConditionTerm::integer_less_equal(left, right))
    }

    #[test]
    fn a_disequality_bounds_only_at_a_type_endpoint() {
        use crate::kernel::{MachineIntegerType, MachineTerm, SharedMachineIntegerTerm};
        let value =
            |ty| SharedMachineIntegerTerm::intern(ty, MachineTerm::Variable(Variable(97301)));
        let differs = |ty, constant: i64| {
            Proposition::condition_is(
                ConditionTerm::integer_equal(
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
                ConditionTerm::IntegerNotEqual(left.into(), right.into()),
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
            ConditionTerm::integer_equal(
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
