//! Goal-local computation for a simple proof leaf.
//!
//! The `computes_leaf` entry point receives no fact context. Reads, calls,
//! folds, and symbolic matches remain opaque operands in that entry point;
//! it has no memory resolution, unfolding, or atomic-prover fallback. Legacy
//! normalization shares arithmetic below but supplies its own atom key.

use crate::kernel::machine_integer::bounds::positive_literal_remainder_divisor;
use crate::kernel::*;
use crate::kernel::{
    constant_i64, constant_u32, constant_u64, int32_constant, int64_constant, uint64_constant,
};

/// Whether this leaf is true by direct computation alone. A negated
/// connective can be checked here as a leaf of the caller's structural walk.
/// Implications and quantifiers still require their ordinary proof steps.
pub(crate) fn computes_leaf(goal: &Proposition) -> bool {
    let negated = matches!(goal, Proposition::Not(_));
    let mut goal = goal;
    let mut expected = true;
    while let Proposition::Not(body) = goal {
        crate::instrumentation::record_deterministic_work(1);
        expected = !expected;
        goal = body;
    }
    if negated && matches!(goal, Proposition::And(..) | Proposition::Or(..)) {
        return computes_connective(goal, expected);
    }
    computes_atom(goal, expected)
}

/// Check the requested polarity of the explicit connective tree. Each
/// connective either needs both sides or can stop at the first decisive
/// side. An atom with unknown truth supplies neither polarity.
fn computes_connective(root: &Proposition, expected: bool) -> bool {
    enum Task<'a> {
        Visit(&'a Proposition, bool),
        VisitRightIf(&'a Proposition, bool, bool),
    }
    let mut tasks = vec![Task::Visit(root, expected)];
    let mut proved = false;
    while let Some(task) = tasks.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            Task::Visit(Proposition::Not(body), expected) => {
                tasks.push(Task::Visit(body, !expected));
            }
            Task::Visit(
                side @ (Proposition::And(left, right) | Proposition::Or(left, right)),
                expected,
            ) => {
                let needs_both = matches!(side, Proposition::And(..)) == expected;
                tasks.push(Task::VisitRightIf(right, expected, needs_both));
                tasks.push(Task::Visit(left, expected));
            }
            Task::Visit(atom, expected) => proved = computes_atom(atom, expected),
            Task::VisitRightIf(right, expected, needs_both) => {
                if proved == needs_both {
                    tasks.push(Task::Visit(right, expected));
                }
            }
        }
    }
    proved
}

fn computes_atom(goal: &Proposition, expected: bool) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if let Some(holds) =
        crate::kernel::spec::checks_int32_sequence_comparison(goal, expected, |condition, value| {
            condition_value(condition) == Some(value)
        })
    {
        return holds;
    }
    let value = match goal {
        Proposition::ConditionIs(condition, truth) => {
            condition_value(condition.native_compat()).map(|value| value == *truth)
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            if let (Some(left), Some(right)) = (left.root(), right.root())
                && left == right
            {
                Some(true)
            } else {
                algebraic_equality(left.native_compat(), right.native_compat())
            }
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => {
            integer_affine_comparison(&ConditionTerm::IntegerEqual(
                left.native_compat().clone().into(),
                right.native_compat().clone().into(),
            ))
        }
        // A concrete span is a single bounds lookup in the goal's memory.
        // A loaded or symbolic base needs its own proof of the address.
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } => bytes
            .as_const()
            .is_some_and(|size| memory.access_in_bounds(base, size))
            .then_some(true),
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
            ..
        } => memory
            .indexed_read_is_defined(pointer, *value_type)
            .then_some(true),
        Proposition::ResourceSeparate { left, right }
            if let (Resource::Memory(left), Resource::Memory(right)) =
                (left.as_ref(), right.as_ref()) =>
        {
            automatic_object_ranges_separate(left, right).then_some(true)
        }
        Proposition::Equal(left, right)
            if matches!(
                left,
                Term::Condition(_)
                    | Term::Bitvector32(_)
                    | Term::PointerOffset(_)
                    | Term::ProgramValue(_)
                    | Term::Sequence(_)
            ) && left == right =>
        {
            Some(true)
        }
        _ => None,
    };
    value == Some(expected)
        || (expected && super::super::arithmetic_special::intrinsic_pointer_alignment(goal))
}

/// These exact block kinds use the structural separation rule without
/// asking about pointer loads or resolving aliases. Range formation has
/// its own checked obligations before the separation goal is opened.
fn automatic_object_ranges_separate(left: &MemoryRange, right: &MemoryRange) -> bool {
    use AddressBase::{AutomaticLocal, ExternalArgument, ExternalObject};
    let left = left.base();
    let right = right.base();
    matches!(
        (&left.base, &right.base),
        (
            AutomaticLocal { .. },
            AutomaticLocal { .. } | ExternalArgument | ExternalObject(_),
        ) | (ExternalArgument | ExternalObject(_), AutomaticLocal { .. })
    ) && left.blocks_proven_distinct(right)
}

/// Constant operands and reflexivity only: a bounded structural check, with
/// no facts, affine normalization, memory walk, or equality-graph query.
/// Unit propagation uses this intrinsic truth beside exact admitted literals.
pub(crate) fn trivial_condition_value(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => {
            // Equality compares word bits. Substitution can retain an unsigned
            // constant in a signed equality (or conversely) at the same width.
            if *relation == CompareRelation::Equal
                && let (
                    MachineTerm::Constant { format: a, bits: x },
                    MachineTerm::Constant { format: b, bits: y },
                ) = (left.as_ref(), right.as_ref())
                && a.format().width() == format.format().width()
                && b.format().width() == format.format().width()
            {
                return Some(x == y);
            }
            let order = if left == right {
                std::cmp::Ordering::Equal
            } else {
                format
                    .constant_from_term(left)?
                    .to_integer()
                    .cmp(&format.constant_from_term(right)?.to_integer())
            };
            Some(match relation {
                CompareRelation::Equal => order.is_eq(),
                CompareRelation::LessThan => order.is_lt(),
                CompareRelation::LessEqual => !order.is_gt(),
                CompareRelation::GreaterThan => order.is_gt(),
                CompareRelation::GreaterEqual => !order.is_lt(),
            })
        }
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => {
            let order = if left == right {
                std::cmp::Ordering::Equal
            } else {
                let (IntegerTerm::Constant(a), IntegerTerm::Constant(b)) =
                    (left.as_ref(), right.as_ref())
                else {
                    return None;
                };
                crate::instrumentation::record_deterministic_work(
                    a.bits() as usize + b.bits() as usize + 1,
                );
                a.cmp(b)
            };
            Some(match condition {
                ConditionTerm::IntegerEqual(..) => order.is_eq(),
                ConditionTerm::IntegerNotEqual(..) => !order.is_eq(),
                ConditionTerm::IntegerLessThan(..) => order.is_lt(),
                ConditionTerm::IntegerLessEqual(..) => !order.is_gt(),
                ConditionTerm::IntegerGreaterThan(..) => order.is_gt(),
                ConditionTerm::IntegerGreaterEqual(..) => !order.is_lt(),
                _ => unreachable!(),
            })
        }
        _ => None,
    }
}

fn condition_value(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::IntegerEqual(..)
        | ConditionTerm::IntegerNotEqual(..)
        | ConditionTerm::IntegerLessThan(..)
        | ConditionTerm::IntegerLessEqual(..)
        | ConditionTerm::IntegerGreaterThan(..)
        | ConditionTerm::IntegerGreaterEqual(..) => {
            let (left, right) = match condition {
                ConditionTerm::IntegerEqual(left, right)
                | ConditionTerm::IntegerNotEqual(left, right)
                | ConditionTerm::IntegerLessThan(left, right)
                | ConditionTerm::IntegerLessEqual(left, right)
                | ConditionTerm::IntegerGreaterThan(left, right)
                | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
                _ => unreachable!(),
            };
            if left == right {
                return Some(matches!(
                    condition,
                    ConditionTerm::IntegerEqual(..)
                        | ConditionTerm::IntegerLessEqual(..)
                        | ConditionTerm::IntegerGreaterEqual(..)
                ));
            }
            super::super::integer_arithmetic::literal_integer_comparison_value(condition)
                .or_else(|| integer_affine_comparison(condition))
                .or_else(|| integer_operation_bound_comparison(condition))
        }
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => {
            if let Some(answer) = known_int32_match_comparison_value(condition) {
                return Some(answer);
            }
            if left == right {
                return Some(matches!(
                    relation,
                    CompareRelation::Equal
                        | CompareRelation::LessEqual
                        | CompareRelation::GreaterEqual
                ));
            }
            if (matches!(left.as_ref(), MachineTerm::IntegerToMachine { .. })
                || matches!(right.as_ref(), MachineTerm::IntegerToMachine { .. }))
                && let Some(value) =
                    crate::kernel::machine_integer::comparison::literal_native_comparison_value(
                        condition,
                    )
            {
                return Some(value);
            }
            if let (Some(left), Some(right)) = (
                format.constant_from_term(left),
                format.constant_from_term(right),
            ) {
                let (left, right) = (left.to_integer(), right.to_integer());
                return Some(match relation {
                    CompareRelation::Equal => left == right,
                    CompareRelation::LessThan => left < right,
                    CompareRelation::LessEqual => left <= right,
                    CompareRelation::GreaterThan => left > right,
                    CompareRelation::GreaterEqual => left >= right,
                });
            }
            let strict_upper_bound = match relation {
                CompareRelation::LessThan => Some((left, right)),
                CompareRelation::GreaterThan => Some((right, left)),
                _ => None,
            };
            if let Some((value, bound)) = strict_upper_bound
                && let Some(divisor) =
                    positive_literal_remainder_divisor(*format, MachineOperandView::Legacy(value))
                && format
                    .constant_from_term(bound)
                    .is_some_and(|bound| bound.to_integer() == divisor)
            {
                return Some(true);
            }
            if matches!(
                relation,
                CompareRelation::LessEqual | CompareRelation::GreaterEqual
            ) {
                // Native comparisons retain their format rather than changing
                // lowering to an Integer condition. Its exact extrema are local.
                let (min, max) = format.format().bounds();
                let a = format.constant_from_term(left).map(|n| n.to_integer());
                let b = format.constant_from_term(right).map(|n| n.to_integer());
                if matches!(relation, CompareRelation::LessEqual)
                    && (a.as_ref() == Some(&min) || b.as_ref() == Some(&max))
                    || matches!(relation, CompareRelation::GreaterEqual)
                        && (a.as_ref() == Some(&max) || b.as_ref() == Some(&min))
                {
                    return Some(true);
                }
                // A promoted narrow operand retains its smaller intrinsic range.
                for reading in
                    crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                        &Proposition::condition_is(condition.clone(), true),
                    )
                {
                    if let Proposition::ConditionIs(reading, true) = reading
                        && integer_operation_bound_comparison(reading.native_compat()) == Some(true)
                    {
                        return Some(true);
                    }
                }
            }
            // Raw goal atoms retain their exact typed state identities.
            // In particular, this key must never canonicalize a memory read.
            machine_affine_equality(condition, Clone::clone)
        }
        ConditionTerm::AddressEqual(left, right) if left == right => Some(true),
        ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
        ConditionTerm::AddressOffsetEqual(left, right) if left == right => Some(true),
        ConditionTerm::AlgebraicEqual(left, right) => algebraic_equality(left, right),
        ConditionTerm::BoolEqual(left, right) if left == right => Some(true),
        // Float comparisons deliberately have no reflexivity rule: NaNs
        // compare unequal even when both operands have the same identity.
        _ => None,
    }
}

pub(super) fn known_int32_match_comparison_value(condition: &ConditionTerm) -> Option<bool> {
    use crate::kernel::proof::term_rewrite::TermRewrite;
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let reduced_left = TermRewrite::reduce_known_int32_match(left);
    let reduced_right = TermRewrite::reduce_known_int32_match(right);
    if reduced_left.is_none() && reduced_right.is_none() {
        return None;
    }
    let left = reduced_left.as_ref().unwrap_or(left);
    let right = reduced_right.as_ref().unwrap_or(right);
    let ordering = if left == right {
        std::cmp::Ordering::Equal
    } else {
        (left.as_const()? as i32).cmp(&(right.as_const()? as i32))
    };
    Some(match relation {
        CompareRelation::Equal => ordering.is_eq(),
        CompareRelation::LessThan => ordering.is_lt(),
        CompareRelation::LessEqual => !ordering.is_gt(),
        CompareRelation::GreaterThan => ordering.is_gt(),
        CompareRelation::GreaterEqual => !ordering.is_lt(),
    })
}

fn algebraic_equality(left: &AlgebraicTerm, right: &AlgebraicTerm) -> Option<bool> {
    if left.algebraic_type != right.algebraic_type {
        return None;
    }
    if left == right {
        return Some(true);
    }
    match (&left.node, &right.node) {
        (
            AlgebraicTermNode::Constructor { variant: left, .. },
            AlgebraicTermNode::Constructor { variant: right, .. },
        ) if left != right => Some(false),
        (
            AlgebraicTermNode::Constructor { fields: left, .. },
            AlgebraicTermNode::Constructor { fields: right, .. },
        ) if left.len() == right.len() => left
            .iter()
            .zip(right)
            .any(|(left, right)| {
                crate::instrumentation::record_deterministic_work(1);
                match (left, right) {
                    (AlgebraicValue::Program(left), AlgebraicValue::Program(right)) => {
                        crate::kernel::reasoning::path_facts::program_values_definitely_distinct(
                            left, right,
                        )
                    }
                    _ => false,
                }
            })
            .then_some(false),
        _ => None,
    }
}

/// Decide a C machine equality whose sides are sums and differences, at
/// either width, by their affine forms over `Z/2^width`. Each side flattens
/// into signed atoms and a constant; the two are equal exactly when every
/// atom cancels and the constants agree, and differ in every model when
/// every atom cancels and the constants do not. The identities used --
/// reordering, regrouping, and cancellation -- hold for exact and for
/// wrapping arithmetic alike, so a C signed overflow, which is a separate
/// definedness obligation, does not affect the verdict. Atoms are keyed by
/// the caller-selected key; anything else, including a product, is an atom.
/// The walk visits each node of the goal once.
pub(super) fn machine_affine_equality(
    condition: &ConditionTerm,
    atom_key: fn(&MachineTerm) -> MachineTerm,
) -> Option<bool> {
    let (left, right, wide) = match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => (left, right, false),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => (left, right, true),
        _ => return None,
    };
    let mask = if wide { u64::MAX } else { u64::from(u32::MAX) };
    let mut atoms = std::collections::BTreeMap::new();
    let mut constant = 0u64;
    collect_machine_affine_atoms(left, 1, wide, &mut atoms, &mut constant, atom_key);
    collect_machine_affine_atoms(right, u64::MAX, wide, &mut atoms, &mut constant, atom_key);
    atoms
        .values()
        .all(|coefficient| coefficient & mask == 0)
        .then_some(constant & mask == 0)
}

fn collect_machine_affine_atoms(
    term: &MachineTerm,
    coefficient: u64,
    wide: bool,
    atoms: &mut std::collections::BTreeMap<MachineTerm, u64>,
    constant: &mut u64,
    atom_key: fn(&MachineTerm) -> MachineTerm,
) {
    crate::instrumentation::record_deterministic_work(1);
    match (term, wide) {
        (binary_term!(Int32, Add, left, right), false)
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left,
                right,
            },
            true,
        )
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left,
                right,
            },
            true,
        ) => {
            collect_machine_affine_atoms(left, coefficient, wide, atoms, constant, atom_key);
            collect_machine_affine_atoms(right, coefficient, wide, atoms, constant, atom_key);
        }
        (binary_term!(Int32, Subtract, left, right), false)
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Subtract,
                left,
                right,
            },
            true,
        )
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Subtract,
                left,
                right,
            },
            true,
        ) => {
            collect_machine_affine_atoms(left, coefficient, wide, atoms, constant, atom_key);
            collect_machine_affine_atoms(
                right,
                coefficient.wrapping_neg(),
                wide,
                atoms,
                constant,
                atom_key,
            );
        }
        (int32_constant!(value), false) => {
            *constant =
                constant.wrapping_add(coefficient.wrapping_mul(u64::from(constant_u32(*value))));
        }
        (int64_constant!(value), true) => {
            *constant =
                constant.wrapping_add(coefficient.wrapping_mul(constant_i64(*value) as u64));
        }
        (uint64_constant!(value), true) => {
            *constant = constant.wrapping_add(coefficient.wrapping_mul(constant_u64(*value)));
        }
        (atom, _) => {
            let entry = atoms.entry(atom_key(atom)).or_insert(0);
            *entry = entry.wrapping_add(coefficient);
        }
    }
}

/// The exact `Integer` counterpart of [`machine_affine_equality`]: sums,
/// differences, and negations flatten into signed atoms and a constant over
/// the integers, with no modulus. When every atom cancels, the sides differ
/// by that constant, which decides equality and, because `Integer` has no
/// overflow, order as well. Atoms are interned terms, keyed by their shared
/// identity. The walk visits each node of the goal once.
pub(super) fn integer_affine_comparison(condition: &ConditionTerm) -> Option<bool> {
    use num_traits::Zero;
    let (left, right) = match condition {
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    let (atoms, difference) = integer_affine_difference(left, right);
    if atoms.values().any(|coefficient| !coefficient.is_zero()) {
        return None;
    }
    let zero = num_bigint::BigInt::zero();
    Some(match condition {
        ConditionTerm::IntegerEqual(..) => difference == zero,
        ConditionTerm::IntegerNotEqual(..) => difference != zero,
        ConditionTerm::IntegerLessThan(..) => difference < zero,
        ConditionTerm::IntegerLessEqual(..) => difference <= zero,
        ConditionTerm::IntegerGreaterThan(..) => difference > zero,
        _ => difference >= zero,
    })
}

fn integer_product_identity(term: &IntegerTerm) -> Option<&SharedIntegerTerm> {
    use num_traits::{One, Zero};
    let IntegerTerm::Multiply(a, b) = term else {
        return None;
    };
    if matches!(a.as_ref(), IntegerTerm::Constant(n) if n.is_zero())
        || matches!(b.as_ref(), IntegerTerm::Constant(n) if n.is_one())
    {
        Some(a)
    } else if matches!(b.as_ref(), IntegerTerm::Constant(n) if n.is_zero())
        || matches!(a.as_ref(), IntegerTerm::Constant(n) if n.is_one())
    {
        Some(b)
    } else {
        None
    }
}

/// One written distributivity step, with opaque operands. This never
/// expands a polynomial or chooses a rewrite location.
pub(super) fn integer_distribution_step(condition: &ConditionTerm) -> bool {
    fn product(a: &SharedIntegerTerm, b: &SharedIntegerTerm) -> SharedIntegerTerm {
        IntegerTerm::Multiply(a.clone(), b.clone()).into()
    }
    fn direction(a: &SharedIntegerTerm, b: &SharedIntegerTerm) -> bool {
        let IntegerTerm::Multiply(x, y) = a.as_ref() else {
            return false;
        };
        for (sum, factor, left) in [(x, y, true), (y, x, false)] {
            let (p, q, subtract) = match sum.as_ref() {
                IntegerTerm::Add(p, q) => (p, q, false),
                IntegerTerm::Subtract(p, q) => (p, q, true),
                _ => continue,
            };
            let (u, v) = if left {
                (product(p, factor), product(q, factor))
            } else {
                (product(factor, p), product(factor, q))
            };
            let expected = if subtract {
                IntegerTerm::Subtract(u, v)
            } else {
                IntegerTerm::Add(u, v)
            };
            if &expected == b.as_ref() {
                return true;
            }
        }
        false
    }
    matches!(condition, ConditionTerm::IntegerEqual(a,b) if direction(a,b) || direction(b,a))
}

/// Explicit `normalize` also distributes constant Integer coefficients.
/// `known` continues to use `integer_affine_comparison`: adding this rule to
/// explicit normalization does not expand its computational leaf. Calls,
/// reads, folds, and products of two symbolic values remain opaque.
pub(super) fn integer_linear_comparison(condition: &ConditionTerm) -> Option<bool> {
    use num_bigint::BigInt;
    use num_traits::Zero;
    use std::collections::{BTreeMap, HashMap, HashSet};
    let (left, right) = match condition {
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    // Intrinsic widening and literal observations have cached value readings.
    // Use the same fact-independent atoms as affine planning; no surrounding
    // context or machine operation identity is imported by this computation.
    let left = left.read_through_ref();
    let right = right.read_through_ref();
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    let mut pending = vec![(left.clone(), false), (right.clone(), false)];
    while let Some((term, expanded)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if expanded {
            order.push(term);
        } else if seen.insert(term.id()) {
            pending.push((term.clone(), true));
            match term.as_ref() {
                IntegerTerm::Add(a, b)
                | IntegerTerm::Subtract(a, b)
                | IntegerTerm::Multiply(a, b) => {
                    pending.push((b.clone(), false));
                    pending.push((a.clone(), false));
                }
                IntegerTerm::Negate(a) => pending.push((a.clone(), false)),
                _ => {}
            }
        }
    }
    // Evaluate constant coefficient DAGs once, independently of facts.
    let mut constants: HashMap<u64, BigInt> = HashMap::new();
    for term in &order {
        let value = match term.as_ref() {
            IntegerTerm::Constant(value) => Some(value.clone()),
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) | IntegerTerm::Multiply(a, b) => {
                match (constants.get(&a.id()), constants.get(&b.id())) {
                    (Some(a), Some(b)) => {
                        let bits = if matches!(term.as_ref(), IntegerTerm::Multiply(..)) {
                            (a.bits() as usize + 1).saturating_mul(b.bits() as usize + 1)
                        } else {
                            a.bits().max(b.bits()) as usize + 1
                        };
                        if crate::instrumentation::deadline_exceeded_with_work(bits) {
                            return None;
                        }
                        Some(match term.as_ref() {
                            IntegerTerm::Add(..) => a + b,
                            IntegerTerm::Subtract(..) => a - b,
                            _ => a * b,
                        })
                    }
                    _ => None,
                }
            }
            IntegerTerm::Negate(a) => constants.get(&a.id()).map(|value| -value),
            _ => None,
        };
        if let Some(value) = value {
            constants.insert(term.id(), value);
        }
    }
    let mut weights: HashMap<u64, BigInt> = HashMap::new();
    *weights.entry(left.id()).or_default() += 1;
    *weights.entry(right.id()).or_default() -= 1;
    let mut atoms: BTreeMap<Vec<u64>, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    for term in order.iter().rev() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        let Some(weight) = weights
            .remove(&term.id())
            .filter(|weight| !weight.is_zero())
        else {
            continue;
        };
        if let Some(value) = constants.get(&term.id()) {
            if crate::instrumentation::deadline_exceeded_with_work(
                (value.bits() as usize + 1).saturating_mul(weight.bits() as usize + 1),
            ) {
                return None;
            }
            constant += value * weight;
            continue;
        }
        match term.as_ref() {
            IntegerTerm::Add(a, b) => {
                *weights.entry(a.id()).or_default() += &weight;
                *weights.entry(b.id()).or_default() += weight;
            }
            IntegerTerm::Subtract(a, b) => {
                *weights.entry(a.id()).or_default() += &weight;
                *weights.entry(b.id()).or_default() -= weight;
            }
            IntegerTerm::Negate(a) => *weights.entry(a.id()).or_default() -= weight,
            IntegerTerm::Multiply(a, b) => {
                let scale = constants
                    .get(&a.id())
                    .map(|value| (value, b))
                    .or_else(|| constants.get(&b.id()).map(|value| (value, a)));
                if let Some((scale, value)) = scale {
                    if crate::instrumentation::deadline_exceeded_with_work(
                        (scale.bits() as usize + 1).saturating_mul(weight.bits() as usize + 1),
                    ) {
                        return None;
                    }
                    *weights.entry(value.id()).or_default() += weight * scale;
                } else {
                    // Collect one monomial without distributing any sum.
                    // Its factors are opaque shared roots. Work follows the
                    // written product, never the surrounding fact context.
                    let mut factors = Vec::new();
                    let mut coefficient = weight;
                    let mut pending = vec![term];
                    while let Some(factor) = pending.pop() {
                        if crate::instrumentation::deadline_exceeded_with_work(1) {
                            return None;
                        }
                        if let Some(value) = constants.get(&factor.id()) {
                            if crate::instrumentation::deadline_exceeded_with_work(
                                (value.bits() as usize + 1)
                                    .saturating_mul(coefficient.bits() as usize + 1),
                            ) {
                                return None;
                            }
                            coefficient *= value;
                        } else {
                            match factor.as_ref() {
                                IntegerTerm::Multiply(a, b) => {
                                    pending.push(a);
                                    pending.push(b);
                                }
                                IntegerTerm::Negate(a) => {
                                    coefficient = -coefficient;
                                    pending.push(a);
                                }
                                _ => factors.push(factor.id()),
                            }
                        }
                    }
                    factors.sort_unstable();
                    *atoms.entry(factors).or_default() += coefficient;
                }
            }
            _ => *atoms.entry(vec![term.id()]).or_default() += weight,
        }
    }
    if atoms.values().any(|weight| !weight.is_zero()) {
        return None;
    }
    let zero = BigInt::zero();
    Some(match condition {
        ConditionTerm::IntegerEqual(..) => constant == zero,
        ConditionTerm::IntegerNotEqual(..) => constant != zero,
        ConditionTerm::IntegerLessThan(..) => constant < zero,
        ConditionTerm::IntegerLessEqual(..) => constant <= zero,
        ConditionTerm::IntegerGreaterThan(..) => constant > zero,
        _ => constant >= zero,
    })
}

/// Check an exact type range or one intrinsic quotient/shift/remainder bound.
/// Only the two operands' fixed bound shapes select observations; no facts,
/// operand history, or nested operations are searched.
pub(super) fn integer_operation_bound_comparison(condition: &ConditionTerm) -> Option<bool> {
    fn scaled(term: &SharedIntegerTerm) -> Option<&SharedMachineIntegerTerm> {
        match term.as_ref() {
            IntegerTerm::Machine(value) => Some(value),
            IntegerTerm::Multiply(a, b) => match (a.as_ref(), b.as_ref()) {
                (IntegerTerm::Constant(_), IntegerTerm::Machine(value))
                | (IntegerTerm::Machine(value), IntegerTerm::Constant(_)) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }
    fn observation(term: &SharedIntegerTerm) -> Option<&SharedMachineIntegerTerm> {
        scaled(term).or_else(|| match term.as_ref() {
            IntegerTerm::Add(a, b) if a.as_const().is_some() => scaled(b),
            IntegerTerm::Add(a, b) if b.as_const().is_some() => scaled(a),
            IntegerTerm::Subtract(a, b) if b.as_const().is_some() => scaled(a),
            _ => None,
        })
    }
    let (left, right) = match condition {
        ConditionTerm::IntegerLessThan(value, bound)
        | ConditionTerm::IntegerGreaterThan(bound, value) => {
            if let (IntegerTerm::Machine(value), IntegerTerm::Constant(bound)) =
                (value.as_ref(), bound.as_ref())
                && positive_literal_remainder_divisor(value.ty(), value.operand_view()).as_ref()
                    == Some(bound)
            {
                return Some(true);
            }
            return None;
        }
        ConditionTerm::IntegerLessEqual(left, right) => (left, right),
        ConditionTerm::IntegerGreaterEqual(left, right) => (right, left),
        _ => return None,
    };
    // Exact type ranges inspect just the observation and its stated endpoint.
    // Unrelated constant comparisons should not construct affine range claims.
    if let (IntegerTerm::Constant(endpoint), IntegerTerm::Machine(value)) =
        (left.as_ref(), right.as_ref())
        && endpoint == &crate::kernel::machine_integer::range::observation_range(value).0
    {
        return Some(true);
    }
    if let (IntegerTerm::Machine(value), IntegerTerm::Constant(endpoint)) =
        (left.as_ref(), right.as_ref())
        && endpoint == &crate::kernel::machine_integer::range::observation_range(value).1
    {
        return Some(true);
    }
    let mut expected = None;
    for value in [observation(left), observation(right)]
        .into_iter()
        .flatten()
    {
        for upper in [false, true] {
            crate::instrumentation::record_deterministic_work(1);
            let Some(bound) = crate::kernel::machine_integer::bounds::operation_bound(value, upper)
            else {
                continue;
            };
            if expected.is_none() {
                expected = Some(super::super::integer_arithmetic::integer_affine_claim(
                    &Proposition::condition_is(condition.clone(), true),
                )?);
            }
            if super::super::integer_arithmetic::integer_affine_claim(&bound).as_ref()
                == expected.as_ref()
            {
                return Some(true);
            }
        }
    }
    None
}

/// The affine form of `left - right`: each atom's coefficient and the
/// constant. Interned terms share subterms, so a sum such as
/// `a + a` over `a = b + b` reaches one node along many paths; coefficients
/// are propagated over the term DAG in topological order, visiting each node
/// once, rather than walking every path.
/// One opaque leaf of an affine difference. A range fold is keyed by its
/// checked alpha identity, so two separately lowered copies of one fold
/// (each with its own binders) cancel; any other leaf is keyed by its shared
/// term identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum AffineLeaf {
    Term(u64),
    Fold(u64),
}

fn integer_affine_difference(
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
) -> (
    std::collections::BTreeMap<AffineLeaf, num_bigint::BigInt>,
    num_bigint::BigInt,
) {
    use num_traits::Zero;
    // Postorder over the arithmetic nodes, so reversing it puts every node
    // before the operands it passes its coefficient to.
    let mut order = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![(left.clone(), false), (right.clone(), false)];
    let mut reduced_matches = std::collections::HashMap::new();
    while let Some((term, expanded)) = stack.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if expanded {
            order.push(term);
            continue;
        }
        if !seen.insert(term.id()) {
            continue;
        }
        stack.push((term.clone(), true));
        match term.as_ref() {
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push((right.clone(), false));
                stack.push((left.clone(), false));
            }
            IntegerTerm::Negate(value) => stack.push((value.clone(), false)),
            IntegerTerm::AlgebraicMatch { .. } => {
                if let Some(value) =
                    crate::kernel::proof::term_rewrite::TermRewrite::reduce_known_integer_match(
                        &term,
                    )
                {
                    stack.push((value.clone(), false));
                    reduced_matches.insert(term.id(), value);
                }
            }
            other => {
                if let Some(value) = integer_product_identity(other) {
                    stack.push((value.clone(), false));
                }
            }
        }
    }
    let mut coefficients = std::collections::HashMap::<u64, num_bigint::BigInt>::new();
    *coefficients.entry(left.id()).or_default() += 1;
    *coefficients.entry(right.id()).or_default() -= 1;
    let mut atoms = std::collections::BTreeMap::new();
    let mut fold_records = Vec::new();
    let mut constant = num_bigint::BigInt::zero();
    for term in order.iter().rev() {
        crate::instrumentation::record_deterministic_work(1);
        let Some(coefficient) = coefficients.remove(&term.id()) else {
            continue;
        };
        if coefficient.is_zero() {
            continue;
        }
        if let Some(value) = reduced_matches.get(&term.id()) {
            *coefficients.entry(value.id()).or_default() += coefficient;
            continue;
        }
        if let IntegerTerm::Machine(value) = term.as_ref()
            && let Some(value) = value.literal_conversion_value()
        {
            constant += value.to_integer() * coefficient;
            continue;
        }
        match term.as_ref() {
            IntegerTerm::Add(left, right) => {
                *coefficients.entry(left.id()).or_default() += &coefficient;
                *coefficients.entry(right.id()).or_default() += &coefficient;
            }
            IntegerTerm::Subtract(left, right) => {
                *coefficients.entry(left.id()).or_default() += &coefficient;
                *coefficients.entry(right.id()).or_default() -= &coefficient;
            }
            IntegerTerm::Negate(value) => {
                *coefficients.entry(value.id()).or_default() -= &coefficient;
            }
            IntegerTerm::Constant(value) => constant += value * coefficient,
            other if integer_product_identity(other).is_some() => {
                let value = integer_product_identity(other).unwrap();
                *coefficients.entry(value.id()).or_default() += coefficient;
            }
            IntegerTerm::RangeFold { .. } => {
                // The interner reuses an id only while a record is alive, so
                // hold each record until the difference is complete.
                let leaf =
                    match crate::kernel::proof::integer_affine_atoms::intern_integer_fold_atom(term)
                    {
                        Some(record) => {
                            let leaf = AffineLeaf::Fold(record.id());
                            fold_records.push(record);
                            leaf
                        }
                        None => AffineLeaf::Term(term.id()),
                    };
                *atoms.entry(leaf).or_insert_with(num_bigint::BigInt::zero) += coefficient;
            }
            _ => {
                *atoms
                    .entry(AffineLeaf::Term(term.id()))
                    .or_insert_with(num_bigint::BigInt::zero) += coefficient;
            }
        }
    }
    drop(fold_records);
    (atoms, constant)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_viewability_checks_only_the_named_span() {
        let _session = VerificationSession::enter();
        let sample = |unrelated, size: u32| {
            let mut memory = SymbolicMemory::new().with_block("target", 1024);
            for i in 0..unrelated {
                memory = memory.with_block(format!("other_{i}"), 4);
            }
            let goal = Proposition::MemoryLoadable {
                memory,
                base: Address {
                    base: "target".into(),
                    offset: AddressOffset::Constant(4),
                },
                bytes: MachineTerm::constant(size).into(),
                wide: false,
            };
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal))
        };
        let measurements = [0, 32, 128].map(|n| [4, 1020, 1021].map(|size| sample(n, size)));
        for checks in measurements {
            assert_eq!(checks.map(|(holds, _)| holds), [true, true, false]);
            for ((_, work), (_, baseline)) in checks.into_iter().zip(measurements[0]) {
                assert!(work <= baseline + 16, "{measurements:?}");
            }
        }
    }

    #[test]
    fn computation_reads_constants_at_the_comparison_format() {
        for (format, expected) in [
            (MachineIntegerType::Int32, true),
            (MachineIntegerType::UInt32, false),
        ] {
            let condition = ConditionTerm::Compare {
                format,
                relation: CompareRelation::LessThan,
                left: Box::new(MachineTerm::constant(u32::MAX)),
                right: Box::new(MachineTerm::constant(0)),
            };
            assert!(computes_leaf(&Proposition::condition_is(
                condition.clone(),
                expected
            )));
            assert!(!computes_leaf(&Proposition::condition_is(
                condition, !expected
            )));
        }
    }

    #[test]
    fn computation_does_not_use_float_reflexivity() {
        let nan = MachineTerm::constant(0x7fc00000);
        let goal = Proposition::condition_is(
            ConditionTerm::Float32(FloatCondition::Comparison {
                operator: ComparisonOperator::Equal,
                left: Box::new(nan.clone()),
                right: Box::new(nan),
            }),
            true,
        );
        assert!(!computes_leaf(&goal));
    }
    #[test]
    fn integer_linear_normalization_matches_independent_bigint_evaluation() {
        use num_bigint::BigInt;
        fn evaluate(term: &IntegerTerm, x: &BigInt, y: &BigInt) -> BigInt {
            match term {
                IntegerTerm::Variable(variable) if *variable == Variable(0) => x.clone(),
                IntegerTerm::Variable(variable) if *variable == Variable(1) => y.clone(),
                IntegerTerm::Constant(value) => value.clone(),
                IntegerTerm::Add(a, b) => evaluate(a, x, y) + evaluate(b, x, y),
                IntegerTerm::Subtract(a, b) => evaluate(a, x, y) - evaluate(b, x, y),
                IntegerTerm::Negate(a) => -evaluate(a, x, y),
                IntegerTerm::Multiply(a, b) => evaluate(a, x, y) * evaluate(b, x, y),
                _ => panic!("unexpected oracle term: {term:?}"),
            }
        }
        let large: BigInt = (BigInt::from(1) << 160) + 1;
        let mut samples: Vec<BigInt> = [-3, -1, 0, 1, 4].into_iter().map(BigInt::from).collect();
        samples.extend([large.clone(), -large]);
        for a in &samples {
            for b in &samples {
                let x = IntegerTerm::Variable(Variable(0));
                let y = IntegerTerm::Variable(Variable(1));
                let left = IntegerTerm::add(
                    IntegerTerm::multiply(
                        IntegerTerm::Constant(a.clone()),
                        IntegerTerm::add(x.clone(), y.clone()),
                    ),
                    IntegerTerm::multiply(IntegerTerm::Constant(b.clone()), x.clone()),
                );
                let right = IntegerTerm::add(
                    IntegerTerm::multiply(IntegerTerm::Constant(a + b), x),
                    IntegerTerm::multiply(IntegerTerm::Constant(a.clone()), y),
                );
                let condition =
                    ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into());
                assert_eq!(integer_linear_comparison(&condition), Some(true));
                for x in &samples {
                    for y in &samples {
                        assert_eq!(evaluate(&left, x, y), evaluate(&right, x, y));
                    }
                }
                let wrong = ConditionTerm::IntegerEqual(
                    left.into(),
                    IntegerTerm::add(right, IntegerTerm::constant_i64(1)).into(),
                );
                assert_eq!(integer_linear_comparison(&wrong), Some(false));
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/proof/fact_reasoning/computation/tests.rs");
    }
}
