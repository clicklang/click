//! Goal-local computation for a simple proof leaf.
//!
//! The `computes_leaf` entry point uses only the goal, including exact
//! stored scalar and union cell values. Legacy normalization shares arithmetic
//! below but supplies its own atom key.
use crate::kernel::machine_integer::bounds::positive_literal_remainder_divisor;
use crate::kernel::*;
use crate::kernel::{
    constant_i64, constant_u32, constant_u64, int32_constant, int64_constant, uint64_constant,
};
use std::borrow::Cow;

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
    if let Some(holds) = crate::kernel::spec::checks_retained_sequence_comparison(
        goal,
        expected,
        |condition, value| condition_value(condition) == Some(value),
    ) {
        return holds;
    }
    let value = match goal {
        Proposition::ConditionIs(condition, truth) => condition
            .operand_view()
            .closed_float_predicate_value()
            .or_else(|| {
                let condition = condition.native_compat();
                condition_value(condition)
                    .or_else(|| super::machine_ranges::comparison_value(condition))
            })
            .map(|value| value == *truth),
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            let left_root = left.root().map(select_closed_algebraic_root);
            let right_root = right.root().map(select_closed_algebraic_root);
            if let (Some(left), Some(right)) = (left_root, right_root)
                && left == right
            {
                Some(true)
            } else {
                let left = left_root
                    .and_then(KernelTerm::algebraic_native_term)
                    .unwrap_or_else(|| left.native_compat());
                let right = right_root
                    .and_then(KernelTerm::algebraic_native_term)
                    .unwrap_or_else(|| right.native_compat());
                algebraic_equality(left, right)
            }
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => {
            let left = left.native_compat();
            let right = right.native_compat();
            if unchanged_integer_folds_equal(left, right) {
                Some(true)
            } else {
                integer_affine_comparison(&ConditionTerm::IntegerEqual(
                    left.clone().into(),
                    right.clone().into(),
                ))
            }
        }
        // Empty spans have no accesses to check. Other concrete spans
        // use one bounds lookup in the exact memory of the goal.
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => {
            let size = if *wide {
                bytes
                    .native_compat()
                    .uint64_as_const()
                    .and_then(|size| u32::try_from(size).ok())
            } else {
                bytes.as_const()
            };
            size.is_some_and(|size| size == 0 || memory.access_in_bounds(base, size))
                .then_some(true)
        }
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
            ..
        } => memory
            .indexed_read_is_defined(pointer, *value_type)
            .then_some(true),
        Proposition::ResourceContains { parent, child }
            if let (Resource::Memory(parent), Resource::Memory(child)) =
                (parent.as_ref(), child.as_ref())
                && !parent.has_holes()
                && !child.has_holes()
                && let Some((parent_base, parent_start, parent_end)) =
                    crate::kernel::primitives::constant_memory_coordinates(parent)
                && let Some((child_base, child_start, child_end)) =
                    crate::kernel::primitives::constant_memory_coordinates(child) =>
        {
            // Compare complete physical intervals on the same written base,
            // even when their element widths differ.
            (parent_base == child_base
                && parent_start <= parent_end
                && child_start <= child_end
                && parent_start <= child_start
                && child_end <= parent_end)
                .then_some(true)
        }
        Proposition::ResourceSeparate { left, right }
            if let (Resource::Memory(left), Resource::Memory(right)) =
                (left.as_ref(), right.as_ref()) =>
        {
            (declared_object_ranges_separate(left, right)
                || crate::kernel::primitives::constant_memory_overlap(left, right) == Some(false))
            .then_some(true)
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

/// A machine fold whose body is its own accumulator retains the initial
/// value for every range. Neither the endpoints nor any facts are inspected.
fn unchanged_fold_initial(operand: MachineOperandView<'_>) -> Option<MachineOperandView<'_>> {
    let (accumulator, _, [_, _, initial, body]) = operand.fold()?;
    (body.variable() == Some(&accumulator)).then_some(initial)
}

fn unchanged_fold_observation(value: &IntegerTerm) -> Option<IntegerTerm> {
    let IntegerTerm::Machine(value) = value else {
        return None;
    };
    if value.ty() != MachineIntegerType::Int32 {
        return None;
    }
    unchanged_fold_initial(value.operand_view())?.observe(value.ty())
}

fn unchanged_integer_folds_equal(left: &IntegerTerm, right: &IntegerTerm) -> bool {
    let a = unchanged_fold_observation(left);
    let b = unchanged_fold_observation(right);
    (a.is_some() || b.is_some()) && a.as_ref().unwrap_or(left) == b.as_ref().unwrap_or(right)
}

fn unchanged_machine_folds_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    let left = MachineOperandView::Legacy(left);
    let right = MachineOperandView::Legacy(right);
    let a = unchanged_fold_initial(left);
    let b = unchanged_fold_initial(right);
    if a.is_none() && b.is_none() {
        return false;
    }
    a.unwrap_or(left)
        .observe(MachineIntegerType::Int32)
        .zip(b.unwrap_or(right).observe(MachineIntegerType::Int32))
        .is_some_and(|(left, right)| left == right)
}

/// These exact block kinds use the structural separation rule without
/// asking about pointer loads or resolving aliases. Range formation has
/// its own checked obligations before the separation goal is opened.
fn declared_object_ranges_separate(left: &MemoryRange, right: &MemoryRange) -> bool {
    use AddressBase::{AutomaticLocal, ExternalArgument, ExternalObject};
    let left = left.base();
    let right = right.base();
    (matches!(
        (&left.base, &right.base),
        (
            AutomaticLocal { .. },
            AutomaticLocal { .. } | ExternalArgument | ExternalObject(_),
        ) | (ExternalArgument | ExternalObject(_), AutomaticLocal { .. })
    ) || left.base.is_static_storage_block() && right.base.is_static_storage_block())
        && left.blocks_proven_distinct(right)
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

/// Guards whose truth is determined by their literal operands.
pub(in crate::kernel) fn literal_value_if_guard(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(_) => {}
        ConditionTerm::Compare { left, right, .. }
            if matches!(left.as_ref(), MachineTerm::Constant { .. })
                && matches!(right.as_ref(), MachineTerm::Constant { .. }) => {}
        integer_comparison_condition!(left, right)
            if matches!(left.as_ref(), IntegerTerm::Constant(_))
                && matches!(right.as_ref(), IntegerTerm::Constant(_)) => {}
        _ => return None,
    }
    trivial_condition_value(condition)
}

pub(in crate::kernel) fn is_literal_value_if_guard_root(guard: &KernelTerm) -> bool {
    match guard.node() {
        KernelTermNode::BoolLiteral(_) => true,
        KernelTermNode::BoolCompare { arguments, .. } => arguments
            .iter()
            .all(|operand| matches!(operand.node(), KernelTermNode::MachineLiteral(_))),
        KernelTermNode::IntegerCompare { arguments, .. } => arguments
            .iter()
            .all(|operand| matches!(operand.node(), KernelTermNode::IntegerLiteral(_))),
        _ => false,
    }
}

/// A by-value copy can hold the source member as its exact typed view.
/// Read that immutable entry without resolving aliases or earlier writes.
fn stored_int32_union_member(read: &MachineTerm) -> Option<&MachineTerm> {
    let MachineTerm::MemoryLoad(point, pointer, LoadKind::Int32) = read else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(1);
    let ProgramValue::Int32(value) = point
        .memory()
        .indexed_union_value(pointer, ProgramType::Int32)?
    else {
        return None;
    };
    Some(value)
}

/// A native comparison can read a literal already stored at its exact
/// typed cell. Run slots, aliases, and earlier memory states stay opaque.
fn stored_int32_literal(term: &MachineTerm) -> Option<MachineIntegerConstant> {
    let MachineTerm::MemoryLoad(point, pointer, LoadKind::Int32) = term else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(1);
    let ProgramValue::Int32(stored) = point.memory().indexed_scalar_value(pointer)? else {
        return None;
    };
    MachineIntegerType::Int32.constant_from_term(stored)
}

/// An unsigned byte promotion preserves the value of the exact selected
/// cell. The value can be compared as a byte or promoted to C's int.
fn stored_uint8_literal(
    format: MachineIntegerType,
    operand: MachineOperandView<'_>,
) -> Option<MachineIntegerConstant> {
    let byte = match format {
        MachineIntegerType::UInt8 => operand,
        MachineIntegerType::Int32 => {
            let (
                MachineCastSpelling::Generic,
                MachineIntegerType::UInt8,
                MachineIntegerType::Int32,
                byte,
            ) = operand.cast()?
            else {
                return None;
            };
            byte
        }
        _ => return None,
    };
    let (point, pointer, LoadKind::UInt8) = byte.read_point()? else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(1);
    let ProgramValue::UInt8(stored) = point.memory().indexed_stored_value(pointer)? else {
        return None;
    };
    let value = MachineIntegerType::UInt8.constant_from_term(stored)?;
    MachineIntegerConstant::from_unsigned(format.format(), value.bits())
}

/// Retained native comparisons may read the operands as exact Integers.
fn stored_uint8_observation(term: &IntegerTerm) -> Option<num_bigint::BigInt> {
    let IntegerTerm::Machine(value) = term else {
        return None;
    };
    stored_uint8_literal(value.ty(), value.operand_view()).map(|byte| byte.to_integer())
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
            if matches!(
                condition,
                ConditionTerm::IntegerEqual(..) | ConditionTerm::IntegerNotEqual(..)
            ) && unchanged_integer_folds_equal(left, right)
            {
                return Some(matches!(condition, ConditionTerm::IntegerEqual(..)));
            }
            if matches!(
                condition,
                ConditionTerm::IntegerEqual(..) | ConditionTerm::IntegerNotEqual(..)
            ) && let Some(equal) = conditional_int32_equality(left, right)
            {
                return Some(equal == matches!(condition, ConditionTerm::IntegerEqual(..)));
            }
            let left_byte = stored_uint8_observation(left);
            let right_byte = stored_uint8_observation(right);
            if (left_byte.is_some() || right_byte.is_some())
                && let (Some(a), Some(b)) = (
                    left_byte.as_ref().or_else(|| left.as_const()),
                    right_byte.as_ref().or_else(|| right.as_const()),
                )
            {
                return Some(match condition {
                    ConditionTerm::IntegerEqual(..) => a == b,
                    ConditionTerm::IntegerNotEqual(..) => a != b,
                    ConditionTerm::IntegerLessThan(..) => a < b,
                    ConditionTerm::IntegerLessEqual(..) => a <= b,
                    ConditionTerm::IntegerGreaterThan(..) => a > b,
                    ConditionTerm::IntegerGreaterEqual(..) => a >= b,
                    _ => unreachable!(),
                });
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
            if *format == MachineIntegerType::Int32
                && *relation == CompareRelation::Equal
                && (unchanged_machine_folds_equal(left, right)
                    || stored_int32_union_member(left) == Some(right)
                    || stored_int32_union_member(right) == Some(left))
            {
                return Some(true);
            }
            let a = MachineOperandView::Legacy(left);
            let b = MachineOperandView::Legacy(right);
            if *format == MachineIntegerType::Int32
                && *relation == CompareRelation::Equal
                && (a.conditional_view().is_some() || b.conditional_view().is_some())
                && let (Some(a), Some(b)) = (a.observe(*format), b.observe(*format))
                && let Some(equal) = conditional_int32_equality(&a, &b)
            {
                return Some(equal);
            }
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
            let literals = (
                format.constant_from_term(left),
                format.constant_from_term(right),
            );
            let literals = if *format == MachineIntegerType::Int32 {
                match literals {
                    (Some(value), None) => (Some(value), stored_int32_literal(right)),
                    (None, Some(value)) => (stored_int32_literal(left), Some(value)),
                    both => both,
                }
            } else {
                literals
            };
            let (left_literal, right_literal) = literals;
            if let (Some(left), Some(right)) = (
                left_literal.or_else(|| stored_uint8_literal(*format, a)),
                right_literal.or_else(|| stored_uint8_literal(*format, b)),
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

fn reduce_known_int32_match_operands(
    condition: &ConditionTerm,
) -> Option<(CompareRelation, [Cow<'_, MachineTerm>; 2])> {
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
    let operands = [left.as_ref(), right.as_ref()].map(|operand| {
        TermRewrite::reduce_known_int32_match(operand)
            .map_or_else(|| Cow::Borrowed(operand), Cow::Owned)
    });
    operands
        .iter()
        .any(|operand| matches!(operand, Cow::Owned(_)))
        .then_some((*relation, operands))
}

pub(in crate::kernel) fn reduce_known_int32_match_comparison(
    condition: &ConditionTerm,
) -> Option<ConditionTerm> {
    let (relation, [left, right]) = reduce_known_int32_match_operands(condition)?;
    Some(ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation,
        left: Box::new(left.into_owned()),
        right: Box::new(right.into_owned()),
    })
}

pub(super) fn known_int32_match_comparison_value(condition: &ConditionTerm) -> Option<bool> {
    let (relation, [left, right]) = reduce_known_int32_match_operands(condition)?;
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

/// Evaluate only a chain of selected machine arms. Constructor rewriting
/// already substitutes the fields, so each guard is checked in its written
/// form without resolving reads, variable aliases, or calls.
fn conditional_int32_observation(value: &IntegerTerm) -> Option<IntegerTerm> {
    let IntegerTerm::Machine(value) = value else {
        return None;
    };
    if value.ty() != MachineIntegerType::Int32 {
        return None;
    }
    let mut operand = value.operand_view();
    let (mut guard, mut arms) = operand.conditional_view()?;
    loop {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        operand = arms[usize::from(!int32_conditional_guard(guard)?)];
        let Some(next) = operand.conditional_view() else {
            return operand.observe(MachineIntegerType::Int32);
        };
        (guard, arms) = next;
    }
}

fn int32_conditional_guard(guard: BooleanOperandView<'_>) -> Option<bool> {
    if let Some(ConditionTerm::Constant(value)) = guard.native_leaf() {
        return Some(*value);
    }
    if let BooleanOperandView::Shared(root) = guard
        && let KernelTermNode::BoolLiteral(value) = root.node()
    {
        return Some(*value);
    }
    let (MachineIntegerType::Int32, CompareRelation::Equal, [left, right]) = guard.comparison()?
    else {
        return None;
    };
    match (left, right) {
        (MachineOperandView::Shared(a), MachineOperandView::Shared(b)) if a == b => Some(true),
        (MachineOperandView::Legacy(a), MachineOperandView::Legacy(b)) if std::ptr::eq(a, b) => {
            Some(true)
        }
        _ if left
            .variable()
            .is_some_and(|var| right.variable() == Some(var)) =>
        {
            Some(true)
        }
        _ => Some(left.literal()?.as_const()? == right.literal()?.as_const()?),
    }
}

fn conditional_int32_equality(left: &IntegerTerm, right: &IntegerTerm) -> Option<bool> {
    let a = conditional_int32_observation(left);
    let b = conditional_int32_observation(right);
    if a.is_none() && b.is_none() {
        return None;
    }
    let a = a.as_ref().unwrap_or(left);
    let b = b.as_ref().unwrap_or(right);
    if a == b {
        Some(true)
    } else {
        Some(a.as_const()? == b.as_const()?)
    }
}

// Read the selected branch before crossing the native compatibility
// boundary. A dormant branch may refer to a large shared constructor.
fn select_closed_algebraic_root(mut root: &KernelTerm) -> &KernelTerm {
    while let KernelTermNode::AlgebraicIf {
        arguments: [guard, then_term, else_term],
    } = root.node()
    {
        if !is_literal_value_if_guard_root(guard) {
            break;
        }
        let Some(truth) = KernelTermExport::condition(guard)
            .ok()
            .and_then(|guard| literal_value_if_guard(&guard))
        else {
            break;
        };
        crate::instrumentation::record_deterministic_work(1);
        root = if truth { then_term } else { else_term };
    }
    root
}

/// Read a direct algebraic equation or disequation through its closed arms.
pub(in crate::kernel) fn closed_algebraic_if_comparison(goal: &Proposition) -> Option<Proposition> {
    let (equality, equal) = match goal {
        Proposition::Not(body) => (body.as_ref(), false),
        proposition => (proposition, true),
    };
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = equality else {
        return None;
    };
    let reduced = |term: &StoredAlgebraicTerm| {
        if let Some(root) = term.root() {
            let selected = select_closed_algebraic_root(root);
            return (selected != root).then(|| {
                StoredAlgebraicTerm::from_root(selected.clone()).expect("typed algebraic arm")
            });
        }
        let input = term.native_compat();
        let selected = select_closed_algebraic_arm(input);
        (!std::ptr::eq(input, selected)).then(|| selected.clone().into())
    };
    let (a, b) = (reduced(left), reduced(right));
    if a.is_none() && b.is_none() {
        return None;
    }
    let proposition = Proposition::Equal(
        Term::Algebraic(a.unwrap_or_else(|| left.clone())),
        Term::Algebraic(b.unwrap_or_else(|| right.clone())),
    );
    Some(if equal {
        proposition
    } else {
        Proposition::Not(Box::new(proposition))
    })
}

fn selected_closed_integer_arm(term: &SharedIntegerTerm) -> Option<&SharedIntegerTerm> {
    let IntegerTerm::If {
        condition,
        then_term,
        else_term,
    } = term.as_ref()
    else {
        return None;
    };
    let truth = literal_value_if_guard(condition)?;
    Some(if truth { then_term } else { else_term })
}

pub(in crate::kernel) fn closed_integer_if_comparison(
    condition: &ConditionTerm,
) -> Option<ConditionTerm> {
    map_integer_comparison(condition, |term| {
        let mut arm = selected_closed_integer_arm(term)?;
        while let Some(selected) = selected_closed_integer_arm(arm) {
            crate::instrumentation::record_deterministic_work(1);
            arm = selected;
        }
        Some(arm.clone())
    })
}

pub(super) fn map_integer_comparison(
    condition: &ConditionTerm,
    reduce: impl Fn(&SharedIntegerTerm) -> Option<SharedIntegerTerm>,
) -> Option<ConditionTerm> {
    let integer_comparison_condition!(left, right) = condition else {
        return None;
    };
    let (left_result, right_result) = (reduce(left), reduce(right));
    if left_result.is_none() && right_result.is_none() {
        return None;
    }
    let left = left_result.unwrap_or_else(|| left.clone());
    let right = right_result.unwrap_or_else(|| right.clone());
    Some(match condition {
        ConditionTerm::IntegerLessThan(..) => ConditionTerm::IntegerLessThan(left, right),
        ConditionTerm::IntegerLessEqual(..) => ConditionTerm::IntegerLessEqual(left, right),
        ConditionTerm::IntegerGreaterThan(..) => ConditionTerm::IntegerGreaterThan(left, right),
        ConditionTerm::IntegerGreaterEqual(..) => ConditionTerm::IntegerGreaterEqual(left, right),
        ConditionTerm::IntegerEqual(..) => ConditionTerm::IntegerEqual(left, right),
        ConditionTerm::IntegerNotEqual(..) => ConditionTerm::IntegerNotEqual(left, right),
        _ => unreachable!(),
    })
}

fn select_closed_algebraic_arm(mut term: &AlgebraicTerm) -> &AlgebraicTerm {
    while let AlgebraicTermNode::If {
        condition,
        then_term,
        else_term,
    } = &term.node
    {
        let Some(truth) = literal_value_if_guard(condition) else {
            break;
        };
        crate::instrumentation::record_deterministic_work(1);
        term = if truth { then_term } else { else_term };
    }
    term
}

fn algebraic_equality(left: &AlgebraicTerm, right: &AlgebraicTerm) -> Option<bool> {
    let left = select_closed_algebraic_arm(left);
    let right = select_closed_algebraic_arm(right);
    if left.algebraic_type != right.algebraic_type {
        return None;
    }
    if left == right {
        return Some(true);
    }
    use crate::kernel::reasoning::path_facts::algebraic_match_rebuilds_scrutinee;
    if (algebraic_match_rebuilds_scrutinee(left, right)
        || algebraic_match_rebuilds_scrutinee(right, left))
        && left.is_well_formed()
        && right.is_well_formed()
    {
        return Some(true);
    }
    if constructor_match_forwards_payload(left, right)
        || constructor_match_forwards_payload(right, left)
    {
        return Some(true);
    }
    let projected_left = constructor_match_projection(left);
    let projected_right = constructor_match_projection(right);
    let left = projected_left.unwrap_or(left);
    let right = projected_right.unwrap_or(right);
    if (projected_left.is_some() || projected_right.is_some()) && left == right {
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

/// Check a selected constructor arm that forwards scalar payloads directly
/// into its result, possibly alongside captured Integer variables. Compare
/// the written fields without building a rewritten match.
fn constructor_match_forwards_payload(matched: &AlgebraicTerm, expected: &AlgebraicTerm) -> bool {
    let (
        AlgebraicTermNode::Match { scrutinee, arms },
        AlgebraicTermNode::Constructor {
            variant: expected_variant,
            fields: expected_fields,
        },
    ) = (&matched.node, &expected.node)
    else {
        return false;
    };
    let AlgebraicTermNode::Constructor { variant, fields } = &scrutinee.node else {
        return false;
    };
    crate::instrumentation::record_deterministic_work(arms.len());
    let Some(arm) = arms.iter().find(|arm| arm.variant == *variant) else {
        return false;
    };
    let AlgebraicTermNode::Constructor {
        variant: result_variant,
        fields: result_fields,
    } = &arm.body.node
    else {
        return false;
    };
    if arm.bindings.len() != fields.len()
        || result_variant != expected_variant
        || result_fields.len() != expected_fields.len()
    {
        return false;
    }

    crate::instrumentation::record_deterministic_work(fields.len() + result_fields.len());
    let mut payloads = std::collections::HashMap::with_capacity(fields.len());
    for (binder, field) in arm.bindings.iter().zip(fields) {
        let variable = match (binder, field) {
            (
                AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(variable))),
                AlgebraicValue::Program(ProgramValue::Int32(int32_constant!(_))),
            )
            | (
                AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
                AlgebraicValue::Integer(IntegerTerm::Constant(_) | IntegerTerm::Variable(_)),
            ) => variable,
            _ => return false,
        };
        if payloads.insert(*variable, field).is_some() {
            return false;
        }
    }
    result_fields
        .iter()
        .zip(expected_fields)
        .all(|(field, expected)| {
            let (variable, captured) = match field {
                AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(variable))) => {
                    (variable, None)
                }
                AlgebraicValue::Integer(IntegerTerm::Variable(variable)) => (variable, Some(field)),
                _ => return false,
            };
            payloads
                .get(variable)
                .copied()
                .or(captured)
                .is_some_and(|payload| {
                    std::mem::discriminant(payload) == std::mem::discriminant(field)
                        && payload == expected
                })
        })
        && matched.is_well_formed()
        && expected.is_well_formed()
}

/// Select an algebraic field when the match names its constructor and
/// the selected arm returns that field's binder directly.
fn constructor_match_projection(term: &AlgebraicTerm) -> Option<&AlgebraicTerm> {
    let AlgebraicTermNode::Match { scrutinee, arms } = &term.node else {
        return None;
    };
    let AlgebraicTermNode::Constructor { variant, fields } = &scrutinee.node else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(arms.len());
    let arm = arms.iter().find(|arm| arm.variant == *variant)?;
    let AlgebraicTermNode::Variable(variable) = arm.body.node else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(arm.bindings.len());
    let mut selected = None;
    use crate::kernel::proof::term_rewrite::{BindingCarrier, typed_declaration_variable};
    let mut binders = std::collections::HashSet::with_capacity(arm.bindings.len());
    for (binding, field) in arm.bindings.iter().zip(fields) {
        let (carrier, binder) = typed_declaration_variable(binding)?;
        if !binders.insert(binder) {
            return None;
        }
        if matches!(carrier, BindingCarrier::Algebraic) && binder == variable {
            let AlgebraicValue::Algebraic(field) = field else {
                return None;
            };
            selected = Some(field);
        }
    }
    selected.filter(|_| term.is_well_formed())
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
    // A rewrite may leave the old count's zero addend in a retained sum.
    // Its observation has the same type range as the written machine value.
    fn unshifted_observation(term: &SharedIntegerTerm) -> Option<&SharedMachineIntegerTerm> {
        let term = match term.as_ref() {
            IntegerTerm::Add(a, b) if a.as_const().is_some_and(num_traits::Zero::is_zero) => b,
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b)
                if b.as_const().is_some_and(num_traits::Zero::is_zero) =>
            {
                a
            }
            _ => term,
        };
        let IntegerTerm::Machine(value) = term.as_ref() else {
            return None;
        };
        Some(value)
    }
    if let (Some(endpoint), Some(value)) = (left.as_const(), unshifted_observation(right))
        && endpoint == &crate::kernel::machine_integer::range::observation_range(value).0
    {
        return Some(true);
    }
    if let (Some(value), Some(endpoint)) = (unshifted_observation(left), right.as_const())
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

/// Read the value of a trivial machine fold without enumerating its range.
pub(super) fn observe_trivial_int32_fold(
    value: &SharedMachineIntegerTerm,
) -> Option<SharedIntegerTerm> {
    if value.ty() != MachineIntegerType::Int32 {
        return None;
    }
    let KernelTermNode::Fold(fold) = value.shared_operand()?.node() else {
        return None;
    };
    observe_machine_fold_result(value.ty(), &fold.trivial_int32_result()?)
}

fn observe_machine_fold_result(
    format: MachineIntegerType,
    result: &KernelTerm,
) -> Option<SharedIntegerTerm> {
    Some(MachineOperandView::Shared(result).observe(format)?.into())
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
    let mut reduced_operands = std::collections::HashMap::new();
    let mut fold_reads = std::collections::HashMap::new();
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
            IntegerTerm::Machine(value) => {
                if let Some(result) = KernelFold::reduce_bounded_int32_in(value, &mut fold_reads)
                    && let Some(value) = observe_machine_fold_result(value.ty(), &result)
                {
                    stack.push((value.clone(), false));
                    reduced_operands.insert(term.id(), value);
                }
            }
            IntegerTerm::If { .. } => {
                if let Some(arm) = selected_closed_integer_arm(&term) {
                    stack.push((arm.clone(), false));
                    reduced_operands.insert(term.id(), arm.clone());
                }
            }
            IntegerTerm::AlgebraicMatch { .. } => {
                if let Some(value) =
                    crate::kernel::proof::term_rewrite::TermRewrite::reduce_known_integer_match(
                        &term,
                    )
                {
                    stack.push((value.clone(), false));
                    reduced_operands.insert(term.id(), value);
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
        if let Some(value) = reduced_operands.get(&term.id()) {
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
    fn exact_union_copy_checks_only_the_selected_typed_views() {
        let _session = VerificationSession::enter();
        let source = Address {
            base: "copy-source".into(),
            offset: AddressOffset::Constant(4),
        };
        let destination = Address {
            base: "copy-destination".into(),
            offset: AddressOffset::Constant(4),
        };
        let read = |memory: SymbolicMemory, pointer: &Address| {
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&crate::kernel::intern_memory(memory)),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            )
        };
        let empty = SymbolicMemory::new();
        let copied = read(empty.clone(), &source);
        let different = read(empty.clone(), &source.offset_by_bytes(4));
        let check = |memory, expected: &MachineTerm| {
            let condition = ConditionTerm::equal(read(memory, &destination), expected.clone());
            let goal = Proposition::condition_is(condition, true);
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal))
        };
        let samples = [0, 32, 128].map(|count| {
            let mut memory = empty.clone().store_union(
                destination.clone(),
                ProgramType::Int32,
                ProgramValue::Int32(copied.clone()),
            );
            for i in 0..count {
                let other = Address {
                    base: format!("copy-unrelated-{i}").into(),
                    offset: AddressOffset::Constant(0),
                };
                memory = memory.store_union(other, ProgramType::Int32, crate::kernel::int32(i));
            }
            let matching = check(memory.clone(), &copied);
            let different = check(memory.clone(), &different);
            let overwritten = memory.store_union(
                destination.clone(),
                ProgramType::UInt8,
                crate::kernel::uint8(0),
            );
            [matching, different, check(overwritten, &copied)]
        });
        for checks in samples {
            assert_eq!(checks.map(|(holds, _)| holds), [true, false, false]);
            for ((_, work), (_, baseline)) in checks.into_iter().zip(samples[0]) {
                assert!(work <= baseline + 16, "{samples:?}");
            }
        }
    }

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
    fn empty_viewability_needs_no_live_base() {
        let _session = VerificationSession::enter();
        for wide in [false, true] {
            let observations = [0, 32, 128].map(|unrelated| {
                let mut memory = SymbolicMemory::new();
                for i in 0..unrelated {
                    memory = memory.with_block(format!("empty-unrelated-{i}"), 4);
                }
                [0, 1].map(|size| {
                    let bytes = if wide {
                        StoredMachineTerm::new(
                            MachineIntegerType::UInt64,
                            MachineTerm::uint64_constant(size),
                        )
                    } else {
                        MachineTerm::constant(size as u32).into()
                    };
                    let goal = Proposition::MemoryLoadable {
                        memory: memory.clone(),
                        base: Address::symbolic(Variable(402901)),
                        bytes,
                        wide,
                    };
                    crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal))
                })
            });
            for checks in observations {
                assert_eq!(checks.map(|(holds, _)| holds), [true, false]);
                for ((_, work), (_, baseline)) in checks.into_iter().zip(observations[0]) {
                    assert_eq!(work, baseline);
                }
            }
        }
    }

    #[test]
    fn constant_span_separation_checks_the_entire_byte_interval() {
        let _session = VerificationSession::enter();
        let base = Address::symbolic(Variable(402902));
        let span = |base, width| {
            Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                base,
                0u32.into(),
                1u32.into(),
                width,
            )))
        };
        for (right, separate) in [
            (base.offset_by_bytes(7), false),
            (base.offset_by_bytes(8), true),
            (Address::symbolic(Variable(402903)), false),
        ] {
            let goal = Proposition::ResourceSeparate {
                left: span(base.clone(), 8),
                right: span(right, 4),
            };
            assert_eq!(computes_leaf(&goal), separate, "{goal:?}");
        }
    }

    #[test]
    fn stored_literal_order_uses_the_named_int32_cell_and_state() {
        let _session = VerificationSession::enter();
        let base = SymbolicMemory::global_pointer("resource-body-literal");
        let sample = |unrelated| {
            let mut memory = SymbolicMemory::new();
            for i in 0..unrelated {
                memory = memory.store(
                    SymbolicMemory::global_pointer(format!("resource-body-neighbor-{i}")),
                    int32(0),
                );
            }
            let before = memory.clone().store(base.clone(), int32(1));
            let after = before.clone().store(base.clone(), int32(u32::MAX));
            let check = |memory| {
                let read = MachineTerm::MemoryLoad(
                    ProgramPoint::at(&crate::kernel::intern_memory(memory)),
                    Box::new(base.clone()),
                    LoadKind::Int32,
                );
                let goal = Proposition::condition_is(
                    ConditionTerm::signed_greater_equal(read, 0u32.into()),
                    true,
                );
                crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal))
            };
            [check(before), check(after), check(memory)]
        };
        let observations = [0, 32, 128].map(sample);
        for checks in observations {
            assert_eq!(checks.map(|(holds, _)| holds), [true, false, false]);
            for ((_, work), (_, baseline)) in checks.into_iter().zip(observations[0]) {
                assert!(work <= baseline + 16, "{observations:?}");
            }
        }
    }

    #[test]
    fn rewritten_zero_count_preserves_the_observations_type_range() {
        let _session = VerificationSession::enter();
        let n = IntegerTerm::from_machine(
            MachineIntegerType::Int32,
            MachineTerm::Variable(Variable(402904)),
        )
        .unwrap();
        let observed =
            |count| IntegerTerm::Add(IntegerTerm::constant_i64(count).into(), n.clone().into());
        let upper = |value: IntegerTerm| {
            Proposition::condition_is(
                ConditionTerm::IntegerLessEqual(
                    value.into(),
                    IntegerTerm::constant_i64(i64::from(i32::MAX)).into(),
                ),
                true,
            )
        };
        let lower = |value: IntegerTerm| {
            Proposition::condition_is(
                ConditionTerm::IntegerLessEqual(
                    IntegerTerm::constant_i64(i64::from(i32::MIN)).into(),
                    value.into(),
                ),
                true,
            )
        };
        assert!(computes_leaf(&upper(observed(0))));
        assert!(computes_leaf(&lower(observed(0))));
        assert!(!computes_leaf(&upper(observed(1))));
        assert!(!computes_leaf(&lower(observed(-1))));
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
