//! Root-local observation rules. Each query names its operands and performs
//! a fixed number of exact premise lookups; it never derives an interval.
use crate::kernel::machine_integer::{conversion, identity};
use crate::kernel::*;
use num_bigint::BigInt;
use num_traits::Zero;

fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
    Proposition::condition_is(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
}

fn holds(p: &Proposition, available: &impl Fn(&Proposition) -> bool) -> bool {
    available(p) || super::computes_leaf(p)
}

fn comparison_holds(
    condition: ConditionTerm,
    truth: bool,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let premise = condition.truth_claim(truth);
    holds(&premise, available)
        || crate::kernel::machine_integer::comparison::structural_native_comparison_of_integer_observation(
            &condition, truth,
        )
        .is_some_and(|(condition, truth)| holds(&condition.truth_claim(truth), available))
        || super::order_claim_forms(&premise)
            .iter()
            .any(|form| form != &premise && available(form))
}

/// Compare the result of a retained fold against the same written operand.
/// The reduced comparison names a single premise for the exact-fact lookup.
fn trivial_fold_comparison(condition: &ConditionTerm) -> Option<ConditionTerm> {
    super::computation::map_integer_comparison(condition, |operand| {
        let machine = operand.root().exact_shared_integer_observation()?;
        super::computation::observe_trivial_int32_fold(&machine)
    })
}

fn in_range(
    value: &IntegerTerm,
    format: crate::kernel::primitives::MachineIntegerFormat,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let (min, max) = format.bounds();
    holds(&le(IntegerTerm::Constant(min), value.clone()), available)
        && holds(&le(value.clone(), IntegerTerm::Constant(max)), available)
}

// A native guard is already explicit input. Shared comparisons retain their
// operand DAGs through observation handles; never export a shared guard tree.
fn written_guard(view: BooleanOperandView<'_>) -> Option<ConditionTerm> {
    if let Some(native) = view.native_leaf() {
        return Some(native.clone());
    }
    if let Some((format, relation, operands)) = view.comparison() {
        return Some(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format, relation, operands,
            ),
        );
    }
    if let BooleanOperandView::Shared(root) = view {
        return match root.node() {
            KernelTermNode::Variable(variable) => Some(ConditionTerm::Variable(*variable)),
            KernelTermNode::BoolLiteral(value) => Some(ConditionTerm::Constant(*value)),
            // These guards keep their exact scalar or pointer operands.
            KernelTermNode::IntegerCompare { .. }
            | KernelTermNode::PointerEqual(_)
            | KernelTermNode::AddressEqual { .. } => KernelTermExport::condition(root).ok(),
            // Other shared guards need their own explicit logical steps.
            _ => None,
        };
    }
    None
}

fn guard_holds(
    guard: BooleanOperandView<'_>,
    truth: bool,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    if let Some(condition) = written_guard(guard)
        && holds(&condition.truth_claim(truth), available)
    {
        return true;
    }
    // Lowering can store a negated native order as its complementary order.
    // Query it using the same retained operands as the conditional guard.
    if let Some((format, relation, operands)) = guard.comparison() {
        let complement = match relation {
            CompareRelation::LessThan => Some(CompareRelation::GreaterEqual),
            CompareRelation::LessEqual => Some(CompareRelation::GreaterThan),
            CompareRelation::GreaterThan => Some(CompareRelation::LessEqual),
            CompareRelation::GreaterEqual => Some(CompareRelation::LessThan),
            CompareRelation::Equal => None,
        };
        if let Some(complement) = complement {
            let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format, complement, operands,
            );
            if holds(&condition.truth_claim(!truth), available) {
                return true;
            }
        }
    }
    let Some([left, right]) = guard.algebraic_equality() else {
        return false;
    };
    let equality = Proposition::Equal(
        Term::Algebraic(StoredAlgebraicTerm::from_root(left).expect("algebraic operand")),
        Term::Algebraic(StoredAlgebraicTerm::from_root(right).expect("algebraic operand")),
    );
    let premise = if truth {
        equality
    } else {
        Proposition::Not(Box::new(equality))
    };
    holds(&premise, available)
}

fn integer_arm(
    value: &SharedIntegerTerm,
    other: &SharedIntegerTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    if let KernelTermNode::IntegerIf {
        arguments: [guard, then_term, else_term],
    } = value.root().node()
    {
        let same_value = |arm: &KernelTerm| {
            arm == other.root() || SharedIntegerTerm::from_root(arm.clone()) == *other
        };
        let then_matches = same_value(then_term);
        let else_matches = same_value(else_term);
        return (then_matches && else_matches)
            || (then_matches && guard_holds(BooleanOperandView::Shared(guard), true, available))
            || (else_matches && guard_holds(BooleanOperandView::Shared(guard), false, available));
    }
    let Some(machine) = value.root().exact_shared_integer_observation() else {
        return false;
    };
    let Some((condition, arms)) = machine.operand_view().conditional_view() else {
        return false;
    };
    let arms = arms.map(|arm| arm.observe(machine.ty()));
    let other = other.as_ref();
    if arms.iter().all(|arm| arm.as_ref() == Some(other)) {
        return true;
    }
    [(true, &arms[0]), (false, &arms[1])]
        .into_iter()
        .any(|(truth, arm)| arm.as_ref() == Some(other) && guard_holds(condition, truth, available))
}

/// Select a narrow machine arm at its written format. Promoted Integer
/// readings need not preserve a narrow conditional at the comparison root.
fn narrow_machine_arm(
    condition: &StoredConditionTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let Some((format, CompareRelation::Equal, [left, right])) =
        condition.operand_view().comparison()
    else {
        return false;
    };
    if format.format().bits() >= 32 {
        return false;
    }
    for (conditional, other) in [(left, right), (right, left)] {
        let Some((condition, [then_arm, else_arm])) = conditional.conditional_view() else {
            continue;
        };
        let Some(other) = other.observe(format) else {
            continue;
        };
        if [then_arm, else_arm].into_iter().all(|arm| {
            arm.observe(format)
                .is_some_and(|arm| arm.value_read() == other.value_read())
        }) {
            return true;
        }
        for (truth, arm) in [(true, then_arm), (false, else_arm)] {
            if arm
                .observe(format)
                .is_some_and(|arm| arm.value_read() == other.value_read())
                && guard_holds(condition, truth, available)
            {
                return true;
            }
        }
    }
    false
}

fn identity(
    value: &IntegerTerm,
    other: &IntegerTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    // Neutral bitwise operands are root-local computation, including source
    // shapes a generic theorem's native substitution has already folded.
    if let IntegerTerm::Machine(machine) = value
        && let Some((ty, op, operands)) = machine.operand_view().binary()
        && ty == machine.ty()
    {
        for [zero, operand] in [operands, [operands[1], operands[0]]] {
            if zero
                .literal()
                .and_then(|n| ty.constant_from_term(&n))
                .is_some_and(|n| n.to_integer().is_zero())
            {
                if op == MachineBinaryOp::BitwiseAnd && other.as_const().is_some_and(Zero::is_zero)
                {
                    return true;
                }
                if op == MachineBinaryOp::BitwiseOr && operand.observe(ty).as_ref() == Some(other) {
                    return true;
                }
            }
        }
    }
    if let Some((ty, exact)) = identity::explicit_mathematical(value)
        && identity::same_exact_value(&exact, other)
        && in_range(other, ty.format(), available)
    {
        return true;
    }
    if let Some((operand, ty)) = conversion::integer_conversion(value)
        && operand.as_ref() == other
        && in_range(other, ty.format(), available)
    {
        return true;
    }
    if let Some(format) = conversion::cast(value, other)
        && in_range(other, format, available)
    {
        return true;
    }
    // A constant left shift is multiplication by 2^k inside its format.
    // The signed operand's nonnegativity remains an explicit guard.
    let IntegerTerm::Machine(machine) = value else {
        return false;
    };
    let Some((ty, MachineBinaryOp::ShiftLeft, [operand, count])) = machine.operand_view().binary()
    else {
        return false;
    };
    if ty.format().bits() != machine.ty().format().bits() {
        return false;
    }
    let ty = machine.ty();
    let Some(count) = crate::kernel::machine_integer::bounds::constant_shift_count(count) else {
        return false;
    };
    if count >= ty.format().bits() {
        return false;
    }
    let Some(operand) = operand.observe(ty) else {
        return false;
    };
    let scale = IntegerTerm::Constant(BigInt::from(1) << count);
    let exact = IntegerTerm::Multiply(operand.clone().into(), scale.clone().into());
    let commuted = IntegerTerm::Multiply(scale.into(), operand.clone().into());
    (other == &exact || other == &commuted)
        && (!ty.format().is_signed()
            || holds(&le(IntegerTerm::constant_i64(0), operand), available))
        && in_range(other, ty.format(), available)
}

/// A word AND with a nonnegative literal mask has this exact Integer range.
pub(crate) fn literal_mask_bounds(observed: &SharedMachineIntegerTerm) -> Option<[Proposition; 2]> {
    let (format, MachineBinaryOp::BitwiseAnd, [left, right]) = observed.operand_view().binary()?
    else {
        return None;
    };
    let ty = observed.ty();
    if format.format().bits() != ty.format().bits() {
        return None;
    }
    let mask = [left, right].into_iter().find_map(|operand| {
        let mask = ty.constant_from_term(&operand.literal()?)?.to_integer();
        (mask >= BigInt::zero()).then_some(mask)
    })?;
    let value = IntegerTerm::Machine(observed.clone());
    Some([
        le(IntegerTerm::constant_i64(0), value.clone()),
        le(value, IntegerTerm::constant(mask)),
    ])
}

fn mask_bound(a: &IntegerTerm, b: &IntegerTerm, available: &impl Fn(&Proposition) -> bool) -> bool {
    let (observed, lower) = match (a, b) {
        (IntegerTerm::Constant(zero), IntegerTerm::Machine(value)) if zero.is_zero() => {
            (value, true)
        }
        (IntegerTerm::Machine(value), _) => (value, false),
        _ => return false,
    };
    let Some((ty, MachineBinaryOp::BitwiseAnd, [left, right])) = observed.operand_view().binary()
    else {
        return false;
    };
    if ty.format().bits() != observed.ty().format().bits() {
        return false;
    }
    let ty = observed.ty();
    for (operand, mask) in [(left, right), (right, left)] {
        let Some(mask) = mask
            .literal()
            .and_then(|n| ty.constant_from_term(&n))
            .map(|n| n.to_integer())
        else {
            continue;
        };
        if mask < BigInt::zero() {
            continue;
        }
        if lower || b.as_const() == Some(&mask) {
            return true;
        }
        if let Some(operand) = operand.observe(ty)
            && &operand == b
            && holds(&le(IntegerTerm::constant_i64(0), operand), available)
        {
            return true;
        }
    }
    false
}

fn unsigned_remainder_bound(
    lower: &IntegerTerm,
    upper: &IntegerTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let IntegerTerm::Machine(remainder) = lower else {
        return false;
    };
    let Some((ty, MachineBinaryOp::Remainder, [dividend, divisor])) =
        remainder.operand_view().binary()
    else {
        return false;
    };
    if ty != remainder.ty()
        || ty.format().is_signed()
        || dividend.observe(ty).as_ref() != Some(upper)
    {
        return false;
    }
    let Some(divisor) = divisor.observe(ty) else {
        return false;
    };
    let zero: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
    let one = IntegerTerm::constant_i64(1).into();
    let divisor: SharedIntegerTerm = divisor.into();
    [
        (
            ConditionTerm::IntegerEqual(divisor.clone(), zero.clone()),
            false,
        ),
        (ConditionTerm::IntegerLessThan(zero, divisor.clone()), true),
        (ConditionTerm::IntegerLessEqual(one, divisor), true),
    ]
    .into_iter()
    .any(|(guard, truth)| comparison_holds(guard, truth, available))
}

fn signed_division_sign(
    left: &IntegerTerm,
    right: &IntegerTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let (result, nonnegative) = if left.as_const().is_some_and(Zero::is_zero) {
        (right, true)
    } else if right.as_const().is_some_and(Zero::is_zero) {
        (left, false)
    } else {
        return false;
    };
    let (dividend, divisor, quotient, overflow_exclusion) = match result {
        IntegerTerm::TruncatingQuotient(n, d) | IntegerTerm::TruncatingRemainder(n, d) => {
            let quotient = matches!(result, IntegerTerm::TruncatingQuotient(..));
            (n.clone(), d.clone(), quotient, None)
        }
        IntegerTerm::Machine(result) => {
            let Some((
                ty @ (MachineIntegerType::Int32 | MachineIntegerType::Int64),
                op @ (MachineBinaryOp::Divide | MachineBinaryOp::Remainder),
                [n, d],
            )) = result.operand_view().binary()
            else {
                return false;
            };
            if ty != result.ty() {
                return false;
            }
            let (Some(dividend), Some(divisor)) = (n.observe(ty), d.observe(ty)) else {
                return false;
            };
            (
                dividend.into(),
                divisor.into(),
                op == MachineBinaryOp::Divide,
                Some((ty, n, d)),
            )
        }
        _ => return false,
    };
    let zero: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
    let ordered = |a: &SharedIntegerTerm, b: &SharedIntegerTerm| {
        comparison_holds(
            ConditionTerm::IntegerLessEqual(a.clone(), b.clone()),
            true,
            available,
        )
    };
    let strict = |a: &SharedIntegerTerm, b: &SharedIntegerTerm| {
        comparison_holds(
            ConditionTerm::IntegerLessThan(a.clone(), b.clone()),
            true,
            available,
        )
    };
    let nonzero = || {
        comparison_holds(
            ConditionTerm::IntegerEqual(divisor.clone(), zero.clone()),
            false,
            available,
        )
    };
    let positive = strict(&zero, &divisor)
        || ordered(&IntegerTerm::constant_i64(1).into(), &divisor)
        || (ordered(&zero, &divisor) && nonzero());
    let negative = || {
        strict(&divisor, &zero)
            || ordered(&divisor, &IntegerTerm::constant_i64(-1).into())
            || (ordered(&divisor, &zero) && nonzero())
    };
    let dividend_nonnegative = || ordered(&zero, &dividend) || strict(&zero, &dividend);
    let dividend_nonpositive = || ordered(&dividend, &zero) || strict(&dividend, &zero);
    let has_sign = |nonnegative| {
        if nonnegative {
            dividend_nonnegative()
        } else {
            dividend_nonpositive()
        }
    };
    let checked_domain = || {
        let Some((ty, n, d)) = overflow_exclusion else {
            return true;
        };
        let exclusion = Proposition::signed_division_exclusion_views(ty, n, d);
        holds(&exclusion, available)
            || matches!(&exclusion, Proposition::Or(a, b)
                if holds(a, available) || holds(b, available))
    };
    if quotient {
        // Equal signs give a nonnegative quotient. The signed minimum divided
        // by -1 must be excluded separately if neither sign rules it out.
        (positive && has_sign(nonnegative))
            || (has_sign(!nonnegative) && negative() && (!nonnegative || checked_domain()))
    } else {
        // The sign of the remainder depends only on its dividend.
        has_sign(nonnegative)
            && (positive || negative() || nonzero())
            && (nonnegative || positive || checked_domain())
    }
}

fn bool_arm(
    value: &ConditionTerm,
    matches_arm: impl Fn(&ConditionTerm) -> bool,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let ConditionTerm::BoolIf {
        condition,
        then_condition,
        else_condition,
    } = value
    else {
        return false;
    };
    [(true, then_condition), (false, else_condition)]
        .into_iter()
        .any(|(polarity, arm)| {
            matches_arm(arm)
                && guard_holds(BooleanOperandView::Native(condition), polarity, available)
        })
}

fn algebraic_arm(
    value: &AlgebraicTerm,
    other: &AlgebraicTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let AlgebraicTermNode::If {
        condition,
        then_term,
        else_term,
    } = &value.node
    else {
        return false;
    };
    value.algebraic_type == other.algebraic_type
        && [(true, then_term), (false, else_term)]
            .into_iter()
            .any(|(polarity, arm)| {
                arm.as_ref() == other && holds(&condition.truth_claim(polarity), available)
            })
}

pub(crate) fn is_quotient_remainder_order(goal: &Proposition) -> bool {
    let Some((condition, true)) = goal.condition_native() else {
        return false;
    };
    let machine_division = |operand: MachineOperandView<'_>| {
        matches!(
            operand.binary(),
            Some((_, MachineBinaryOp::Divide | MachineBinaryOp::Remainder, _))
        )
    };
    match condition {
        ConditionTerm::IntegerLessEqual(a, b) | ConditionTerm::IntegerGreaterEqual(a, b) => {
            [a.as_ref(), b.as_ref()]
                .into_iter()
                .any(|operand| match operand {
                    IntegerTerm::TruncatingQuotient(..) | IntegerTerm::TruncatingRemainder(..) => {
                        true
                    }
                    IntegerTerm::Machine(term) => machine_division(term.operand_view()),
                    _ => false,
                })
        }
        ConditionTerm::Compare {
            relation: CompareRelation::LessEqual | CompareRelation::GreaterEqual,
            left,
            right,
            ..
        } => [left.as_ref(), right.as_ref()]
            .into_iter()
            .any(|operand| machine_division(MachineOperandView::Legacy(operand))),
        _ => false,
    }
}

/// The first range ends where the second starts. Ordering its endpoints
/// makes the element count nonnegative, so even a modular byte count can
/// only shorten the first range. The second range occupies bytes forward
/// from that shared address.
fn adjacent_range_separation(
    first: &MemoryRange,
    second: &MemoryRange,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    first.wide_bounds().is_none()
        && first.end_pointer() == second.start_pointer()
        && comparison_holds(
            ConditionTerm::signed_less_equal(first.start().clone(), first.end().clone()),
            true,
            available,
        )
}

/// A declared uint32 has no invalid bit patterns. Its four initialized
/// representation bytes suffice, even when a call reports them as facts.
pub(in crate::kernel) fn known_uint32_from_defined_bytes(
    goal: &Proposition,
    mut contains: impl FnMut(&Proposition) -> bool,
) -> bool {
    let Proposition::MemoryReadDefined {
        at,
        memory,
        pointer,
        value_type: ProgramType::UInt32,
    } = goal
    else {
        return false;
    };
    memory.is_live_declared_local_uint32(pointer)
        && (0..ProgramType::UInt32.byte_width()).all(|offset| {
            crate::instrumentation::record_deterministic_work(1);
            contains(&Proposition::MemoryReadDefined {
                at: *at,
                memory: memory.clone(),
                pointer: pointer.offset_by_bytes(offset),
                value_type: ProgramType::UInt8,
            })
        })
}

/// The product's width, operands and bound name each possible guard. The
/// number of sign cases and the number of lookups per case are fixed.
fn signed_product_bound(goal: &Proposition, available: &impl Fn(&Proposition) -> bool) -> bool {
    super::super::arithmetic_special::signed_product_guard_candidates(goal).any(|guards| {
        guards.into_iter().all(|guard| {
            guard.condition_native().is_some_and(|(condition, truth)| {
                comparison_holds(condition.clone(), *truth, available)
            })
        })
    })
}

fn exact_float_bound(goal: &Proposition, available: &impl Fn(&Proposition) -> bool) -> bool {
    [false, true].into_iter().any(|strict| {
        super::super::arithmetic_special::exact_float_bound_source(goal, strict).is_some_and(
            |source| available(&source) || super::order_claim_forms(&source).iter().any(available),
        )
    })
}

pub(crate) fn known_bridge_leaf(
    goal: &Proposition,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if let Some(reading) = super::closed_algebraic_if_comparison(goal)
        && holds(&reading, available)
    {
        return true;
    }
    use super::super::arithmetic_special::{
        promoted_right_shift_bound, shift_count_mask_requirements,
    };
    if promoted_right_shift_bound(goal) == Some(true)
        || shift_count_mask_requirements(goal).is_some_and(|bounds| {
            bounds.iter().all(|bound| {
                bound.condition_native().is_some_and(|(condition, truth)| {
                    comparison_holds(condition.clone(), *truth, available)
                })
            })
        })
    {
        return true;
    }
    if super::super::arithmetic_special::float_zero_product_premise(goal)
        .is_some_and(|premise| holds(&premise, available))
        || super::super::arithmetic_special::float_self_operation_bounds(goal).is_some_and(
            |(finite, nonzero)| {
                holds(&finite, available)
                    && nonzero.as_ref().is_none_or(|fact| holds(fact, available))
            },
        )
        || super::super::arithmetic_special::bitwise_division_disequality(
            goal,
            |condition, truth| comparison_holds(condition, truth, available),
        )
    {
        return true;
    }
    match goal {
        Proposition::ConditionIs(_, true) if exact_float_bound(goal, available) => true,
        Proposition::ConditionIs(condition, true) if narrow_machine_arm(condition, available) => {
            true
        }
        Proposition::ConditionIs(condition, truth)
            if let Some(reduced) =
                super::closed_integer_if_comparison(condition.native_compat())
                && comparison_holds(reduced, *truth, available) =>
        {
            true
        }
        Proposition::ConditionIs(condition, truth)
            if let Some(reduced) = trivial_fold_comparison(condition.native_compat())
                && comparison_holds(reduced, *truth, available) =>
        {
            true
        }
        Proposition::ConditionIs(condition, true)
            if let Some(wide) = pointer_projection_source(condition.native_compat()) =>
        {
            comparison_holds(
                ConditionTerm::IntegerLessEqual(
                    wide.into(),
                    IntegerTerm::constant_i64(i64::from(i32::MAX)).into(),
                ),
                true,
                available,
            )
        }
        Proposition::ConditionIs(condition, truth)
            if let Some(reduced) =
                super::reduce_known_int32_match_comparison(condition.native_compat()) =>
        {
            comparison_holds(reduced, *truth, available)
        }
        Proposition::ResourceSeparate { left, right }
            if matches!(
                (left.as_ref(), right.as_ref()),
                (Resource::Footprint(_), _) | (_, Resource::Footprint(_))
            ) =>
        {
            crate::kernel::region_footprint::separate_members(left, right, |fact| {
                available(fact)
                    || match fact {
                        Proposition::ResourceSeparate { left, right }
                            if let (Resource::Memory(left), Resource::Memory(right)) =
                                (left.as_ref(), right.as_ref()) =>
                        {
                            adjacent_range_separation(left, right, available)
                                || adjacent_range_separation(right, left, available)
                        }
                        _ => false,
                    }
            })
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            integer_arm(a, b, available)
                || integer_arm(b, a, available)
                || identity(a.as_ref(), b.as_ref(), available)
                || identity(b.as_ref(), a.as_ref(), available)
                || super::super::arithmetic_special::signed_max_shift_identity_count_bound(a, b)
                    .is_some_and(|bound| holds(&bound, available))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::IntegerLessEqual(a, b) | ConditionTerm::IntegerGreaterEqual(b, a),
                _,
            )) = condition_source_0.condition_native() =>
        {
            mask_bound(a, b, available)
                || ((matches!(a.as_ref(), IntegerTerm::Multiply(..)) && b.as_const().is_some()
                    || matches!(b.as_ref(), IntegerTerm::Multiply(..)) && a.as_const().is_some())
                    && signed_product_bound(condition_source_0, available))
                || unsigned_remainder_bound(a, b, available)
                || signed_division_sign(a, b, available)
                || condition_source_0
                    .condition_native()
                    .is_some_and(|(condition, _)| {
                        condition
                            .nonnegative_division_bound_guards()
                            .is_some_and(|guards| {
                                guards
                                    .into_iter()
                                    .all(|guard| holds(&guard.truth_claim(true), available))
                            })
                    })
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::BoolEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            bool_arm(a, |arm| arm == b.as_ref(), available)
                || bool_arm(b, |arm| arm == a.as_ref(), available)
        }
        condition_source_0 @ Proposition::ConditionIs(_, truth)
            if let Some((condition @ ConditionTerm::BoolIf { .. }, _)) =
                condition_source_0.condition_native() =>
        {
            bool_arm(
                condition,
                |arm| holds(&arm.truth_claim(*truth), available),
                available,
            )
        }
        Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
            algebraic_arm(a.native_compat(), b.native_compat(), available)
                || algebraic_arm(b.native_compat(), a.native_compat(), available)
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::AlgebraicEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            algebraic_arm(a, b, available) || algebraic_arm(b, a, available)
        }
        _ => crate::kernel::proof::arithmetic_special::finite_float_reflexivity_premise(goal)
            .is_some_and(|premise| holds(&premise, available)),
    }
}

/// Read the full-width source of a signed low-word projection at the same
/// base and stride. A bound on that source gives equality of the offsets.
/// Raw complete pointer comparisons retain their own domain requirements.
pub(crate) fn pointer_projection_source(condition: &ConditionTerm) -> Option<IntegerTerm> {
    if !matches!(
        condition,
        ConditionTerm::AddressEqual(..) | ConditionTerm::AddressOffsetEqual(..)
    ) {
        return None;
    }
    let (a, b) = condition.pointer_offset_sides()?;
    // A pointer parameter is itself an exact offset in the abstract
    // argument block. Cancel that common prefix before comparing its indices.
    let (a, b) = match (a, b) {
        (AddressOffset::Add(base, a), AddressOffset::Add(other, b)) if base == other => {
            (a.as_ref(), b.as_ref())
        }
        _ => (a, b),
    };
    for (narrow, wide) in [(a, b), (b, a)] {
        if let (
            AddressOffset::Int32Scaled {
                value: narrow,
                byte_width,
            },
            AddressOffset::Int64Scaled {
                value: wide,
                byte_width: wide_width,
                unsigned: true,
            },
        ) = (narrow, wide)
            && byte_width == wide_width
            && *byte_width > 0
            && let Some((
                _,
                MachineIntegerType::UInt64,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                source,
            )) = narrow.operand_view().cast()
            && crate::kernel::machine_operand_syntax_cmp(source, wide.operand_view()).is_eq()
        {
            return wide.operand_view().observe(MachineIntegerType::UInt64);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::machine_integer::{Operation, representation};
    use crate::kernel::proof::PureFactStore;

    fn known(goal: &Proposition, premises: &[Proposition]) -> bool {
        let facts = PureFactStore::from_ordered(premises);
        known_bridge_leaf(goal, &|p| facts.pure_known_available(p))
    }
    fn equality(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::condition_is(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }
    fn operation(ty: MachineIntegerType, op: Operation) -> Option<(IntegerTerm, IntegerTerm)> {
        let a = MachineTerm::Variable(Variable(995701));
        let b = MachineTerm::Variable(Variable(995702));
        let native =
            representation::operation_word(ty, op, Box::new(a.clone()), Box::new(b.clone()))?;
        Some((
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(ty, native)),
            op.exact(
                IntegerTerm::from_machine(ty, a)?,
                IntegerTerm::from_machine(ty, b)?,
            ),
        ))
    }
    fn bounds(value: &IntegerTerm, ty: MachineIntegerType) -> [Proposition; 2] {
        let (min, max) = ty.format().bounds();
        [
            le(IntegerTerm::Constant(min), value.clone()),
            le(value.clone(), IntegerTerm::Constant(max)),
        ]
    }
    #[test]
    fn defined_local_word_checks_four_exact_bytes_among_unrelated_facts() {
        let _session = VerificationSession::enter();
        let word = SymbolicMemory::local_pointer("word");
        let memory = SymbolicMemory::new().with_declared_scalar_block(
            word.base.clone(),
            4,
            ProgramType::UInt32,
        );
        let defined = |pointer, value_type| Proposition::MemoryReadDefined {
            at: None,
            memory: memory.clone(),
            pointer,
            value_type,
        };
        let goal = defined(word.clone(), ProgramType::UInt32);
        for count in [0, 16, 256] {
            let mut premises = (0..count)
                .map(|index| defined(Address::symbolic(Variable(index)), ProgramType::UInt8))
                .collect::<Vec<_>>();
            for offset in 0..4 {
                let facts = PureFactStore::from_ordered(&premises);
                assert!(!known_uint32_from_defined_bytes(&goal, |byte| facts.contains(byte)));
                premises.push(defined(word.offset_by_bytes(offset), ProgramType::UInt8));
            }
            let facts = PureFactStore::from_ordered(&premises);
            let mut lookups = 0;
            assert!(known_uint32_from_defined_bytes(&goal, |byte| {
                lookups += 1;
                facts.contains(byte)
            }));
            assert_eq!(lookups, 4);
        }
    }

    #[test]
    fn known_footprint_separation_checks_selected_members() {
        let _session = VerificationSession::enter();
        let cell = |n| {
            Resource::Memory(MemoryRange::new_with_element_width(
                Address::symbolic(Variable(n)),
                0u32.into(),
                1u32.into(),
                4,
            ))
        };
        let separate = |a, b| Proposition::ResourceSeparate {
            left: Box::new(a),
            right: Box::new(b),
        };
        let before = ExecutionState::new();
        let kept = cell(995800);
        let sample = |writes: usize, extra: usize, omit: bool| {
            let members = (0..writes)
                .map(|i| cell(995801 + i as u64))
                .collect::<imbl::Vector<_>>();
            let mut facts = members
                .iter()
                .skip(usize::from(omit))
                .map(|write| separate(write.clone(), kept.clone()))
                .collect::<Vec<_>>();
            facts.extend((0..extra).map(|i| separate(cell(996000 + i as u64), kept.clone())));
            let goal = separate(
                Resource::Footprint(RegionFootprint::sequence(
                    "write".into(),
                    &before,
                    &before,
                    members,
                    true,
                )),
                kept.clone(),
            );
            let facts = PureFactStore::from_ordered(&facts);
            crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|fact| facts.pure_known_available(fact))
            })
        };
        assert!(sample(0, 0, false).0);
        assert!(!sample(2, 0, false).0);
        let observations =
            [0, 32, 128].map(|extra| [sample(1, extra, false), sample(1, extra, true)]);
        for [success, refusal] in observations {
            assert!(success.0 && !refusal.0);
            assert!(success.1 <= observations[0][0].1 + 16, "{observations:?}");
            assert!(refusal.1 <= observations[0][1].1 + 16, "{observations:?}");
        }
    }

    #[test]
    fn adjacent_footprint_needs_order_and_the_exact_boundary() {
        let _session = VerificationSession::enter();
        let base = Address::symbolic(Variable(997400));
        let endpoint = MachineTerm::Variable(Variable(997401));
        let memory = |base, end| {
            Resource::Memory(MemoryRange::new_with_element_width(
                base,
                0u32.into(),
                end,
                4,
            ))
        };
        let write = memory(base.clone(), endpoint.clone());
        let before = ExecutionState::new();
        let footprint = Resource::Footprint(RegionFootprint::sequence(
            "write".into(),
            &before,
            &before,
            [write].into_iter().collect(),
            true,
        ));
        let boundary = base.offset_by_elements(endpoint.clone(), 4);
        let held = Proposition::condition_is(
            ConditionTerm::signed_less_equal(0u32.into(), endpoint),
            true,
        );
        let check = |offset, facts: &PureFactStore| {
            let goal = Proposition::ResourceSeparate {
                left: Box::new(footprint.clone()),
                right: Box::new(memory(
                    Address {
                        base: boundary.base.clone(),
                        offset: AddressOffset::add(
                            boundary.offset.clone(),
                            AddressOffset::Constant(offset),
                        ),
                    },
                    1u32.into(),
                )),
            };
            crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|fact| facts.pure_known_available(fact))
            })
        };
        let observations = [0, 32, 128].map(|count| {
            let unrelated = (0..count)
                .map(|i| {
                    Proposition::condition_is(
                        ConditionTerm::signed_less_equal(
                            0u32.into(),
                            MachineTerm::Variable(Variable(997500 + i)),
                        ),
                        true,
                    )
                })
                .collect::<Vec<_>>();
            let without_order = PureFactStore::from_ordered(&unrelated);
            let with_order = without_order.with_kernel_checked_fact(held.clone());
            [
                check(0, &with_order),
                check(0, &without_order),
                check(-1, &with_order),
            ]
        });
        for checks in observations {
            assert_eq!(checks.map(|(holds, _)| holds), [true, false, false]);
            for ((_, work), (_, baseline)) in checks.into_iter().zip(observations[0]) {
                assert!(work <= baseline + 16, "{observations:?}");
            }
        }
    }

    #[test]
    fn known_operation_identities_check_both_exact_operands_and_bounds() {
        let _session = VerificationSession::enter();
        for ty in crate::kernel::machine_integer::FORMATS {
            for op in Operation::ALL {
                let Some((observed, exact)) = operation(ty, op) else {
                    assert!(ty.format().bits() == 128);
                    continue;
                };
                let goal = equality(observed.clone(), exact.clone());
                let bounds = bounds(&exact, ty);
                assert!(known(&goal, &bounds), "{ty:?}, {op:?}");
                assert!(!known(&goal, &bounds[..1]), "missing upper {ty:?}, {op:?}");
                assert!(!known(&goal, &bounds[1..]), "missing lower {ty:?}, {op:?}");
                let wrong = IntegerTerm::Add(exact.into(), IntegerTerm::constant_i64(1).into());
                assert!(!known(
                    &equality(observed, wrong.clone()),
                    &self::bounds(&wrong, ty)
                ));
            }
        }
    }
    #[test]
    fn known_integer_casts_check_the_destination_and_exact_operand() {
        let _session = VerificationSession::enter();
        for ty in crate::kernel::machine_integer::FORMATS {
            let operand = IntegerTerm::var(Variable(995705));
            let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                ty,
                MachineTerm::IntegerToMachine {
                    value: operand.clone().into(),
                    destination: ty,
                },
            ));
            let goal = equality(observed.clone(), operand.clone());
            let bounds = bounds(&operand, ty);
            assert!(known(&goal, &bounds));
            assert!(!known(&goal, &bounds[..1]));
            assert!(!known(&goal, &bounds[1..]));
            let wrong = IntegerTerm::var(Variable(995706));
            assert!(!known(
                &equality(observed, wrong.clone()),
                &self::bounds(&wrong, ty)
            ));
        }
    }
    #[test]
    fn known_conditional_equations_require_the_chosen_guard() {
        let _session = VerificationSession::enter();
        let guard = ConditionTerm::Variable(Variable(995707));
        let a = IntegerTerm::var(Variable(995708));
        let b = IntegerTerm::var(Variable(995709));
        let value = IntegerTerm::If {
            condition: Box::new(guard.clone()),
            then_term: a.clone().into(),
            else_term: b.clone().into(),
        };
        for (truth, arm, wrong) in [(true, a.clone(), b.clone()), (false, b, a)] {
            let premise = Proposition::condition_is(guard.clone(), truth);
            assert!(known(
                &equality(value.clone(), arm.clone()),
                std::slice::from_ref(&premise)
            ));
            assert!(!known(&equality(value.clone(), wrong), &[premise]));
            assert!(!known(&equality(value.clone(), arm), &[]));
        }
    }
    #[test]
    fn known_identical_conditional_arms_do_constant_work() {
        let _session = VerificationSession::enter();
        let a = IntegerTerm::var(Variable(995708));
        let value = IntegerTerm::If {
            condition: Box::new(ConditionTerm::Variable(Variable(995707))),
            then_term: a.clone().into(),
            else_term: a.clone().into(),
        };
        let goal = equality(value, a.clone());
        let mut expected_work = None;
        for count in [0, 8, 128] {
            let facts = PureFactStore::from_ordered(
                &(0..count)
                    .flat_map(|index| {
                        let other = IntegerTerm::var(Variable(996000 + 2 * index));
                        let unrelated = IntegerTerm::var(Variable(996001 + 2 * index));
                        [
                            equality(a.clone(), other.clone()),
                            equality(other, unrelated),
                        ]
                    })
                    .collect::<Vec<_>>(),
            );
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|fact| facts.pure_known_available(fact))
            });
            assert!(proved);
            assert_eq!(work, *expected_work.get_or_insert(work));
        }
    }
    fn native_binary(ty: MachineIntegerType, op: MachineBinaryOp, count: i32) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            ty,
            MachineTerm::Binary {
                format: ty,
                op,
                left: Box::new(MachineTerm::Variable(Variable(995710))),
                right: Box::new(MachineTerm::constant(count as u32)),
            },
        ))
    }
    #[test]
    fn known_shift_and_mask_rules_keep_their_literal_and_sign_guards() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let source =
            IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(995710))).unwrap();
        for count in [0, 1, 2, 31] {
            let exact = IntegerTerm::Multiply(
                source.clone().into(),
                IntegerTerm::Constant(BigInt::from(1) << count).into(),
            );
            let shifted = native_binary(ty, MachineBinaryOp::ShiftLeft, count);
            let mut premises = bounds(&exact, ty).to_vec();
            assert!(!known(&equality(shifted.clone(), exact.clone()), &premises));
            premises.push(le(IntegerTerm::constant_i64(0), source.clone()));
            assert!(known(&equality(shifted, exact), &premises));
        }
        for count in [-1, 32, 33] {
            let exact =
                IntegerTerm::Multiply(source.clone().into(), IntegerTerm::constant_i64(4).into());
            let mut premises = bounds(&exact, ty).to_vec();
            premises.push(le(IntegerTerm::constant_i64(0), source.clone()));
            assert!(!known(
                &equality(native_binary(ty, MachineBinaryOp::ShiftLeft, count), exact),
                &premises
            ));
        }
        for mask in [0, 1, 255, i32::MAX] {
            let masked = native_binary(ty, MachineBinaryOp::BitwiseAnd, mask);
            assert!(known(
                &le(IntegerTerm::constant_i64(0), masked.clone()),
                &[]
            ));
            assert!(known(
                &le(masked.clone(), IntegerTerm::constant_i64(mask.into())),
                &[]
            ));
            let goal = le(masked, source.clone());
            assert!(!known(&goal, &[]));
            assert!(known(
                &goal,
                &[le(IntegerTerm::constant_i64(0), source.clone())]
            ));
        }
        assert!(!known(
            &le(
                IntegerTerm::constant_i64(0),
                native_binary(ty, MachineBinaryOp::BitwiseAnd, -1)
            ),
            &[]
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/proof/fact_reasoning/known_bridges.rs");
    }
}
