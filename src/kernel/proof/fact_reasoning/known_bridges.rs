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
            // Integer operands export as shared observation handles.
            KernelTermNode::IntegerCompare { .. } => KernelTermExport::condition(root).ok(),
            // Other shared guards need their own explicit logical steps.
            _ => None,
        };
    }
    None
}

fn integer_arm(
    value: &IntegerTerm,
    other: &IntegerTerm,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    let (condition, arms) = match value {
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            return [(true, then_term), (false, else_term)]
                .into_iter()
                .any(|(truth, arm)| {
                    arm.as_ref() == other
                        && holds(
                            &Proposition::condition_is(condition.as_ref().clone(), truth),
                            available,
                        )
                });
        }
        IntegerTerm::Machine(machine) => {
            let Some((condition, arms)) = machine.operand_view().conditional_view() else {
                return false;
            };
            let Some(condition) = written_guard(condition) else {
                return false;
            };
            (condition, arms.map(|arm| arm.observe(machine.ty())))
        }
        _ => return false,
    };
    [(true, &arms[0]), (false, &arms[1])]
        .into_iter()
        .any(|(truth, arm)| {
            arm.as_ref() == Some(other)
                && holds(
                    &Proposition::condition_is(condition.clone(), truth),
                    available,
                )
        })
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
    if integer_arm(value, other, available) {
        return true;
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
            holds(&condition.truth_claim(polarity), available) && matches_arm(arm)
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

pub(crate) fn known_bridge_leaf(
    goal: &Proposition,
    available: &impl Fn(&Proposition) -> bool,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match goal {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            identity(a, b, available) || identity(b, a, available)
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerLessEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            mask_bound(a, b, available)
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
            algebraic_arm(a, b, available) || algebraic_arm(b, a, available)
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
