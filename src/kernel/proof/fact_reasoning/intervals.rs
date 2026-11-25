//! One-operation interval reduction from explicitly cited constant endpoints.
//! Children are opaque observations: this never reconstructs a nested interval.
use crate::kernel::*;
use num_traits::ToPrimitive;
use std::collections::HashMap;

type Bounds = (i128, i128);

fn parts(p: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm, bool)> {
    let (condition, expected) = p.condition_native()?;
    // Integer order is total. A negative C safety test is the opposite
    // directed bound, with the opposite strictness.
    match (condition, expected) {
        (ConditionTerm::IntegerLessEqual(a, b), true)
        | (ConditionTerm::IntegerGreaterThan(a, b), false) => Some((a, b, false)),
        (ConditionTerm::IntegerLessThan(a, b), true)
        | (ConditionTerm::IntegerGreaterEqual(a, b), false) => Some((a, b, true)),
        (ConditionTerm::IntegerGreaterEqual(a, b), true)
        | (ConditionTerm::IntegerLessThan(a, b), false) => Some((b, a, false)),
        (ConditionTerm::IntegerGreaterThan(a, b), true)
        | (ConditionTerm::IntegerLessEqual(a, b), false) => Some((b, a, true)),
        _ => None,
    }
}
fn readings(p: &Proposition) -> Vec<Proposition> {
    let mut result =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(p);
    result.push(p.clone());
    result
}
fn bounds(
    value: &SharedIntegerTerm,
    selected: &HashMap<SharedIntegerTerm, Bounds>,
) -> Option<Bounds> {
    if let Some(n) = value.as_const().and_then(ToPrimitive::to_i128) {
        return Some((n, n));
    }
    if let Some(range) = selected.get(value) {
        return Some(*range);
    }
    let IntegerTerm::Machine(machine) = value.as_ref() else {
        return None;
    };
    let (lo, hi) = machine.ty().format().bounds();
    Some((lo.to_i128()?, hi.to_i128()?))
}
fn child(
    value: MachineOperandView<'_>,
    ty: MachineIntegerType,
    selected: &HashMap<SharedIntegerTerm, Bounds>,
) -> Option<Bounds> {
    bounds(&value.observe(ty)?.into(), selected)
}
fn operation(
    value: &SharedIntegerTerm,
    selected: &HashMap<SharedIntegerTerm, Bounds>,
    premises: &[Proposition],
) -> Option<Bounds> {
    // Exact arithmetic over two bounded observations is the same local
    // endpoint calculation, without a machine-range intersection.
    match value.as_ref() {
        IntegerTerm::Add(a, b) => {
            let (al, ah) = bounds(a, selected)?;
            let (bl, bh) = bounds(b, selected)?;
            return Some((al.checked_add(bl)?, ah.checked_add(bh)?));
        }
        IntegerTerm::Subtract(a, b) => {
            let (al, ah) = bounds(a, selected)?;
            let (bl, bh) = bounds(b, selected)?;
            return Some((al.checked_sub(bh)?, ah.checked_sub(bl)?));
        }
        IntegerTerm::Multiply(a, b) => {
            let (al, ah) = bounds(a, selected)?;
            let (bl, bh) = bounds(b, selected)?;
            let corners = [
                al.checked_mul(bl)?,
                al.checked_mul(bh)?,
                ah.checked_mul(bl)?,
                ah.checked_mul(bh)?,
            ];
            return Some((*corners.iter().min()?, *corners.iter().max()?));
        }
        _ => {}
    }
    let IntegerTerm::Machine(machine) = value.as_ref() else {
        return None;
    };
    let mut view = machine.operand_view();
    while let Some((_, source, destination, operand)) = view.cast() {
        if source != destination || destination != machine.ty() {
            break;
        }
        view = operand;
    }

    if let Some((_, source, destination, operand)) = view.cast() {
        let range = child(operand, source, selected)?;
        let (lo, hi) = destination.format().bounds();
        return (range.0 >= lo.to_i128()? && range.1 <= hi.to_i128()?).then_some(range);
    }
    if machine.ty() != MachineIntegerType::Int32 {
        return None;
    }
    let (ty, op, [a, b]) = view.binary()?;
    if !matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32) {
        return None;
    }
    let (al, ah) = child(a, ty, selected)?;
    let (bl, bh) = child(b, ty, selected)?;
    use MachineBinaryOp::*;
    let mut result = match op {
        Add => (al.checked_add(bl)?, ah.checked_add(bh)?),
        Subtract => (al.checked_sub(bh)?, ah.checked_sub(bl)?),
        Multiply => {
            let values = [
                al.checked_mul(bl)?,
                al.checked_mul(bh)?,
                ah.checked_mul(bl)?,
                ah.checked_mul(bh)?,
            ];
            (*values.iter().min()?, *values.iter().max()?)
        }
        Remainder
            if bl == bh
                && bl > 0
                && a.binary()
                    .is_some_and(|(format, op, _)| format == ty && op == Add) =>
        {
            let (_, _, [base, offset]) = a.binary()?;
            let (offset_lo, offset_hi) = child(offset, ty, selected)?;
            if offset_lo != offset_hi {
                return None;
            }
            let (base_lo, base_hi) = child(base, ty, selected)?;
            if base_lo < 0 || base_lo + offset_lo < 0 || base_hi + offset_lo > i128::from(i32::MAX)
            {
                return None;
            }
            let root = KernelTerm::machine_binary_shared(
                ty,
                Remainder,
                [
                    KernelTerm::retained_machine_operand(ty, base),
                    KernelTerm::retained_machine_operand(ty, b),
                ],
            );
            let original: SharedIntegerTerm =
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root)?).into();
            // This is the stated original remainder, not a recursively
            // inferred interval or a scan for a matching expression.
            let &(lo, hi) = selected.get(&original)?;
            if lo < 0 || hi >= bl {
                return None;
            }
            let (lo, hi) = (lo + offset_lo, hi + offset_lo);
            if lo.div_euclid(bl) != hi.div_euclid(bl) {
                return None;
            }
            (lo.rem_euclid(bl), hi.rem_euclid(bl))
        }
        Remainder if bl == bh && bl != 0 => {
            if bl == -1 && al == i128::from(i32::MIN) {
                return None;
            }
            let n = bl.abs() - 1;
            (if al >= 0 { 0 } else { -n }, if ah < 0 { 0 } else { n })
        }
        ShiftLeft if bl == bh && (0..32).contains(&bl) && al >= 0 => {
            (al.checked_shl(bl as u32)?, ah.checked_shl(bl as u32)?)
        }
        ShiftRight if bl == bh && (0..32).contains(&bl) => (al >> bl, ah >> bl),
        BitwiseAnd if bl == bh && bl >= 0 => (0, if al >= 0 { ah.min(bl) } else { bl }),
        _ => return None,
    };
    let minimum = i128::from(i32::MIN);
    let maximum = i128::from(i32::MAX);
    if result.0 < minimum || result.1 > maximum {
        // A stated guard permits intersecting the mathematical endpoints
        // with the signed range, never inferring definedness from a result.
        let (operation, operands) =
            crate::kernel::machine_integer::representation::view_operation(ty, view)?;
        let query = crate::kernel::machine_integer::definedness::OverflowQueryView::from_operands(
            ty, operation, operands,
        )?;
        let defined = premises.iter().any(|p| {
            crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(p)
                .is_some_and(|guard| {
                    guard.format == query.format
                        && guard.operation == query.operation
                        && guard
                            .operands
                            .iter()
                            .zip(query.operands.iter())
                            .all(|(a, b)| {
                                a.operand_view().retain(ty) == b.operand_view().retain(ty)
                            })
                })
        });
        if !defined {
            return None;
        }
        result = (result.0.max(minimum), result.1.min(maximum));
    }
    (result.0 <= result.1).then_some(result)
}

pub(super) fn reduces_one_operation(goal: &Proposition, premises: &[Proposition]) -> bool {
    let goals = match goal {
        Proposition::And(left, right) => {
            // A single explicit endpoint pair shares one selected-bound index.
            // Nested conjunctions still require separate ordinary proof steps.
            if matches!(left.as_ref(), Proposition::And(..))
                || matches!(right.as_ref(), Proposition::And(..))
            {
                return false;
            }
            vec![left.as_ref(), right.as_ref()]
        }
        _ => vec![goal],
    };
    let mut comparisons = Vec::with_capacity(goals.len());
    for goal in goals {
        if parts(goal).is_none() {
            let Proposition::ConditionIs(condition, truth) = goal else {
                return false;
            };
            if !crate::kernel::machine_integer::comparison::comparison_view(
                condition.old_form(),
                *truth,
            )
            .is_some_and(|view| {
                matches!(
                    view.relation,
                    crate::kernel::machine_integer::Relation::Less
                        | crate::kernel::machine_integer::Relation::LessEqual
                )
            }) {
                return false;
            }
        }
        let goal_readings = readings(goal);
        if !goal_readings.iter().any(|reading| parts(reading).is_some()) {
            return false;
        }
        comparisons.push(goal_readings);
    }
    let mut selected = HashMap::<SharedIntegerTerm, Bounds>::new();
    for p in premises {
        for reading in readings(p) {
            crate::instrumentation::record_deterministic_work(1);
            let Some((a, b, strict)) = parts(&reading) else {
                continue;
            };
            let (term, bound, lower) = if let Some(n) = a.as_const().and_then(ToPrimitive::to_i128)
            {
                let Some(bound) = n.checked_add(i128::from(strict)) else {
                    continue;
                };
                (b, bound, true)
            } else if let Some(n) = b.as_const().and_then(ToPrimitive::to_i128) {
                let Some(bound) = n.checked_sub(i128::from(strict)) else {
                    continue;
                };
                (a, bound, false)
            } else {
                continue;
            };
            let Some(intrinsic) = bounds(term, &HashMap::new()) else {
                continue;
            };
            let range = selected.entry(term.clone()).or_insert(intrinsic);
            if lower {
                range.0 = range.0.max(bound);
            } else {
                range.1 = range.1.min(bound);
            }
            if range.0 > range.1 {
                return false;
            }
        }
    }
    comparisons.iter().all(|goal_readings| {
        goal_readings.iter().any(|reading| {
            let Some((a, b, strict)) = parts(reading) else {
                return false;
            };
            // At most one operation per written endpoint. Children are opaque.
            let left = operation(a, &selected, premises).or_else(|| bounds(a, &selected));
            let right = operation(b, &selected, premises).or_else(|| bounds(b, &selected));
            match (left, right) {
                (Some((_, ah)), Some((bl, _))) => {
                    if strict {
                        ah < bl
                    } else {
                        ah <= bl
                    }
                }
                _ => false,
            }
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::{PureFactStore, fact_reasoning::normalize_using_conditions};
    fn literal(n: i64) -> SharedIntegerTerm {
        IntegerTerm::constant_i64(n).into()
    }
    fn le(a: SharedIntegerTerm, b: SharedIntegerTerm) -> Proposition {
        Proposition::condition_is(ConditionTerm::IntegerLessEqual(a, b), true)
    }
    fn observe(value: OldMachineTerm) -> SharedIntegerTerm {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .unwrap()
            .into()
    }
    fn inputs(op: MachineBinaryOp, constant: i32) -> (Proposition, Vec<Proposition>) {
        let x = OldMachineTerm::Variable(Variable(987_701));
        let observed = observe(x.clone());
        let operation = OldMachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            op,
            x,
            OldMachineTerm::constant(constant as u32),
        );
        (
            le(observe(operation), literal(11)),
            vec![le(literal(0), observed.clone()), le(observed, literal(10))],
        )
    }
    #[test]
    fn interval_reduction_requires_the_selected_endpoints() {
        let (goal, bounds) = inputs(MachineBinaryOp::Add, 1);
        let facts = PureFactStore::from_ordered(&bounds);
        normalize_using_conditions(&goal, &bounds, &facts).unwrap();
        assert!(normalize_using_conditions(&goal, &bounds[..1], &facts).is_err());
        let wrong = le(literal(0), literal(1));
        assert!(normalize_using_conditions(&goal, &[wrong], &facts).is_err());
    }
    #[test]
    fn signed_observations_do_not_clip_with_an_unsigned_guard() {
        let x = OldMachineTerm::Variable(Variable(987_777));
        let root = OldMachineTerm::logical_machine_binary(
            MachineIntegerType::UInt32,
            MachineBinaryOp::Add,
            x.clone(),
            OldMachineTerm::constant(1),
        );
        let unsigned: SharedIntegerTerm = IntegerTerm::from_machine(MachineIntegerType::UInt32, x)
            .unwrap()
            .into();
        let exact: SharedIntegerTerm = IntegerTerm::Add(unsigned.clone(), literal(1)).into();
        let guard = Proposition::And(
            Box::new(le(literal(0), exact.clone())),
            Box::new(le(exact, literal(i64::from(u32::MAX)))),
        );
        let selected = vec![
            le(literal(0), unsigned.clone()),
            le(unsigned, literal(i64::from(u32::MAX) - 1)),
            guard,
        ];
        let goal = le(literal(0), observe(root));
        assert!(
            normalize_using_conditions(&goal, &selected, &PureFactStore::from_ordered(&selected))
                .is_err()
        );
    }
    #[test]
    fn extreme_strict_endpoints_refuse_without_panicking() {
        let (goal, _) = inputs(MachineBinaryOp::Add, 1);
        let x = observe(OldMachineTerm::Variable(Variable(987_701)));
        for (value, lower) in [(i128::MAX, true), (i128::MIN, false)] {
            let endpoint: SharedIntegerTerm = IntegerTerm::Constant(value.into()).into();
            let (a, b) = if lower {
                (endpoint, x.clone())
            } else {
                (x.clone(), endpoint)
            };
            let premise = Proposition::condition_is(ConditionTerm::IntegerLessThan(a, b), true);
            assert!(!reduces_one_operation(&goal, &[premise]));
        }
    }
    #[test]
    fn interval_reduction_refuses_overflow_and_invalid_shifts() {
        for (op, n) in [
            (MachineBinaryOp::Add, i32::MAX),
            (MachineBinaryOp::ShiftLeft, 32),
            (MachineBinaryOp::ShiftLeft, -1),
            (MachineBinaryOp::Remainder, 0),
        ] {
            let (goal, bounds) = inputs(op, n);
            assert!(
                normalize_using_conditions(&goal, &bounds, &PureFactStore::from_ordered(&bounds))
                    .is_err()
            );
        }
    }
    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/fact_reasoning/intervals/tests.rs");
    }
}
