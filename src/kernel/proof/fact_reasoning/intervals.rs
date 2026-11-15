//! One-operation interval reduction from explicitly cited constant endpoints.
//! Children are opaque observations: this never reconstructs a nested interval.
use crate::kernel::*;
use num_traits::ToPrimitive;
use std::collections::HashMap;

type Bounds = (i128, i128);

fn parts(p: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm, bool)> {
    match p {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => {
            Some((a, b, false))
        }
        Proposition::ConditionIs(ConditionTerm::IntegerLessThan(a, b), true) => Some((a, b, true)),
        Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(a, b), true) => {
            Some((b, a, false))
        }
        Proposition::ConditionIs(ConditionTerm::IntegerGreaterThan(a, b), true) => {
            Some((b, a, true))
        }
        _ => None,
    }
}
fn readings(p: &Proposition) -> Vec<Proposition> {
    let mut result =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(p);
    result.push(p.clone());
    result
}
fn bounds(value: &SharedIntegerTerm, selected: &HashMap<u64, Bounds>) -> Option<Bounds> {
    if let Some(n) = value.as_const().and_then(ToPrimitive::to_i128) {
        return Some((n, n));
    }
    if let Some(range) = selected.get(&value.id()) {
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
    selected: &HashMap<u64, Bounds>,
) -> Option<Bounds> {
    bounds(&value.observe(ty)?.into(), selected)
}
fn operation(
    value: &SharedIntegerTerm,
    selected: &HashMap<u64, Bounds>,
    premises: &[Proposition],
) -> Option<Bounds> {
    let IntegerTerm::Machine(machine) = value.as_ref() else {
        return None;
    };
    let view = machine.operand_view();
    if let Some((_, source, destination, operand)) = view.cast() {
        let range = child(operand, source, selected)?;
        let (lo, hi) = destination.format().bounds();
        return (range.0 >= lo.to_i128()? && range.1 <= hi.to_i128()?).then_some(range);
    }
    if machine.ty() != MachineIntegerType::Int32 {
        return None;
    }
    let (ty, op, [a, b]) = view.binary()?;
    if ty != MachineIntegerType::Int32 {
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
    let mut selected = HashMap::<u64, Bounds>::new();
    for p in premises {
        for reading in readings(p) {
            crate::instrumentation::record_deterministic_work(1);
            let Some((a, b, strict)) = parts(&reading) else {
                continue;
            };
            let (term, bound, lower) = if let Some(n) = a.as_const().and_then(ToPrimitive::to_i128)
            {
                (b, n + i128::from(strict), true)
            } else if let Some(n) = b.as_const().and_then(ToPrimitive::to_i128) {
                (a, n - i128::from(strict), false)
            } else {
                continue;
            };
            let Some(intrinsic) = bounds(term, &HashMap::new()) else {
                continue;
            };
            let range = selected.entry(term.id()).or_insert(intrinsic);
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
    for reading in readings(goal) {
        let Some((a, b, strict)) = parts(&reading) else {
            continue;
        };
        // At most one written operation is reduced. A bound on its opaque
        // children must be cited; nested arithmetic requires another have.
        let left = operation(a, &selected, premises).or_else(|| bounds(a, &selected));
        let right = operation(b, &selected, premises).or_else(|| bounds(b, &selected));
        if let (Some((_, ah)), Some((bl, _))) = (left, right) {
            if if strict { ah < bl } else { ah <= bl } {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::{ProofFacts, fact_reasoning::normalize_using_conditions};
    fn literal(n: i64) -> SharedIntegerTerm {
        IntegerTerm::constant_i64(n).into()
    }
    fn le(a: SharedIntegerTerm, b: SharedIntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true)
    }
    fn observe(value: MachineTerm) -> SharedIntegerTerm {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .unwrap()
            .into()
    }
    fn inputs(op: MachineBinaryOp, constant: i32) -> (Proposition, Vec<Proposition>) {
        let x = MachineTerm::Variable(Variable(987_701));
        let observed = observe(x.clone());
        let operation = MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            op,
            x,
            MachineTerm::constant(constant as u32),
        );
        (
            le(observe(operation), literal(11)),
            vec![le(literal(0), observed.clone()), le(observed, literal(10))],
        )
    }
    #[test]
    fn interval_reduction_requires_the_selected_endpoints() {
        let (goal, bounds) = inputs(MachineBinaryOp::Add, 1);
        let facts = ProofFacts::from_ordered(&bounds);
        normalize_using_conditions(&goal, &bounds, &facts).unwrap();
        assert!(normalize_using_conditions(&goal, &bounds[..1], &facts).is_err());
        let wrong = le(literal(0), literal(1));
        assert!(normalize_using_conditions(&goal, &[wrong], &facts).is_err());
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
                normalize_using_conditions(&goal, &bounds, &ProofFacts::from_ordered(&bounds))
                    .is_err()
            );
        }
    }
    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/fact_reasoning/intervals/tests.rs");
    }
}
