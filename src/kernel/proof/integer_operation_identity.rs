//! A machine addition or subtraction whose mathematical result lies inside
//! its type's range is that mathematical result. The certificate names
//! exactly two bounds on the mathematical result.

use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition, SharedIntegerTerm,
};

fn order(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => Some((a, b)),
        _ => None,
    }
}

/// The mathematical value of the machine operation that `observed` reads,
/// spelled over the operands' own observations in the operation's type.
/// `to_integer(observed) == value` is the identity this rule proves once
/// `value` is bounded inside the type.
pub(crate) fn mathematical(observed: &IntegerTerm) -> Option<(MachineIntegerType, IntegerTerm)> {
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    let ty = machine.ty();
    let (left, right, subtract) = match (ty, machine.value()) {
        (
            MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            Bitvector32Term::Add(left, right),
        )
        | (MachineIntegerType::Int64, Bitvector32Term::Int64Add(left, right))
        | (MachineIntegerType::UInt64, Bitvector32Term::UInt64Add(left, right)) => {
            (left, right, false)
        }
        (
            MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            Bitvector32Term::Subtract(left, right),
        )
        | (MachineIntegerType::Int64, Bitvector32Term::Int64Subtract(left, right))
        | (MachineIntegerType::UInt64, Bitvector32Term::UInt64Subtract(left, right)) => {
            (left, right, true)
        }
        _ => return None,
    };
    let left = IntegerTerm::from_machine(ty, left.as_ref().clone())?;
    let right = IntegerTerm::from_machine(ty, right.as_ref().clone())?;
    let value = if subtract {
        IntegerTerm::subtract(left, right)
    } else {
        IntegerTerm::add(left, right)
    };
    Some((ty, value))
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerOperationIdentity(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 2 {
        return Err(invalid());
    }
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = result else {
        return Err(invalid());
    };
    let (ty, value, stated) = if let Some((ty, value)) = mathematical(a) {
        (ty, value, b)
    } else if let Some((ty, value)) = mathematical(b) {
        (ty, value, a)
    } else {
        return Err(invalid());
    };
    if stated.as_ref() != &value {
        return Err(invalid());
    }
    let lower = premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?;
    let upper = premises
        .get(bounds[1])
        .ok_or(Error::InvalidPremise(bounds[1]))?;
    let (lo, operand) = order(lower).ok_or_else(invalid)?;
    let (other_operand, hi) = order(upper).ok_or_else(invalid)?;
    if operand != stated || other_operand != stated {
        return Err(invalid());
    }
    let (lo, hi) = lo.as_const().zip(hi.as_const()).ok_or_else(invalid)?;
    // Endpoints supplied by the certificate may have arbitrary bit length.
    let work = usize::try_from(lo.bits())
        .unwrap_or(usize::MAX)
        .saturating_add(usize::try_from(hi.bits()).unwrap_or(usize::MAX))
        .saturating_add(512);
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(Error::WorkLimitExceeded);
    }
    let (min, max) = ty.format().bounds();
    if lo > hi || lo < &min || hi > &max {
        return Err(invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    use MachineIntegerType as Ty;
    use num_bigint::BigInt;

    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(a, b), true)
    }
    fn equal(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_equal(a, b), true)
    }
    fn certificate(result: Proposition, bounds: Vec<usize>) -> SpecialArithmeticCertificate {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerOperationIdentity { bounds, result }],
            conclusion: 0,
        }
    }
    fn operation(
        ty: Ty,
        subtract: bool,
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Bitvector32Term {
        let (left, right) = (Box::new(left), Box::new(right));
        match (ty, subtract) {
            (Ty::Int32 | Ty::UInt32, false) => Bitvector32Term::Add(left, right),
            (Ty::Int32 | Ty::UInt32, true) => Bitvector32Term::Subtract(left, right),
            (Ty::Int64, false) => Bitvector32Term::Int64Add(left, right),
            (Ty::Int64, true) => Bitvector32Term::Int64Subtract(left, right),
            (Ty::UInt64, false) => Bitvector32Term::UInt64Add(left, right),
            (Ty::UInt64, true) => Bitvector32Term::UInt64Subtract(left, right),
            _ => unreachable!(),
        }
    }
    /// Premises bounding the mathematical result by `[lo, hi]`, and the
    /// identity `to_integer(a op b) == to_integer(a) op to_integer(b)`.
    fn inputs(
        ty: Ty,
        subtract: bool,
        lo: BigInt,
        hi: BigInt,
    ) -> (Vec<Proposition>, Proposition, IntegerTerm) {
        let left = Bitvector32Term::Variable(Variable(171_001));
        let right = Bitvector32Term::Variable(Variable(171_002));
        let observe =
            |value: &Bitvector32Term| IntegerTerm::from_machine(ty, value.clone()).unwrap();
        let value = if subtract {
            IntegerTerm::subtract(observe(&left), observe(&right))
        } else {
            IntegerTerm::add(observe(&left), observe(&right))
        };
        let observed =
            IntegerTerm::from_machine(ty, operation(ty, subtract, left.clone(), right.clone()))
                .unwrap();
        (
            vec![
                le(IntegerTerm::constant(lo), value.clone()),
                le(value.clone(), IntegerTerm::constant(hi)),
            ],
            equal(observed, value.clone()),
            value,
        )
    }

    #[test]
    fn integer_operation_identity_accepts_in_range_results_in_either_orientation() {
        for ty in [Ty::Int32, Ty::UInt32, Ty::Int64, Ty::UInt64] {
            let (min, max) = ty.format().bounds();
            for subtract in [false, true] {
                let (premises, goal, _) = inputs(ty, subtract, min.clone(), max.clone());
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &premises)
                        .is_ok()
                );
                let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = &goal
                else {
                    unreachable!()
                };
                let flipped = equal(b.as_ref().clone(), a.as_ref().clone());
                assert!(
                    certificate(flipped.clone(), vec![0, 1])
                        .check(&flipped, &premises)
                        .is_ok()
                );
                let (narrow, goal, _) = inputs(ty, subtract, 0.into(), 7.into());
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &narrow)
                        .is_ok()
                );
            }
        }
    }

    #[test]
    fn integer_operation_identity_refuses_missing_wrong_and_out_of_range_bounds() {
        for ty in [Ty::Int32, Ty::UInt32, Ty::Int64, Ty::UInt64] {
            let (min, max) = ty.format().bounds();
            let (premises, goal, value) = inputs(ty, true, min.clone(), max.clone());
            for bounds in [
                vec![],
                vec![0],
                vec![1, 0],
                vec![0, 0],
                vec![0, 1, 1],
                vec![0, 2],
            ] {
                assert!(
                    certificate(goal.clone(), bounds)
                        .check(&goal, &premises)
                        .is_err()
                );
            }
            for altered in [
                vec![
                    le(IntegerTerm::constant(min.clone() - 1), value.clone()),
                    premises[1].clone(),
                ],
                vec![
                    premises[0].clone(),
                    le(value.clone(), IntegerTerm::constant(max.clone() + 1)),
                ],
                vec![
                    le(IntegerTerm::constant(5.into()), value.clone()),
                    le(value.clone(), IntegerTerm::constant(4.into())),
                ],
                vec![
                    le(
                        IntegerTerm::constant(min.clone()),
                        IntegerTerm::var(Variable(171_003)),
                    ),
                    premises[1].clone(),
                ],
                vec![
                    Proposition::ConditionIs(
                        ConditionTerm::integer_less_equal(
                            IntegerTerm::constant(min.clone()),
                            value.clone(),
                        ),
                        false,
                    ),
                    premises[1].clone(),
                ],
            ] {
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &altered)
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn integer_operation_identity_refuses_mismatched_operations_types_and_polarity() {
        let left = Bitvector32Term::Variable(Variable(171_001));
        let right = Bitvector32Term::Variable(Variable(171_002));
        let (premises, goal, value) = inputs(
            Ty::Int32,
            false,
            Ty::Int32.format().bounds().0,
            Ty::Int32.format().bounds().1,
        );
        // The stated value must be the operation's own: a sum is not a difference.
        let difference = IntegerTerm::subtract(
            IntegerTerm::from_machine(Ty::Int32, left.clone()).unwrap(),
            IntegerTerm::from_machine(Ty::Int32, right.clone()).unwrap(),
        );
        let observed = IntegerTerm::from_machine(
            Ty::Int32,
            operation(Ty::Int32, false, left.clone(), right.clone()),
        )
        .unwrap();
        let wrong = equal(observed.clone(), difference);
        assert!(
            certificate(wrong.clone(), vec![0, 1])
                .check(&wrong, &premises)
                .is_err()
        );
        // An operation in another type does not match the stated width.
        for (ty, other) in [
            (Ty::Int64, Ty::Int32),
            (Ty::UInt32, Ty::Int64),
            (Ty::UInt64, Ty::Int64),
        ] {
            let Some(observed) =
                IntegerTerm::from_machine(ty, operation(other, false, left.clone(), right.clone()))
            else {
                continue;
            };
            let forged = equal(observed, value.clone());
            assert!(
                certificate(forged.clone(), vec![0, 1])
                    .check(&forged, &premises)
                    .is_err()
            );
        }
        // Unsigned bounds do not license a signed identity's wider range.
        let (unsigned, _, _) = inputs(Ty::UInt32, false, 0.into(), Ty::UInt32.format().bounds().1);
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &unsigned)
                .is_err()
        );
        // A multiplication is not an addition.
        let product = IntegerTerm::from_machine(
            Ty::Int32,
            Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
        )
        .unwrap();
        let forged = equal(product, value);
        assert!(
            certificate(forged.clone(), vec![0, 1])
                .check(&forged, &premises)
                .is_err()
        );
        let Proposition::ConditionIs(condition, true) = goal.clone() else {
            unreachable!()
        };
        let negated = Proposition::ConditionIs(condition, false);
        assert!(
            certificate(negated.clone(), vec![0, 1])
                .check(&negated, &premises)
                .is_err()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/integer_operation_identity/tests.rs");
    }
}
