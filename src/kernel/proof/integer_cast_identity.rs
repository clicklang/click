//! A modulo integral cast preserves its mathematical value inside the
//! destination range. The certificate names exactly two source bounds.

use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};

fn order(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => Some((a, b)),
        _ => None,
    }
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerCastIdentity(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 2 {
        return Err(invalid());
    }
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = result else {
        return Err(invalid());
    };
    let cast = |observed: &IntegerTerm, original: &IntegerTerm| {
        let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) = (observed, original)
        else {
            return None;
        };
        if !operand.ty().accepts_cast_operand(operand.value()) {
            return None;
        }
        // Compare with the canonical conversion of the *observed* source.
        // A narrowing cast can discard an intermediate widening/reinterpretation
        // node, so inspecting only the outer node loses the source named by the
        // certificate. The canonical cast still has exactly its modulo semantics;
        // the bounds below establish that this conversion preserves the value.
        let converted = Bitvector32Term::machine_integer_cast(
            operand.ty(),
            machine.ty(),
            operand.value().clone(),
        );
        if machine.value() == &converted {
            return Some(machine.ty().format());
        }
        // Typed byte stores/readback represent unsigned sub-word values by
        // retaining their low bits. This is the same modulo conversion from a
        // u32 word, with the source bounds still required below.
        if operand.ty() == crate::kernel::MachineIntegerType::UInt32
            && matches!(
                machine.ty(),
                crate::kernel::MachineIntegerType::UInt8
                    | crate::kernel::MachineIntegerType::UInt16
            )
            && let Bitvector32Term::BitwiseAnd(left, right) = machine.value()
        {
            let mask = (1u32 << machine.ty().format().bits()) - 1;
            let matches = |value: &Bitvector32Term, bits: &Bitvector32Term| {
                value == operand.value() && bits == &Bitvector32Term::Constant(mask)
            };
            if matches(left, right) || matches(right, left) {
                return Some(machine.ty().format());
            }
        }
        None
    };
    let (original, destination) = if let Some(destination) = cast(a, b) {
        (b, destination)
    } else if let Some(destination) = cast(b, a) {
        (a, destination)
    } else {
        return Err(invalid());
    };
    let lower = premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?;
    let upper = premises
        .get(bounds[1])
        .ok_or(Error::InvalidPremise(bounds[1]))?;
    let (lo, operand) = order(lower).ok_or_else(invalid)?;
    let (other_operand, hi) = order(upper).ok_or_else(invalid)?;
    if operand != original || other_operand != original {
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
    let (min, max) = destination.bounds();
    if lo > hi || lo < &min || hi > &max {
        return Err(invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    use crate::kernel::{MachineIntegerConstant, MachineIntegerType as Ty, Variable};
    use num_bigint::BigInt;

    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(a, b), true)
    }
    fn inputs(source: Ty, destination: Ty) -> (Vec<Proposition>, Proposition) {
        let value = Bitvector32Term::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(source, value.clone()).unwrap();
        let cast = Bitvector32Term::machine_integer_cast(source, destination, value);
        let observed = IntegerTerm::from_machine(destination, cast).unwrap();
        let (lo, hi) = destination.format().bounds();
        (
            vec![
                le(IntegerTerm::constant(lo), original.clone()),
                le(original.clone(), IntegerTerm::constant(hi)),
            ],
            Proposition::ConditionIs(ConditionTerm::integer_equal(observed, original), true),
        )
    }
    fn certificate(result: Proposition, bounds: Vec<usize>) -> SpecialArithmeticCertificate {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerCastIdentity { bounds, result }],
            conclusion: 0,
        }
    }

    #[test]
    fn integer_cast_identity_matches_exact_modulo_oracle_at_destination_boundaries() {
        for source in [Ty::Int128, Ty::UInt128] {
            for destination in [
                Ty::Int8,
                Ty::UInt8,
                Ty::Int16,
                Ty::UInt16,
                Ty::Int32,
                Ty::UInt32,
                Ty::Int64,
                Ty::UInt64,
            ] {
                let (premises, goal) = inputs(source, destination);
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &premises)
                        .is_ok()
                );
                let (min, max) = destination.format().bounds();
                for number in [
                    min.clone() - 1,
                    min.clone(),
                    BigInt::from(0),
                    max.clone(),
                    max.clone() + 1,
                ] {
                    let Some(value) =
                        MachineIntegerConstant::from_integer(source.format(), &number)
                    else {
                        continue;
                    };
                    let bits = BigInt::from(1u8) << destination.format().bits();
                    let mut expected = ((&number % &bits) + &bits) % &bits;
                    if destination.format().is_signed() && expected > max {
                        expected -= bits;
                    }
                    assert_eq!(
                        value.convert_modulo(destination.format()).to_integer(),
                        expected
                    );
                    assert_eq!(expected == number, min <= number && number <= max);
                }
                let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = &goal
                else {
                    unreachable!()
                };
                let reversed = Proposition::ConditionIs(
                    ConditionTerm::integer_equal(b.as_ref().clone(), a.as_ref().clone()),
                    true,
                );
                assert!(
                    certificate(reversed.clone(), vec![0, 1])
                        .check(&reversed, &premises)
                        .is_ok()
                );
            }
        }
    }

    #[test]
    fn integer_cast_identity_checks_normalized_nested_conversions() {
        let variable = Bitvector32Term::Variable(Variable(168_001));
        for (source, intermediate, destination) in [
            (Ty::Int32, Ty::UInt32, Ty::UInt16),
            (Ty::UInt32, Ty::Int32, Ty::UInt16),
            (Ty::UInt8, Ty::UInt32, Ty::UInt16),
            (Ty::Int128, Ty::UInt64, Ty::Int32),
        ] {
            let widened =
                Bitvector32Term::machine_integer_cast(source, intermediate, variable.clone());
            let narrowed =
                Bitvector32Term::machine_integer_cast(intermediate, destination, widened.clone());
            let original = IntegerTerm::from_machine(intermediate, widened).unwrap();
            let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(observed.clone(), original.clone()),
                true,
            );
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(255.into())),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_ok()
            );
            let wrong_source = vec![
                le(
                    IntegerTerm::constant(0.into()),
                    IntegerTerm::var(Variable(168_002)),
                ),
                premises[1].clone(),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &wrong_source)
                    .is_err()
            );
            // The bounds must describe the source observation in the equality,
            // even when the constructor has removed that intermediate cast.
            let underlying = IntegerTerm::from_machine(source, variable.clone()).unwrap();
            if underlying == original {
                continue;
            }
            let wrong_goal =
                Proposition::ConditionIs(ConditionTerm::integer_equal(observed, underlying), true);
            assert!(
                certificate(wrong_goal.clone(), vec![0, 1])
                    .check(&wrong_goal, &premises)
                    .is_err()
            );
        }

        // Widening after a truncation cannot be treated as a direct cast of the
        // pre-truncation value, even if that value fits the final destination.
        let truncated =
            Bitvector32Term::machine_integer_cast(Ty::UInt32, Ty::UInt8, variable.clone());
        let widened = Bitvector32Term::machine_integer_cast(Ty::UInt8, Ty::UInt16, truncated);
        let original = IntegerTerm::from_machine(Ty::UInt32, variable).unwrap();
        let observed = IntegerTerm::from_machine(Ty::UInt16, widened).unwrap();
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(observed, original.clone()),
            true,
        );
        let premises = vec![
            le(IntegerTerm::constant(0.into()), original.clone()),
            le(original, IntegerTerm::constant(65535.into())),
        ];
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn integer_cast_identity_checks_unsigned_byte_readback_masks() {
        let value = Bitvector32Term::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(Ty::UInt32, value.clone()).unwrap();
        for destination in [Ty::UInt8, Ty::UInt16] {
            let mask = (1u32 << destination.format().bits()) - 1;
            let goal_with_mask = |mask| {
                let narrowed = Bitvector32Term::BitwiseAnd(
                    Box::new(value.clone()),
                    Box::new(Bitvector32Term::Constant(mask)),
                );
                let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
                Proposition::ConditionIs(
                    ConditionTerm::integer_equal(observed, original.clone()),
                    true,
                )
            };
            let goal = goal_with_mask(mask);
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(mask.into())),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_ok()
            );
            for incorrect in [mask - 1, mask + 1, 0, u32::MAX] {
                let wrong = goal_with_mask(incorrect);
                assert!(
                    certificate(wrong.clone(), vec![0, 1])
                        .check(&wrong, &premises)
                        .is_err()
                );
            }
            let outside = vec![
                premises[0].clone(),
                le(
                    original.clone(),
                    IntegerTerm::constant((u64::from(mask) + 1).into()),
                ),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &outside)
                    .is_err()
            );
            let wrong_source = vec![
                premises[0].clone(),
                le(
                    IntegerTerm::var(Variable(168_002)),
                    IntegerTerm::constant(mask.into()),
                ),
            ];
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &wrong_source)
                    .is_err()
            );
            for number in [0, 1, mask - 1, mask, mask + 1, i32::MAX as u32, u32::MAX] {
                let converted = match destination {
                    Ty::UInt8 => u32::from(number as u8),
                    Ty::UInt16 => u32::from(number as u16),
                    _ => unreachable!(),
                };
                assert_eq!(converted, number & mask);
                assert_eq!(converted == number, number <= mask);
            }
        }
    }

    #[test]
    fn integer_cast_identity_refuses_missing_wrong_and_out_of_range_bounds() {
        let (premises, goal) = inputs(Ty::Int128, Ty::Int64);
        for bounds in [
            vec![],
            vec![0],
            vec![1],
            vec![0, 0],
            vec![1, 0],
            vec![0, 1, 1],
            vec![0, 2],
        ] {
            assert!(
                certificate(goal.clone(), bounds)
                    .check(&goal, &premises)
                    .is_err()
            );
        }
        let original =
            IntegerTerm::from_machine(Ty::Int128, Bitvector32Term::Variable(Variable(168_001)))
                .unwrap();
        let (lo, hi) = Ty::Int64.format().bounds();
        for altered in [
            vec![
                le(IntegerTerm::constant(lo.clone() - 1), original.clone()),
                premises[1].clone(),
            ],
            vec![
                premises[0].clone(),
                le(original.clone(), IntegerTerm::constant(hi.clone() + 1)),
            ],
            vec![
                le(IntegerTerm::constant(5.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(4.into())),
            ],
            vec![
                le(
                    IntegerTerm::constant(lo.clone()),
                    IntegerTerm::var(Variable(168_002)),
                ),
                premises[1].clone(),
            ],
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(IntegerTerm::constant(lo), original.clone()),
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
        let stronger = vec![
            le(IntegerTerm::constant((-3).into()), original.clone()),
            le(original, IntegerTerm::constant(4.into())),
        ];
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&goal, &stronger)
                .is_ok()
        );
        let (_, other_goal) = inputs(Ty::UInt128, Ty::Int64);
        assert!(
            certificate(goal.clone(), vec![0, 1])
                .check(&other_goal, &premises)
                .is_err()
        );
        assert!(
            certificate(other_goal.clone(), vec![0, 1])
                .check(&other_goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn integer_cast_identity_rejects_forged_format_payload_and_goal_polarity() {
        use crate::kernel::SharedMachineIntegerTerm;
        let (premises, _) = inputs(Ty::Int128, Ty::Int64);
        let original =
            IntegerTerm::from_machine(Ty::Int128, Bitvector32Term::Variable(Variable(168_001)))
                .unwrap();
        for (ty, source, destination, value) in [
            (
                Ty::Int32,
                Ty::Int128,
                Ty::Int64,
                Bitvector32Term::Variable(Variable(168_001)),
            ),
            (
                Ty::Int64,
                Ty::Int128,
                Ty::Int64,
                Bitvector32Term::Constant(1),
            ),
            (
                Ty::Int64,
                Ty::UInt128,
                Ty::Int64,
                Ty::Int128
                    .constant_term(
                        MachineIntegerConstant::from_integer(Ty::Int128.format(), &1.into())
                            .unwrap(),
                    )
                    .unwrap(),
            ),
        ] {
            let cast = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                ty,
                Bitvector32Term::MachineIntegerCast {
                    source,
                    destination,
                    value: Box::new(value),
                },
            ));
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(cast, original.clone()),
                true,
            );
            assert!(
                certificate(goal.clone(), vec![0, 1])
                    .check(&goal, &premises)
                    .is_err()
            );
        }
        let (_, goal) = inputs(Ty::Int128, Ty::Int64);
        let Proposition::ConditionIs(condition, _) = goal else {
            unreachable!()
        };
        let false_goal = Proposition::ConditionIs(condition, false);
        assert!(
            certificate(false_goal.clone(), vec![0, 1])
                .check(&false_goal, &premises)
                .is_err()
        );
    }

    #[test]
    fn integer_cast_identity_checks_only_explicit_premises_and_scales_with_nodes() {
        let (mut premises, goal) = inputs(Ty::Int128, Ty::Int64);
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            premises.resize_with(size, || {
                Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_003)), true)
            });
            let cert = certificate(goal.clone(), vec![0, 1]);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
            "{samples:?}"
        );
        let mut previous = None;
        for size in [2usize, 8, 32, 128] {
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerCastIdentity {
                        bounds: vec![0, 1],
                        result: goal.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            assert!(work <= 4096 * size, "{size}: {work}");
            if let Some(before) = previous {
                assert!(work <= 4 * before + 64);
            }
            previous = Some(work);
        }
    }
}
