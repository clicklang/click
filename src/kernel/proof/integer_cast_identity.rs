//! A modulo integral cast preserves its mathematical value inside the
//! destination range, and so does the Integer-to-machine conversion
//! `to_T(z)`: `to_integer(to_T(z)) == z` when `z` lies in `T`
//! (`conversion::integer_conversion`). The certificate names exactly two
//! source bounds.

use super::arithmetic_special::ArithmeticRuleError as Error;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::machine_integer::conversion::{cast, integer_conversion};
use crate::kernel::{ConditionTerm, Proposition, SharedIntegerTerm};

fn order(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerLessEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    // A read of a cell holding the cast is that cast (the read-over-write
    // authority), so the identity also sees the cast a store wrote.
    check_as_written(node, bounds, premises, result).or_else(|error| {
        match crate::kernel::comparison_form(result) {
            Some(resolved) => check_as_written(node, bounds, premises, &resolved),
            None => Err(error),
        }
    })
}

fn check_as_written(
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
    let Some((ConditionTerm::IntegerEqual(a, b), true)) = result.condition_native() else {
        return Err(invalid());
    };
    // Two observations with one value reading (rule W: a widening's value
    // is its operand's) are the identity itself; its bounds are still
    // checked, at the format of that reading. A typed 32-to-64-bit
    // extension node, the conversion C lowering writes, keeps the range of
    // its destination, as for any other conversion as written. One match on
    // each root.
    let (original, destination) = if a.value_read() == b.value_read() {
        let crate::kernel::IntegerTerm::Machine(machine) = a.value_read() else {
            return Err(invalid());
        };
        let extension = |term: &SharedIntegerTerm| match term.as_ref() {
            crate::kernel::IntegerTerm::Machine(written) => written
                .operand_view()
                .cast()
                .filter(|(encoding, source, destination, _)| {
                    crate::kernel::machine_integer::conversion::reads_as_operand(
                        *encoding,
                        *source,
                        *destination,
                    )
                })
                .map(|(_, _, destination, _)| destination.format()),
            _ => None,
        };
        let destination = extension(a)
            .or_else(|| extension(b))
            .unwrap_or(machine.ty().format());
        (a, destination)
    } else if let Some(destination) = cast(a, b) {
        (b, destination)
    } else if let Some(destination) = cast(b, a) {
        (a, destination)
    } else if let Some((_, destination)) = integer_conversion(a).filter(|(z, _)| z == b) {
        (b, destination.format())
    } else if let Some((_, destination)) = integer_conversion(b).filter(|(z, _)| z == a) {
        (a, destination.format())
    } else {
        return Err(invalid());
    };
    let bounded = original.as_ref();
    let lower = premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?;
    let upper = premises
        .get(bounds[1])
        .ok_or(Error::InvalidPremise(bounds[1]))?;
    let (lo, operand) = order(lower).ok_or_else(invalid)?;
    let (other_operand, hi) = order(upper).ok_or_else(invalid)?;
    // A bound may name the original or any observation with its value
    // reading, such as its widening (rule W, a relation across widths).
    let names_original = |operand: &SharedIntegerTerm| {
        operand.as_ref() == bounded
            || operand.value_read() == bounded.value_read()
            || crate::kernel::machine_integer::conversion::narrow_widening(operand, bounded)
    };
    if !names_original(operand) || !names_original(other_operand) {
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
    fn check_rule(
        bounds: Vec<usize>,
        goal: &crate::kernel::Proposition,
        premises: &[crate::kernel::Proposition],
    ) -> Result<(), super::Error> {
        super::check(0, &bounds, premises, goal)
    }

    use super::*;

    use crate::kernel::{
        IntegerTerm, MachineIntegerConstant, MachineIntegerType as Ty, MachineTerm, Variable,
    };
    use num_bigint::BigInt;

    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::condition_is(ConditionTerm::integer_less_equal(a, b), true)
    }
    fn inputs(source: Ty, destination: Ty) -> (Vec<Proposition>, Proposition) {
        let value = MachineTerm::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(source, value.clone()).unwrap();
        let cast = MachineTerm::machine_integer_cast(source, destination, value);
        let observed = IntegerTerm::from_machine(destination, cast).unwrap();
        let (lo, hi) = destination.format().bounds();
        (
            vec![
                le(IntegerTerm::constant(lo), original.clone()),
                le(original.clone(), IntegerTerm::constant(hi)),
            ],
            Proposition::condition_is(ConditionTerm::integer_equal(observed, original), true),
        )
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
                assert!(check_rule(vec![0, 1], &goal, &premises).is_ok());
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
                let Some((ConditionTerm::IntegerEqual(a, b), true)) = (&goal).condition_native()
                else {
                    unreachable!()
                };
                let reversed = Proposition::condition_is(
                    ConditionTerm::integer_equal(b.as_ref().clone(), a.as_ref().clone()),
                    true,
                );
                assert!(check_rule(vec![0, 1], &reversed, &premises).is_ok());
            }
        }
    }

    #[test]
    fn integer_cast_identity_checks_normalized_nested_conversions() {
        let variable = MachineTerm::Variable(Variable(168_001));
        for (source, intermediate, destination) in [
            (Ty::Int32, Ty::UInt32, Ty::UInt16),
            (Ty::UInt32, Ty::Int32, Ty::UInt16),
            (Ty::UInt8, Ty::UInt32, Ty::UInt16),
            (Ty::Int128, Ty::UInt64, Ty::Int32),
        ] {
            let widened = MachineTerm::machine_integer_cast(source, intermediate, variable.clone());
            let narrowed =
                MachineTerm::machine_integer_cast(intermediate, destination, widened.clone());
            let original = IntegerTerm::from_machine(intermediate, widened).unwrap();
            let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
            let goal = Proposition::condition_is(
                ConditionTerm::integer_equal(observed.clone(), original.clone()),
                true,
            );
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(255.into())),
            ];
            assert!(check_rule(vec![0, 1], &goal, &premises).is_ok());
            let wrong_source = vec![
                le(
                    IntegerTerm::constant(0.into()),
                    IntegerTerm::var(Variable(168_002)),
                ),
                premises[1].clone(),
            ];
            assert!(check_rule(vec![0, 1], &goal, &wrong_source).is_err());
            // The bounds must describe the source observation in the equality.
            // A widened intermediate has its operand's value (rule W), so
            // bounds on it describe the operand too.
            let underlying = IntegerTerm::from_machine(source, variable.clone()).unwrap();
            if underlying.value_read() == original.value_read() {
                continue;
            }
            let wrong_goal =
                Proposition::condition_is(ConditionTerm::integer_equal(observed, underlying), true);
            assert!(check_rule(vec![0, 1], &wrong_goal, &premises).is_err());
        }

        // Widening after a truncation cannot be treated as a direct cast of the
        // pre-truncation value, even if that value fits the final destination.
        let truncated = MachineTerm::machine_integer_cast(Ty::UInt32, Ty::UInt8, variable.clone());
        let widened = MachineTerm::machine_integer_cast(Ty::UInt8, Ty::UInt16, truncated);
        let original = IntegerTerm::from_machine(Ty::UInt32, variable).unwrap();
        let observed = IntegerTerm::from_machine(Ty::UInt16, widened).unwrap();
        let goal = Proposition::condition_is(
            ConditionTerm::integer_equal(observed, original.clone()),
            true,
        );
        let premises = vec![
            le(IntegerTerm::constant(0.into()), original.clone()),
            le(original, IntegerTerm::constant(65535.into())),
        ];
        assert!(check_rule(vec![0, 1], &goal, &premises).is_err());
    }

    #[test]
    fn integer_cast_identity_checks_unsigned_byte_readback_masks() {
        let value = MachineTerm::Variable(Variable(168_001));
        let original = IntegerTerm::from_machine(Ty::UInt32, value.clone()).unwrap();
        for destination in [Ty::UInt8, Ty::UInt16] {
            let mask = (1u32 << destination.format().bits()) - 1;
            let goal_with_mask = |mask| {
                let narrowed = binary_node!(
                    Int32,
                    BitwiseAnd,
                    Box::new(value.clone()),
                    Box::new(MachineTerm::constant(mask)),
                );
                let observed = IntegerTerm::from_machine(destination, narrowed).unwrap();
                Proposition::condition_is(
                    ConditionTerm::integer_equal(observed, original.clone()),
                    true,
                )
            };
            let goal = goal_with_mask(mask);
            let premises = vec![
                le(IntegerTerm::constant(0.into()), original.clone()),
                le(original.clone(), IntegerTerm::constant(mask.into())),
            ];
            assert!(check_rule(vec![0, 1], &goal, &premises).is_ok());
            for incorrect in [mask - 1, mask + 1, 0, u32::MAX] {
                let wrong = goal_with_mask(incorrect);
                assert!(check_rule(vec![0, 1], &wrong, &premises).is_err());
            }
            let outside = vec![
                premises[0].clone(),
                le(
                    original.clone(),
                    IntegerTerm::constant((u64::from(mask) + 1).into()),
                ),
            ];
            assert!(check_rule(vec![0, 1], &goal, &outside).is_err());
            let wrong_source = vec![
                premises[0].clone(),
                le(
                    IntegerTerm::var(Variable(168_002)),
                    IntegerTerm::constant(mask.into()),
                ),
            ];
            assert!(check_rule(vec![0, 1], &goal, &wrong_source).is_err());
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
            assert!(check_rule(bounds, &goal, &premises).is_err());
        }
        let original =
            IntegerTerm::from_machine(Ty::Int128, MachineTerm::Variable(Variable(168_001)))
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
                Proposition::condition_is(
                    ConditionTerm::integer_less_equal(IntegerTerm::constant(lo), original.clone()),
                    false,
                ),
                premises[1].clone(),
            ],
        ] {
            assert!(check_rule(vec![0, 1], &goal, &altered).is_err());
        }
        let stronger = vec![
            le(IntegerTerm::constant((-3).into()), original.clone()),
            le(original, IntegerTerm::constant(4.into())),
        ];
        assert!(check_rule(vec![0, 1], &goal, &stronger).is_ok());
        let (_, other_goal) = inputs(Ty::UInt128, Ty::Int64);
        assert!(check_rule(vec![0, 1], &other_goal, &premises).is_err());
    }

    #[test]
    fn integer_cast_identity_rejects_forged_format_payload_and_goal_polarity() {
        use crate::kernel::SharedMachineIntegerTerm;
        let (premises, _) = inputs(Ty::Int128, Ty::Int64);
        let original =
            IntegerTerm::from_machine(Ty::Int128, MachineTerm::Variable(Variable(168_001)))
                .unwrap();
        for (ty, source, destination, value) in [
            (
                Ty::Int32,
                Ty::Int128,
                Ty::Int64,
                MachineTerm::Variable(Variable(168_001)),
            ),
            (Ty::Int64, Ty::Int128, Ty::Int64, MachineTerm::constant(1)),
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
                MachineTerm::Cast {
                    spelling: crate::kernel::MachineCastSpelling::Generic,
                    from: source,
                    to: destination,
                    value: Box::new(value),
                },
            ));
            let goal = Proposition::condition_is(
                ConditionTerm::integer_equal(cast, original.clone()),
                true,
            );
            assert!(check_rule(vec![0, 1], &goal, &premises).is_err());
        }
        let (_, goal) = inputs(Ty::Int128, Ty::Int64);
        let Proposition::ConditionIs(condition, _) = goal else {
            unreachable!()
        };
        let false_goal = Proposition::condition_is(condition, false);
        assert!(check_rule(vec![0, 1], &false_goal, &premises).is_err());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/integer_cast_identity/tests.rs");
    }
}
