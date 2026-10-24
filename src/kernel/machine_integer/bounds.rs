//! Operation bounds: the bound a quotient, right shift or remainder by a
//! positive constant puts between the result and its operand.
//!
//! For `q = x / c` with `c > 0` truncated toward zero, `x - c * q` is the
//! remainder `r`, which has the sign of `x` and `|r| <= c - 1`:
//!
//! - in an unsigned format `x >= 0`, so `c * q <= x <= c * q + (c - 1)`;
//! - in a signed one, `c * q - (c - 1) <= x <= c * q + (c - 1)`.
//!
//! A right shift `x >> k` with `k` below the width is the floor of
//! `x / 2^k` in both signednesses (the logical shift of an unsigned value,
//! the arithmetic shift of a signed one), so it has the unsigned form with
//! `c = 2^k`. For `r = x % c` the upper bound is `r <= c - 1` and, in a
//! signed format, the lower bound `-(c - 1) <= r`; an unsigned format's
//! range already says `0 <= r`.
//!
//! Every quotient here is defined: `c > 0` excludes division by zero and
//! the one signed overflow, `MIN / -1`.

use super::representation::{self, Division};
use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, Proposition, SharedMachineIntegerTerm,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// The constant a machine word spells, read as unsigned bits: a shift
/// amount is a count, whatever word carries it.
fn unsigned_constant(term: &Bitvector32Term) -> Option<BigInt> {
    match term {
        Bitvector32Term::Constant(value) => Some(BigInt::from(*value)),
        Bitvector32Term::Int64Constant(value) => Some(BigInt::from(*value)),
        Bitvector32Term::UInt64Constant(value) => Some(BigInt::from(*value)),
        _ => None,
    }
}

/// The bound a quotient, right shift or remainder by a constant takes from
/// its operand, as an Integer comparison (see the module documentation).
/// `upper` selects the upper bound. A value that is no such operation, a
/// divisor that is not a positive constant of the value's format, a shift
/// by the width or more, an unsigned remainder's lower bound, and a format
/// with no division nodes (`representation::word_division`) have none.
pub(crate) fn operation_bound(
    value: &SharedMachineIntegerTerm,
    upper: bool,
) -> Option<Proposition> {
    let ty = value.ty();
    let format = ty.format();
    let signed = format.is_signed();
    let (division, operand, divisor) = representation::word_division(ty, value.value())?;
    let divisor = match division {
        Division::ShiftRight => {
            let amount = usize::try_from(unsigned_constant(divisor)?).ok()?;
            if amount >= usize::try_from(format.bits()).ok()? {
                return None;
            }
            BigInt::one() << amount
        }
        // A signed divisor is read at its format: the word `0xffffffff`
        // is `-1`, not a positive number.
        Division::Quotient | Division::Remainder if signed => {
            ty.constant_from_term(divisor)?.to_integer()
        }
        Division::Quotient | Division::Remainder => unsigned_constant(divisor)?,
    };
    if divisor <= BigInt::zero() {
        return None;
    }
    let slack = &divisor - BigInt::one();
    let observed = IntegerTerm::Machine(value.clone());
    let condition = match division {
        Division::Quotient | Division::ShiftRight => {
            let operand = IntegerTerm::from_machine(ty, operand.clone())?;
            let scaled =
                IntegerTerm::Multiply(IntegerTerm::constant(divisor).into(), observed.into());
            match (upper, signed && division == Division::Quotient) {
                (true, _) => ConditionTerm::integer_less_equal(
                    operand,
                    IntegerTerm::Add(scaled.into(), IntegerTerm::constant(slack).into()),
                ),
                (false, false) => ConditionTerm::integer_less_equal(scaled, operand),
                (false, true) => ConditionTerm::integer_less_equal(
                    IntegerTerm::Add(scaled.into(), IntegerTerm::constant(-slack).into()),
                    operand,
                ),
            }
        }
        Division::Remainder if upper => {
            ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(slack))
        }
        Division::Remainder if signed => {
            ConditionTerm::integer_less_equal(IntegerTerm::constant(-slack), observed)
        }
        Division::Remainder => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::MachineBinaryOp;
    use crate::kernel::{MachineIntegerType, Variable};

    fn machine(ty: MachineIntegerType, value: Bitvector32Term) -> SharedMachineIntegerTerm {
        SharedMachineIntegerTerm::intern(ty, value)
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(left, right), true)
    }

    fn scaled(divisor: i64, value: &SharedMachineIntegerTerm) -> IntegerTerm {
        IntegerTerm::Multiply(
            IntegerTerm::constant_i64(divisor).into(),
            IntegerTerm::Machine(value.clone()).into(),
        )
    }

    fn plus(term: IntegerTerm, constant: i64) -> IntegerTerm {
        IntegerTerm::Add(term.into(), IntegerTerm::constant_i64(constant).into())
    }

    #[test]
    fn a_signed_quotient_is_within_its_divisor_of_its_operand_either_way() {
        for (ty, word, divisor) in [
            (
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(173_001)),
                Bitvector32Term::Constant(8),
            ),
            (
                MachineIntegerType::Int64,
                Bitvector32Term::Variable(Variable(173_001)),
                Bitvector32Term::Int64Constant(8),
            ),
        ] {
            let operand = IntegerTerm::from_machine(ty, word.clone()).unwrap();
            let quotient = machine(
                ty,
                representation_quotient(ty, word.clone(), divisor.clone()),
            );
            // `8 * q - 7 <= x` and `x <= 8 * q + 7`: truncation toward zero
            // leaves a remainder with the sign of `x`.
            assert_eq!(
                operation_bound(&quotient, false),
                Some(less_equal(plus(scaled(8, &quotient), -7), operand.clone()))
            );
            assert_eq!(
                operation_bound(&quotient, true),
                Some(less_equal(operand.clone(), plus(scaled(8, &quotient), 7)))
            );
            // A remainder lies in `-7..=7`.
            let remainder = machine(
                ty,
                match ty {
                    MachineIntegerType::Int32 => Bitvector32Term::Remainder(
                        Box::new(word.clone()),
                        Box::new(divisor.clone()),
                    ),
                    _ => Bitvector32Term::Binary {
                        format: MachineIntegerType::Int64,
                        op: MachineBinaryOp::Remainder,
                        left: Box::new(word.clone()),
                        right: Box::new(divisor.clone()),
                    },
                },
            );
            let observed = IntegerTerm::Machine(remainder.clone());
            assert_eq!(
                operation_bound(&remainder, false),
                Some(less_equal(IntegerTerm::constant_i64(-7), observed.clone()))
            );
            assert_eq!(
                operation_bound(&remainder, true),
                Some(less_equal(observed, IntegerTerm::constant_i64(7)))
            );
            // An arithmetic shift is the floor: `8 * (x >> 3) <= x`.
            let shifted = machine(
                ty,
                match ty {
                    MachineIntegerType::Int32 => Bitvector32Term::ArithmeticShiftRight(
                        Box::new(word.clone()),
                        Box::new(Bitvector32Term::Constant(3)),
                    ),
                    _ => Bitvector32Term::Binary {
                        format: MachineIntegerType::Int64,
                        op: MachineBinaryOp::ShiftRight,
                        left: Box::new(word.clone()),
                        right: Box::new(Bitvector32Term::Constant(3)),
                    },
                },
            );
            assert_eq!(
                operation_bound(&shifted, false),
                Some(less_equal(scaled(8, &shifted), operand.clone()))
            );
            assert_eq!(
                operation_bound(&shifted, true),
                Some(less_equal(operand, plus(scaled(8, &shifted), 7)))
            );
        }
    }

    fn representation_quotient(
        ty: MachineIntegerType,
        word: Bitvector32Term,
        divisor: Bitvector32Term,
    ) -> Bitvector32Term {
        match ty {
            MachineIntegerType::Int32 => Bitvector32Term::Divide(Box::new(word), Box::new(divisor)),
            _ => Bitvector32Term::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Divide,
                left: Box::new(word),
                right: Box::new(divisor),
            },
        }
    }

    #[test]
    fn a_signed_divisor_is_read_at_its_format() {
        // The word `0xfffffff8` is `-8` in `int32`, which bounds nothing,
        // though its unsigned reading is a large positive number.
        let x = Box::new(Bitvector32Term::Variable(Variable(173_002)));
        for divisor in [
            Bitvector32Term::Constant(-8i32 as u32),
            Bitvector32Term::Constant(0),
        ] {
            for word in [
                Bitvector32Term::Divide(x.clone(), Box::new(divisor.clone())),
                Bitvector32Term::Remainder(x.clone(), Box::new(divisor.clone())),
            ] {
                let value = machine(MachineIntegerType::Int32, word);
                assert_eq!(operation_bound(&value, false), None);
                assert_eq!(operation_bound(&value, true), None);
            }
        }
        // A shift by the width or more, or by a negative count, has none.
        for amount in [32u32, -1i32 as u32] {
            let value = machine(
                MachineIntegerType::Int32,
                Bitvector32Term::ArithmeticShiftRight(
                    x.clone(),
                    Box::new(Bitvector32Term::Constant(amount)),
                ),
            );
            assert_eq!(operation_bound(&value, true), None);
        }
    }
}
