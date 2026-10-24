//! Operation bounds: the bound a quotient, right shift or remainder by a
//! positive constant puts between the result and its operand.
//!
//! For an unsigned `q = x / c` with `c > 0`, truncating division is the
//! floor, so `c * q <= x <= c * q + (c - 1)`. A logical right shift
//! `x >> k` with `k` below the width is the floor of `x / 2^k`, the same
//! form with `c = 2^k`. For `r = x % c` the upper bound is `r <= c - 1`;
//! the format's range already says `0 <= r`.

use super::representation::{self, Division};
use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, Proposition, SharedMachineIntegerTerm,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// The constant a machine word spells, read as unsigned bits.
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
/// zero or symbolic divisor, a shift by the width or more, a remainder's
/// lower bound, and a format with no division nodes
/// (`representation::word_division`) have none.
pub(crate) fn operation_bound(
    value: &SharedMachineIntegerTerm,
    upper: bool,
) -> Option<Proposition> {
    let ty = value.ty();
    let format = ty.format();
    let (division, operand, divisor) = representation::word_division(ty, value.value())?;
    let divisor = match division {
        Division::ShiftRight => {
            let amount = usize::try_from(unsigned_constant(divisor)?).ok()?;
            if amount >= usize::try_from(format.bits()).ok()? {
                return None;
            }
            BigInt::one() << amount
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
            if upper {
                ConditionTerm::integer_less_equal(
                    operand,
                    IntegerTerm::Add(scaled.into(), IntegerTerm::constant(slack).into()),
                )
            } else {
                ConditionTerm::integer_less_equal(scaled, operand)
            }
        }
        Division::Remainder if upper => {
            ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(slack))
        }
        Division::Remainder => return None,
    };
    Some(Proposition::ConditionIs(condition, true))
}
