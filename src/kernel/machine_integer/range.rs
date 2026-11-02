//! Range: `min(F) <= to_integer(v) <= max(F)` for every value `v` of a
//! format `F`. A term of format `F` denotes an element of `F`'s range
//! (`docs/internals/kernel.md`, "One meaning for a narrow value"), so this
//! holds of every observation with no premise.

use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerConstant, MachineIntegerType,
    Proposition, SharedMachineIntegerTerm,
};
use num_bigint::BigInt;

/// The inclusive range of `ty`.
pub(crate) fn range(ty: MachineIntegerType) -> (BigInt, BigInt) {
    ty.format().bounds()
}

/// The bound the range of `value`'s format puts on its observation:
/// `MIN <= to_integer(value)`, or with `upper`, `to_integer(value) <= MAX`.
/// The format is that of the observation's value reading (rule W): a
/// widening's value lies in its operand's range, so
/// `to_integer(x as uint32) <= 65535` for a `uint16` `x`. The observation
/// is stated as written.
pub(crate) fn range_fact(value: &SharedMachineIntegerTerm, upper: bool) -> Proposition {
    let (min, max) = observation_range(value);
    let observed = IntegerTerm::Machine(value.clone());
    let condition = if upper {
        ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(max))
    } else {
        ConditionTerm::integer_less_equal(IntegerTerm::constant(min), observed)
    };
    Proposition::ConditionIs(condition, true)
}

/// The range of an observation's value: its format's, or the format of its
/// value reading (rule W) when it has one, which a conversion's value never
/// leaves. One cached lookup.
pub(crate) fn observation_range(value: &SharedMachineIntegerTerm) -> (BigInt, BigInt) {
    match value.value_reading() {
        Some(IntegerTerm::Machine(read)) => range(read.ty()),
        _ => range(value.ty()),
    }
}

/// The word that spells the constant `value` at `ty`, or `None` when
/// `value` is outside `ty`'s range.
pub(crate) fn constant_word(ty: MachineIntegerType, value: &BigInt) -> Option<Bitvector32Term> {
    ty.constant_term(MachineIntegerConstant::from_integer(ty.format(), value)?)
}
