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
pub(crate) fn range_fact(value: &SharedMachineIntegerTerm, upper: bool) -> Proposition {
    let (min, max) = range(value.ty());
    let observed = IntegerTerm::Machine(value.clone());
    let condition = if upper {
        ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(max))
    } else {
        ConditionTerm::integer_less_equal(IntegerTerm::constant(min), observed)
    };
    Proposition::ConditionIs(condition, true)
}

/// The word that spells the constant `value` at `ty`, or `None` when
/// `value` is outside `ty`'s range.
pub(crate) fn constant_word(ty: MachineIntegerType, value: &BigInt) -> Option<Bitvector32Term> {
    ty.constant_term(MachineIntegerConstant::from_integer(ty.format(), value)?)
}
