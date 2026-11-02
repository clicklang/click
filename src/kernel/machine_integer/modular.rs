//! Modular equality: an `Integer` equality over `+`, `-`, `*` and negation
//! of observations of formats of one width `w` implies the word equality
//! modulo `2^w`. Reduction modulo `2^w` maps `to_integer(x)` to the bits
//! of `x` and respects the ring operations, so equal Integers have equal
//! wrapped words: `to_integer(a) - to_integer(b) == 0` implies the word
//! `a - b` is zero. Only this direction holds, and only for equality.

use super::{Operation, Relation, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType};
use num_bigint::BigInt;

/// Reference spelling of the old 32-bit admission consequence, retained for
/// differential tests. Admission now registers the residue relation directly
/// in the graph; explicit equality rewriting still uses `wrapped_equality_at`.
#[cfg(test)]
pub(crate) fn wrapped_equality_of_integer_equality(
    condition: &ConditionTerm,
    value: bool,
) -> Option<ConditionTerm> {
    wrapped_equality_at(MachineIntegerType::UInt32, condition, value)
}

/// The word equality modulo `2^w` that an Integer equality implies, where
/// `w` is the width of `modulus` and the equality is over observations of
/// formats of that width (`int32` and `uint32` for 32 bits), constants and
/// ring operations. `None` when the equality names no such observation, an
/// observation of another width, or `modulus` is a 128-bit format, which has
/// no operations. An 8- or 16-bit format's operations are native, of its own
/// width.
pub(crate) fn wrapped_equality_at(
    modulus: MachineIntegerType,
    condition: &ConditionTerm,
    value: bool,
) -> Option<ConditionTerm> {
    let ((ConditionTerm::IntegerEqual(left, right), true)
    | (ConditionTerm::IntegerNotEqual(left, right), false)) = (condition, value)
    else {
        return None;
    };
    // The operations reduce modulo their format's width; a 128-bit format
    // has none.
    let width = modulus.format().bits();
    if representation::word_bits(modulus) != Some(width) {
        return None;
    }
    let reduce = |constant: &BigInt| -> Option<Bitvector32Term> {
        let modulo = BigInt::from(1) << width;
        let residue = ((constant % &modulo) + &modulo) % &modulo;
        range::constant_word(modulus, &residue)
    };
    let word = |term: &IntegerTerm, nodes: &mut usize, observed: &mut bool| {
        fn walk(
            term: &IntegerTerm,
            modulus: MachineIntegerType,
            width: u32,
            reduce: &dyn Fn(&BigInt) -> Option<Bitvector32Term>,
            nodes: &mut usize,
            observed: &mut bool,
        ) -> Option<Bitvector32Term> {
            *nodes += 1;
            if *nodes > 64 {
                return None;
            }
            let mut walk = |term: &IntegerTerm| walk(term, modulus, width, reduce, nodes, observed);
            Some(match term {
                IntegerTerm::Machine(machine) if machine.ty().format().bits() == width => {
                    *observed = true;
                    machine.value().clone()
                }
                IntegerTerm::Constant(constant) => reduce(constant)?,
                IntegerTerm::Negate(inner) => {
                    let inner = walk(inner)?;
                    representation::folded_operation_word(
                        modulus,
                        Operation::Subtract,
                        reduce(&BigInt::from(0))?,
                        inner,
                    )?
                }
                _ => {
                    let (operation, left, right) = Operation::of_exact(term)?;
                    let left = walk(left)?;
                    let right = walk(right)?;
                    representation::folded_operation_word(modulus, operation, left, right)?
                }
            })
        }
        walk(term, modulus, width, &reduce, nodes, observed)
    };
    let (mut nodes, mut observed) = (0, false);
    let left = word(left, &mut nodes, &mut observed)?;
    let right = word(right, &mut nodes, &mut observed)?;
    let (wrapped, _) = representation::comparison(modulus, Relation::Equal, left, right)?;
    (observed && !matches!(wrapped, ConditionTerm::Constant(_))).then_some(wrapped)
}

/// Whether the bounded 32-bit residue projection applies. Admission records
/// that consequence in the graph from the original Integer equality.
pub(crate) fn has_word_equality_projection(condition: &ConditionTerm, value: bool) -> bool {
    let ((ConditionTerm::IntegerEqual(left, right), true)
    | (ConditionTerm::IntegerNotEqual(left, right), false)) = (condition, value)
    else {
        return false;
    };
    let mut pending = vec![left.as_ref(), right.as_ref()];
    let (mut count, mut observed) = (0, false);
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        count += 1;
        if count > 64 {
            return false;
        }
        match term {
            IntegerTerm::Machine(machine) if machine.ty().format().bits() == 32 => observed = true,
            IntegerTerm::Constant(_) => {}
            IntegerTerm::Negate(inner) => pending.push(inner),
            _ => {
                let Some((_, left, right)) = Operation::of_exact(term) else {
                    return false;
                };
                pending.push(right);
                pending.push(left);
            }
        }
    }
    observed
}
