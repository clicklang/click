//! Modular equality: an `Integer` equality over `+`, `-`, `*` and negation
//! of observations of formats of one width `w` implies the word equality
//! modulo `2^w`. Reduction modulo `2^w` maps `to_integer(x)` to the bits
//! of `x` and respects the ring operations, so equal Integers have equal
//! wrapped words: `to_integer(a) - to_integer(b) == 0` implies the word
//! `a - b` is zero. Only this direction holds, and only for equality.

use super::{Operation, Relation, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType};
use num_bigint::BigInt;

/// The word equality an Integer equality over 32-bit machine observations
/// implies, which built-in checks reading machine facts (a population count
/// retired at zero) can use. The result is filed as a consequence and never
/// used to decide the Integer equality. Terms of more than 64 nodes are
/// left alone.
///
/// The rule holds at every width ([`wrapped_equality_at`]); the fact
/// context files it at 32 bits, where its consumers read.
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
/// observation of another width, or `modulus` is not as wide as the word its
/// operations reduce in (a narrow format, whose operations are 32-bit, or a
/// 128-bit one, which has none).
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
    // The word operations reduce modulo the word's width, which is the
    // modulus only for a format as wide as its word: an 8-bit sum is a
    // 32-bit word sum, not reduced modulo 2^8.
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
