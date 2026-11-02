//! In-range identity: `to_integer(a op b) == to_integer(a) op to_integer(b)`
//! for a machine `+`, `-` or `*` of format `F` whose exact result lies in
//! `F`.
//!
//! The machine operation is the exact result reduced modulo `2^w` into
//! `F`: each operand's word is congruent to its value modulo `2^w`
//! (a narrow value's word is its canonical extension, congruent modulo
//! `2^32` and so modulo its own `2^w`), and `+`, `-` and `*` respect the
//! congruence. When the exact result lies in `F` it is the one element of
//! `F` in its residue class, so it is the machine result. The certificate
//! rule `integer_operation_identity` checks this statement for the format
//! the observation names, with the two bounds as premises.

use super::{Operation, definedness, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition};
use num_bigint::BigInt;

/// The format of the machine `+`, `-` or `*` that `observed` reads, and
/// its exact value spelled over the operands' own observations in that
/// format. `to_integer(observed) == value` is the in-range identity once
/// `value` is bounded inside the format.
pub(crate) fn mathematical(observed: &IntegerTerm) -> Option<(MachineIntegerType, IntegerTerm)> {
    // An observation of σ or a widening of the operation is read through
    // its value relation (rule W) to the operation's own observation.
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    let ty = machine.ty();
    // An explicit operation's identity refers to its actual operands. Only
    // an observation of a stored read needs the read-over-write adapter;
    // recursively expanding an explicit operation changes the identity the
    // source expression asks for.
    let resolved = representation::word_operation(machine.ty(), machine.value())
        .is_none()
        .then(|| crate::kernel::eval::read_over_write_value(machine.value()))
        .flatten();
    let (operation, left, right) =
        representation::word_operation(ty, resolved.as_ref().unwrap_or(machine.value()))?;
    let left = IntegerTerm::from_machine(ty, left.clone())?;
    let right = IntegerTerm::from_machine(ty, right.clone())?;
    Some((ty, operation.exact(left, right)))
}

/// Whether `stated` is the exact value `value` of an operation
/// ([`mathematical`]) up to the value relations of its operands' observations
/// (rule W): the same operation over operands with one value reading each,
/// `to_integer(tag) + to_integer(p0 as uint32)` for the observation of
/// `tag + p0` at `uint32`. O(1): one root match and two readings per side.
pub(crate) fn same_exact_value(value: &IntegerTerm, stated: &IntegerTerm) -> bool {
    if value == stated {
        return true;
    }
    match (Operation::of_exact(value), Operation::of_exact(stated)) {
        (Some((operation, left, right)), Some((stated_operation, stated_left, stated_right))) => {
            operation == stated_operation
                && left.value_read() == stated_left.value_read()
                && right.value_read() == stated_right.value_read()
        }
        _ => false,
    }
}

/// [`mathematical`] for `+` and `-` only: the operations whose identity
/// the comparison readings and the surface's identity planner spell.
pub(crate) fn additive_mathematical(
    observed: &IntegerTerm,
) -> Option<(MachineIntegerType, IntegerTerm)> {
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    // An explicit operation's identity refers to its actual operands. Only
    // an observation of a stored read needs the read-over-write adapter;
    // recursively expanding an explicit operation changes the identity the
    // source expression asks for.
    let resolved = representation::word_operation(machine.ty(), machine.value())
        .is_none()
        .then(|| crate::kernel::eval::read_over_write_value(machine.value()))
        .flatten();
    match representation::word_operation(
        machine.ty(),
        resolved.as_ref().unwrap_or(machine.value()),
    )? {
        (Operation::Add | Operation::Subtract, _, _) => mathematical(observed),
        (Operation::Multiply, _, _) => None,
    }
}

/// One endpoint of a format's range that the exact value of a machine
/// `+` or `-` must respect for the operation to equal that value: `exact
/// >= bound` when `lower`, else `exact <= bound`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegerOperationRangeBound {
    pub(crate) exact: IntegerTerm,
    pub(crate) bound: BigInt,
    pub(crate) lower: bool,
}

impl IntegerOperationRangeBound {
    /// The Integer facts that state this bound: its two order spellings
    /// and, for an operation with an overflow test, the definedness fact
    /// each of them reads (`definedness::definedness_of_integer_bound`).
    pub(crate) fn stating_facts(&self) -> Vec<Proposition> {
        let bound = IntegerTerm::constant(self.bound.clone());
        let forms = if self.lower {
            [
                ConditionTerm::integer_greater_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_less_equal(bound, self.exact.clone()),
            ]
        } else {
            [
                ConditionTerm::integer_less_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_greater_equal(bound, self.exact.clone()),
            ]
        };
        let mut facts = forms
            .into_iter()
            .map(|form| Proposition::ConditionIs(form, true))
            .collect::<Vec<_>>();
        // 0 <= (x - y) is exactly y <= x. Retain the native spelling
        // when both observations have the same format, so a direct machine
        // bound can certify subtraction without a difference-graph walk.
        if self.lower
            && self.bound == BigInt::from(0)
            && let IntegerTerm::Subtract(left, right) = &self.exact
            && let (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) =
                (left.as_ref(), right.as_ref())
            && left.ty() == right.ty()
        {
            facts.push(Proposition::ConditionIs(
                ConditionTerm::machine_compare(
                    left.ty(),
                    crate::kernel::CompareRelation::LessEqual,
                    right.value().clone(),
                    left.value().clone(),
                ),
                true,
            ));
        }
        if let Some(defined) = facts
            .iter()
            .find_map(definedness::definedness_of_integer_bound)
        {
            facts.push(defined);
        }
        facts
    }
}

/// The exact observation of the machine `+` or `-` in `ty` whose
/// mathematical value ([`mathematical`]) is `exact`, an Integer sum or
/// difference of observations and constants, with the range bounds the
/// operation must respect to equal it. A bound the operands' own ranges
/// already imply is not listed: `4294967295 - to_integer(b)` for `uint32`
/// `b` lies in `uint32` and needs none. The candidate is recomputed through
/// the forward map, so only an exact reading is returned.
pub(crate) fn machine_operation_of_integer_value(
    exact: &IntegerTerm,
    ty: MachineIntegerType,
) -> Option<(IntegerTerm, Vec<IntegerOperationRangeBound>)> {
    let (operation, left, right) = match Operation::of_exact(exact)? {
        found @ (Operation::Add | Operation::Subtract, _, _) => found,
        (Operation::Multiply, _, _) => return None,
    };
    // An operand's word is the one, as written or widened, whose
    // observation in `ty` gives the operand back; its range is its own
    // format's, or the constant itself.
    let operand = |side: &IntegerTerm| -> Option<(Bitvector32Term, BigInt, BigInt)> {
        // An observation is read through its value relations (rule W): the
        // range of `to_integer(x as uint32)` is `x`'s own format's.
        match side.value_read() {
            IntegerTerm::Machine(machine) => {
                let word = machine.value().clone();
                let widened = Bitvector32Term::MachineIntegerCast {
                    value: Box::new(word.clone()),
                    source: machine.ty(),
                    destination: ty,
                };
                // A value of another width is never `ty`'s word as written:
                // its word in `ty` is its widening, a node of its own.
                let as_written =
                    (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                let word = as_written.into_iter().chain([widened]).find(|word| {
                    IntegerTerm::from_machine(ty, word.clone())
                        .is_some_and(|observed| observed.value_read() == side.value_read())
                })?;
                let (low, high) = range::range(machine.ty());
                Some((word, low, high))
            }
            IntegerTerm::Constant(value) => Some((
                range::constant_word(ty, value)?,
                value.clone(),
                value.clone(),
            )),
            _ => None,
        }
    };
    let (left_word, left_low, left_high) = operand(left)?;
    let (right_word, right_low, right_high) = operand(right)?;
    let word =
        representation::operation_word(ty, operation, Box::new(left_word), Box::new(right_word))?;
    let observed = IntegerTerm::from_machine(ty, word)?;
    let (read_ty, value) = mathematical(&observed)?;
    if read_ty != ty || !same_exact_value(&value, exact) {
        return None;
    }
    let (low, high) = if operation == Operation::Subtract {
        (left_low - right_high, left_high - right_low)
    } else {
        (left_low + right_low, left_high + right_high)
    };
    let (minimum, maximum) = range::range(ty);
    let mut bounds = Vec::new();
    if low < minimum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: minimum,
            lower: true,
        });
    }
    if high > maximum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: maximum,
            lower: false,
        });
    }
    Some((observed, bounds))
}

#[test]
fn explicit_operation_identity_keeps_its_read_operands() {
    use crate::kernel::{CMemory, CValue, LoadKind, Pointer, Variable};
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let x = Bitvector32Term::Variable(Variable(989_773));
    let y = Bitvector32Term::Variable(Variable(989_774));
    let address = Pointer::symbolic(Variable(989_775));
    let stored = Bitvector32Term::logical_machine_binary(
        format,
        crate::kernel::MachineBinaryOp::Add,
        x.clone(),
        Bitvector32Term::Constant(1),
    );
    let memory = CMemory::new().store(address.clone(), CValue::Int32(stored));
    let read = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_c_memory_ref(&memory),
        address,
        LoadKind::Int32,
    );
    let observe = |value| IntegerTerm::from_machine(format, value).unwrap();
    let sum = observe(Bitvector32Term::logical_machine_binary(
        format,
        crate::kernel::MachineBinaryOp::Add,
        read.clone(),
        y.clone(),
    ));
    assert_eq!(
        mathematical(&sum),
        Some((format, IntegerTerm::add(observe(read.clone()), observe(y))))
    );
    assert_eq!(
        mathematical(&observe(read)),
        Some((
            format,
            IntegerTerm::add(observe(x), IntegerTerm::constant(1.into()))
        ))
    );
}
