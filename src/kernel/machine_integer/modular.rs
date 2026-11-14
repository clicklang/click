//! Modular equality: an `Integer` equality over `+`, `-`, `*` and negation
//! of observations of formats of one width `w` implies the word equality
//! modulo `2^w`. Reduction modulo `2^w` maps `to_integer(x)` to the bits
//! of `x` and respects the ring operations, so equal Integers have equal
//! wrapped words: `to_integer(a) - to_integer(b) == 0` implies the word
//! `a - b` is zero. Only this direction holds, and only for equality.

use super::{Operation, comparison, range, representation};
use crate::kernel::{
    CompareRelation, ConditionTerm, IntegerTerm, KernelTerm, MachineIntegerType,
    MachineOperandView, MachineTerm,
};
use num_bigint::BigInt;

// Native inputs remain native; a shared observation never crosses the boxed
// boundary merely to construct its residue.
enum Residue {
    Native(MachineTerm),
    Shared(KernelTerm),
}

impl Residue {
    fn view(&self) -> MachineOperandView<'_> {
        match self {
            Self::Native(value) => MachineOperandView::Legacy(value),
            Self::Shared(value) => MachineOperandView::Shared(value),
        }
    }

    fn operation(
        modulus: MachineIntegerType,
        op: Operation,
        left: Self,
        right: Self,
    ) -> Option<Self> {
        if let (Self::Native(a), Self::Native(b)) = (&left, &right) {
            return representation::folded_operation_word(modulus, op, a.clone(), b.clone())
                .map(Self::Native);
        }
        let format = representation::operator_format(modulus)?;
        let retain = |value: Self| match value {
            Self::Shared(value) => value,
            Self::Native(value) => {
                KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(&value))
            }
        };
        let (left, right) = (retain(left), retain(right));
        let operator = representation::machine_binary_op_of(op);
        if let (Some(a), Some(b)) = (
            MachineOperandView::Shared(&left).literal(),
            MachineOperandView::Shared(&right).literal(),
        ) {
            return representation::folded_operation_word(modulus, op, a, b).map(Self::Native);
        }
        // Narrow native constructors fold literals only, unlike the word
        // comparison constructor (which also cancels x - x).
        let root = if format.format().bits() < 32 {
            KernelTerm::machine_binary_shared(format, operator, [left, right])
        } else if format == MachineIntegerType::UInt64 && op == Operation::Subtract && left == right
        {
            // The native uint64 constructor does not cancel identical words.
            KernelTerm::machine_binary_shared(format, operator, [left, right])
        } else {
            crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
                format, operator, left, right,
            )
        };
        Some(Self::Shared(root.with_machine_observation_type(modulus)))
    }
}

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
    let reduce = |constant: &BigInt| -> Option<Residue> {
        let modulo = BigInt::from(1) << width;
        let residue = ((constant % &modulo) + &modulo) % &modulo;
        range::constant_word(modulus, &residue).map(Residue::Native)
    };
    let word = |term: &IntegerTerm, nodes: &mut usize, observed: &mut bool| {
        fn walk(
            term: &IntegerTerm,
            modulus: MachineIntegerType,
            width: u32,
            reduce: &dyn Fn(&BigInt) -> Option<Residue>,
            nodes: &mut usize,
            observed: &mut bool,
        ) -> Option<Residue> {
            crate::instrumentation::record_deterministic_work(1);
            *nodes += 1;
            if *nodes > 64 {
                return None;
            }
            let mut walk = |term: &IntegerTerm| walk(term, modulus, width, reduce, nodes, observed);
            Some(match term {
                IntegerTerm::Machine(machine) if machine.ty().format().bits() == width => {
                    *observed = true;
                    match machine.shared_operand() {
                        Some(root) => Residue::Shared(root.with_machine_observation_type(modulus)),
                        None => Residue::Native(machine.value().clone()),
                    }
                }
                IntegerTerm::Constant(constant) => reduce(constant)?,
                IntegerTerm::Negate(inner) => {
                    let inner = walk(inner)?;
                    Residue::operation(
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
                    Residue::operation(modulus, operation, left, right)?
                }
            })
        }
        walk(term, modulus, width, &reduce, nodes, observed)
    };
    let (mut nodes, mut observed) = (0, false);
    let left = word(left, &mut nodes, &mut observed)?;
    let right = word(right, &mut nodes, &mut observed)?;
    let wrapped = comparison::condition_for_operand_views(
        modulus,
        CompareRelation::Equal,
        [left.view(), right.view()],
    );
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::*;

    fn shared(ty: MachineIntegerType, depth: usize) -> IntegerTerm {
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1007100));
        for _ in 0..depth {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap())
    }

    fn boxed(condition: ConditionTerm) -> ConditionTerm {
        comparison::native_comparison_of_integer_observation(&condition, true)
            .map(|v| v.0)
            .unwrap_or(condition)
    }

    #[test]
    fn shared_projection_matches_native_width_polarity_and_ring_operations() {
        let _session = VerificationSession::enter();
        use MachineIntegerType as T;
        for ty in [
            T::Int8,
            T::UInt8,
            T::Int16,
            T::UInt16,
            T::Int32,
            T::UInt32,
            T::Int64,
            T::UInt64,
        ] {
            let a = shared(ty, 2);
            for op in Operation::ALL {
                for right in [
                    IntegerTerm::constant_i64(-3),
                    shared(ty, 1),
                    a.clone(),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        ty,
                        MachineTerm::If {
                            condition: ConditionTerm::Variable(Variable(1007101)).into(),
                            then_term: MachineTerm::Variable(Variable(1007102)).into(),
                            else_term: MachineTerm::Variable(Variable(1007103)).into(),
                        },
                    )),
                ] {
                    let expression = op.exact(a.clone(), right);
                    for expression in [expression.clone(), IntegerTerm::Negate(expression.into())] {
                        for reversed in [false, true] {
                            let (left, right) = if reversed {
                                (IntegerTerm::constant_i64(-1), expression.clone())
                            } else {
                                (expression.clone(), IntegerTerm::constant_i64(-1))
                            };
                            for truth in [false, true] {
                                let condition = if truth {
                                    ConditionTerm::IntegerEqual(
                                        left.clone().into(),
                                        right.clone().into(),
                                    )
                                } else {
                                    ConditionTerm::IntegerNotEqual(
                                        left.clone().into(),
                                        right.clone().into(),
                                    )
                                };
                                let before = KernelTermExport::machine_export_count();
                                let actual = wrapped_equality_at(ty, &condition, truth);
                                assert_eq!(KernelTermExport::machine_export_count(), before);
                                let expected = native_reference(ty, &condition, truth);
                                assert_eq!(actual.map(boxed), expected, "{ty:?} {op:?}");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn projection_preserves_refusals_and_outer_node_budget() {
        let _session = VerificationSession::enter();
        use MachineIntegerType as T;
        let source = shared(T::Int32, 3);
        let condition =
            ConditionTerm::IntegerEqual(source.clone().into(), IntegerTerm::constant_i64(0).into());
        let before = KernelTermExport::machine_export_count();
        assert!(wrapped_equality_at(T::UInt32, &condition, false).is_none());
        for ty in [T::UInt8, T::UInt16, T::UInt64, T::UInt128, T::Int128] {
            assert!(wrapped_equality_at(ty, &condition, true).is_none());
        }
        let constants = ConditionTerm::IntegerEqual(
            IntegerTerm::constant_i64(1).into(),
            IntegerTerm::constant_i64(2).into(),
        );
        assert!(wrapped_equality_at(T::UInt32, &constants, true).is_none());
        let mut term = source;
        // 62 negations + observation + right constant = 64 outer nodes.
        for _ in 0..62 {
            term = IntegerTerm::Negate(term.into());
        }
        let at_limit =
            ConditionTerm::IntegerEqual(term.clone().into(), IntegerTerm::constant_i64(0).into());
        assert!(wrapped_equality_at(T::UInt32, &at_limit, true).is_some());
        let over_limit = ConditionTerm::IntegerEqual(
            IntegerTerm::Negate(term.into()).into(),
            IntegerTerm::constant_i64(0).into(),
        );
        assert!(wrapped_equality_at(T::UInt32, &over_limit, true).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/machine_integer/modular.rs");
    }
    fn native_reference(
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
        let reduce = |constant: &BigInt| -> Option<MachineTerm> {
            let modulo = BigInt::from(1) << width;
            let residue = ((constant % &modulo) + &modulo) % &modulo;
            range::constant_word(modulus, &residue)
        };
        let word = |term: &IntegerTerm, nodes: &mut usize, observed: &mut bool| {
            fn walk(
                term: &IntegerTerm,
                modulus: MachineIntegerType,
                width: u32,
                reduce: &dyn Fn(&BigInt) -> Option<MachineTerm>,
                nodes: &mut usize,
                observed: &mut bool,
            ) -> Option<MachineTerm> {
                *nodes += 1;
                if *nodes > 64 {
                    return None;
                }
                let mut walk =
                    |term: &IntegerTerm| walk(term, modulus, width, reduce, nodes, observed);
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
        let (wrapped, _) =
            representation::comparison(modulus, super::super::Relation::Equal, left, right)?;
        (observed && !matches!(wrapped, ConditionTerm::Constant(_))).then_some(wrapped)
    }
}
