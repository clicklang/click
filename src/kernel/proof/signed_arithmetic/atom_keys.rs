//! Signed-certificate atom identities backed by the common structural DAG.
//! The admitted fragment and opaque-atom rule are unchanged; these keys are
//! checking metadata and never replace a written expression.
use super::*;
use crate::kernel::{KernelTerm, KernelTermImport, KernelTermNode, KernelType, MachineUnaryOp};
use MachineIntegerType as T;
use SignedArithmeticAtomToken as Token;

fn constant(bits: u32) -> KernelTerm {
    KernelTermImport::default().machine(T::Int32, &MachineTerm::constant(bits))
}
fn variable(variable: Variable) -> KernelTerm {
    if crate::kernel::is_load_variable(&variable)
        && let Some(read) = crate::kernel::eval::registered_scalar_read_term(&variable, T::Int32)
    {
        return read;
    }
    KernelTerm::variable(KernelType::C(T::Int32.c_type()), variable)
}
fn low_word(value: KernelTerm) -> KernelTerm {
    KernelTerm::machine_cast_shared(
        MachineCastSpelling::UInt32From64,
        T::UInt64,
        T::UInt32,
        value,
    )
}

/// The legacy input is already an explicit tree. Read its prefix tokens once;
/// subsequent claim operations retain only a structural handle.
pub(super) fn from_tokens(tokens: Vec<Token>) -> Option<SignedArithmeticAtom> {
    let widening = |token: &Token| {
        matches!(token,
        Token::Cast { source, destination: T::Int32 } if source.format().bits() < 32)
    };
    let opaque_parts = tokens.iter().all(|token| {
        widening(token)
            || matches!(
                token,
                Token::Constant(_)
                    | Token::Read(_)
                    | Token::Variable(_)
                    | Token::Narrow64Variable(_)
                    | Token::Narrow64Expression
                    | Token::NativeConstant(_)
                    | Token::NativeBinary(_)
                    | Token::PureFunction { .. }
            )
    });
    let opaque_root = (matches!(
        tokens.first(),
        Some(
            Token::Variable(_)
                | Token::Read(_)
                | Token::Narrow64Variable(_)
                | Token::Narrow64Expression
                | Token::PureFunction { .. }
        )
    ) || tokens.first().is_some_and(widening))
        && opaque_parts;
    let small_word_literal = tokens
        .iter()
        .any(|token| matches!(token, Token::Constant(value) if *value <= 31));
    let mut pending = Vec::new();
    for token in tokens.into_iter().rev() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        let key = match token {
            Token::Constant(bits) => constant(bits),
            Token::Read(read) => read,
            Token::Variable(value) => variable(value),
            Token::Narrow64Variable(value) => low_word(variable(value)),
            Token::Narrow64Expression => low_word(pending.pop()?),
            Token::NativeConstant(bits) => {
                KernelTermImport::default().machine(T::UInt64, &MachineTerm::uint64_constant(bits))
            }
            Token::Binary(BitvectorBinaryOp::Machine(format, operator))
            | Token::NativeBinary(BitvectorBinaryOp::Machine(format, operator)) => {
                let left = pending.pop()?;
                let right = pending.pop()?;
                KernelTerm::machine_binary_shared(format, operator, [left, right])
            }
            Token::Binary(_) | Token::NativeBinary(_) => return None,
            Token::UnaryNot => KernelTerm::machine_unary_shared(
                T::Int32,
                MachineUnaryOp::BitwiseNot,
                pending.pop()?,
            ),
            Token::Cast {
                source,
                destination,
            } => KernelTerm::machine_cast_shared(
                MachineCastSpelling::Generic,
                source,
                destination,
                pending.pop()?,
            ),
            Token::PureFunction { name, arity } => {
                let arguments = (0..arity)
                    .map(|_| pending.pop())
                    .collect::<Option<Vec<_>>>()?;
                KernelTerm::checked_call(KernelType::C(T::Int32.c_type()), name, arguments)
            }
        };
        pending.push(key);
    }
    let key = pending.pop()?;
    pending.is_empty().then_some(SignedArithmeticAtom {
        key,
        opaque_root,
        opaque_parts,
        small_word_literal,
    })
}

pub(super) fn remainder(base: &SignedArithmeticAtom, divisor: u32) -> SignedArithmeticAtom {
    SignedArithmeticAtom {
        key: KernelTerm::machine_binary_shared(
            T::Int32,
            MachineBinaryOp::Remainder,
            [base.key.clone(), constant(divisor)],
        ),
        opaque_root: false,
        opaque_parts: false,
        small_word_literal: base.small_word_literal || divisor <= 31,
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Reading {
    Signed,
    Native,
}
thread_local! {
    static KEYS: std::cell::RefCell<HashMap<(u64, Reading), Option<SignedArithmeticAtom>>> = Default::default();
    static CANONICAL: std::cell::RefCell<HashMap<u64, KernelTerm>> = Default::default();
}
pub(super) fn clear() {
    KEYS.with(|keys| keys.borrow_mut().clear());
    CANONICAL.with(|keys| keys.borrow_mut().clear());
}
#[cfg(test)]
pub(super) fn cache_len() -> usize {
    KEYS.with(|keys| keys.borrow().len())
}

#[derive(Clone)]
enum Head {
    Variable(Variable),
    Read(KernelTerm),
    Constant(u32),
    NativeConstant(u64),
    Binary(T, MachineBinaryOp),
    Not,
    LowWord,
    Cast(T, T),
}
fn shape(term: &KernelTerm, reading: Reading) -> Option<(Head, Vec<(&KernelTerm, Reading)>)> {
    use crate::kernel::MachineOperandView as V;
    use KernelTermNode as N;
    let child = |value| vec![(value, reading)];
    match term.node() {
        N::Variable(value) => Some((Head::Variable(*value), vec![])),
        N::MemoryLoad { .. } => Some((Head::Read(term.clone()), vec![])),
        N::MachineLiteral(_) => {
            let literal = V::Shared(term).literal()?;
            match reading {
                Reading::Signed => Some((Head::Constant(literal.constant32()?), vec![])),
                Reading::Native => Some((Head::NativeConstant(literal.uint64_as_const()?), vec![])),
            }
        }
        N::MachineBinary {
            format,
            operator,
            arguments,
        } => {
            let supported = match reading {
                Reading::Signed => {
                    *format == T::Int32
                        || (*format == T::UInt32 && *operator == MachineBinaryOp::ShiftRight)
                }
                Reading::Native => {
                    *format == T::UInt64
                        && matches!(
                            operator,
                            MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply
                                | MachineBinaryOp::Divide
                                | MachineBinaryOp::Remainder
                        )
                }
            };
            supported.then(|| {
                (
                    Head::Binary(*format, *operator),
                    arguments.iter().map(|v| (v, reading)).collect(),
                )
            })
        }
        N::MachineUnary {
            format: T::Int32,
            operator: MachineUnaryOp::BitwiseNot,
            operand,
        } if reading == Reading::Signed => Some((Head::Not, child(operand))),
        N::MachineCast {
            encoding: MachineCastSpelling::UInt32From64,
            operand,
            ..
        } if reading == Reading::Signed => Some((Head::LowWord, vec![(operand, Reading::Native)])),
        N::MachineCast {
            encoding: MachineCastSpelling::Generic,
            source,
            destination,
            operand,
        } if reading == Reading::Signed => {
            if *destination == T::Int32
                && let N::MachineCast {
                    encoding: MachineCastSpelling::Generic,
                    source: inner_source,
                    destination: inner_destination,
                    operand: inner,
                } = operand.node()
                && source == inner_destination
                && narrowed_word_cast(*inner_source, *inner_destination)
            {
                return Some((Head::Cast(*inner_source, *inner_destination), child(inner)));
            }
            ((*destination == T::Int32 && source.format().bits() < 32)
                || crate::kernel::is_sign_cast32(*source, *destination))
            .then(|| (Head::Cast(*source, *destination), child(operand)))
        }
        _ => None,
    }
}

pub(super) fn from_shared(root: &KernelTerm) -> Option<SignedArithmeticAtom> {
    KEYS.with(|keys| {
        let mut keys = keys.borrow_mut();
        let mut pending = vec![(root, Reading::Signed, false)];
        while let Some((term, reading, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            let key = (term.id(), reading);
            if keys.contains_key(&key) {
                continue;
            }
            let Some((head, children)) = shape(term, reading) else {
                keys.insert(key, None);
                continue;
            };
            if !finish && !children.is_empty() {
                pending.push((term, reading, true));
                pending.extend(children.iter().map(|(child, mode)| (*child, *mode, false)));
                continue;
            }
            let operands = children
                .iter()
                .map(|(child, mode)| keys[&(child.id(), *mode)].clone())
                .collect::<Option<Vec<_>>>();
            let Some(operands) = operands else {
                keys.insert(key, None);
                continue;
            };
            let all_parts = operands.iter().all(|operand| operand.opaque_parts);
            let small_word_literal = matches!(&head, Head::Constant(value) if *value <= 31)
                || operands.iter().any(|operand| operand.small_word_literal);
            let (node, root_opaque, parts) = match head {
                Head::Variable(v) => (variable(v), true, true),
                Head::Read(read) => (read.with_machine_observation_type(T::Int32), true, true),
                Head::Constant(v) => (constant(v), false, true),
                Head::NativeConstant(v) => (
                    KernelTermImport::default()
                        .machine(T::UInt64, &MachineTerm::uint64_constant(v)),
                    false,
                    true,
                ),
                Head::Binary(format, operator) => (
                    KernelTerm::machine_binary_shared(
                        format,
                        operator,
                        [operands[0].key.clone(), operands[1].key.clone()],
                    ),
                    false,
                    reading == Reading::Native && all_parts,
                ),
                Head::Not => (
                    KernelTerm::machine_unary_shared(
                        T::Int32,
                        MachineUnaryOp::BitwiseNot,
                        operands[0].key.clone(),
                    ),
                    false,
                    false,
                ),
                Head::LowWord => (low_word(operands[0].key.clone()), true, all_parts),
                Head::Cast(source, destination) => {
                    let widening = destination == T::Int32 && source.format().bits() < 32;
                    (
                        KernelTerm::machine_cast_shared(
                            MachineCastSpelling::Generic,
                            source,
                            destination,
                            operands[0].key.clone(),
                        ),
                        widening,
                        widening && all_parts,
                    )
                }
            };
            keys.insert(
                key,
                Some(SignedArithmeticAtom {
                    key: node,
                    opaque_root: root_opaque && parts,
                    opaque_parts: parts,
                    small_word_literal,
                }),
            );
        }
        keys[&(root.id(), Reading::Signed)].clone()
    })
}

/// The legacy canonicalizer keeps arithmetic operators raw and composes only
/// generic casts. Shared machine operands already name their loads. Integer
/// conversion leaves are opaque to both canonicalization passes and outside
/// this certificate's atom grammar, so they are refused without an export.
fn canonical_arithmetic(root: &KernelTerm) -> Option<KernelTerm> {
    if root.has_machine_conversions() {
        return None;
    }
    CANONICAL.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![(root, false)];
        while let Some((term, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            if cache.contains_key(&term.id()) {
                continue;
            }
            let children: Vec<_> = match term.node() {
                KernelTermNode::MachineBinary { arguments, .. } => arguments.iter().collect(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand],
                _ => vec![],
            };
            if !finish && !children.is_empty() {
                pending.push((term, true));
                pending.extend(children.into_iter().map(|child| (child, false)));
                continue;
            }
            let value = match term.node() {
                KernelTermNode::Variable(_)
                | KernelTermNode::MachineLiteral(_)
                | KernelTermNode::MemoryLoad { .. } => term.clone(),
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => KernelTerm::machine_binary_shared(
                    *format,
                    *operator,
                    arguments.each_ref().map(|v| cache[&v.id()].clone()),
                ),
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } => KernelTerm::machine_unary_shared(
                    *format,
                    *operator,
                    cache[&operand.id()].clone(),
                ),
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    let operand = cache[&operand.id()].clone();
                    if *encoding == MachineCastSpelling::Generic {
                        operand.checking_machine_cast_preserving_sign_pairs(*source, *destination)
                    } else {
                        KernelTerm::machine_cast_shared(*encoding, *source, *destination, operand)
                    }
                }
                _ => return None,
            };
            cache.insert(term.id(), value);
        }
        Some(cache[&root.id()].clone())
    })
}

pub(super) fn from_observation(root: &KernelTerm, format: T) -> Option<SignedArithmeticAtom> {
    if format != T::Int32 && format.format().bits() >= 32 {
        return None;
    }
    let mut value = canonical_arithmetic(root)?;
    if format != T::Int32 {
        value = value.checking_machine_cast_preserving_sign_pairs(format, T::Int32);
    }
    from_shared(&value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, MachineOperandView, VerificationSession};

    #[test]
    fn shared_atom_keys_preserve_native_cast_width_and_opaque_rules() {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1006400));
        let cast = |source, destination, value| MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: source,
            to: destination,
            value: Box::new(value),
        };
        let mut terms = vec![
            (T::Int32, x.clone()),
            (T::UInt32, MachineTerm::uint32_constant(7)),
        ];
        for source in [
            T::Int8,
            T::UInt8,
            T::Int16,
            T::UInt16,
            T::Int32,
            T::UInt32,
            T::Int64,
            T::UInt64,
        ] {
            for destination in [T::Int8, T::UInt8, T::Int16, T::UInt16, T::Int32, T::UInt32] {
                let inner = cast(source, destination, x.clone());
                terms.push((destination, inner.clone()));
                terms.push((T::Int32, cast(destination, T::Int32, inner)));
            }
        }
        for format in [T::Int8, T::Int32, T::UInt32, T::Int64, T::UInt64] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
            ] {
                let node = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(x.clone()),
                    right: Box::new(if format == T::UInt64 {
                        MachineTerm::uint64_constant(3)
                    } else {
                        MachineTerm::constant(3)
                    }),
                };
                terms.push((format, node.clone()));
                terms.push((
                    T::UInt32,
                    MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(node)),
                ));
            }
        }
        terms.push((
            T::UInt32,
            MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(x)),
        ));
        for (format, native) in terms {
            let shared = KernelTermImport::default()
                .machine_arithmetic(format, &native)
                .unwrap();
            let expected = SignedArithmeticAtom::from_term(&native);
            let exports = KernelTermExport::machine_export_count();
            let actual = SignedArithmeticAtom::from_operand(MachineOperandView::Shared(&shared));
            assert_eq!(actual, expected, "{native:?}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let canonical = if format == T::Int32 {
                Some(crate::kernel::eval::canonical_term(&native))
            } else if format.format().bits() < 32 {
                Some(crate::kernel::eval::canonical_term(
                    &MachineTerm::machine_integer_cast(format, T::Int32, native.clone()),
                ))
            } else {
                None
            };
            let expected = canonical.as_ref().and_then(SignedArithmeticAtom::from_term);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                from_observation(&shared, format),
                expected,
                "canonical {format:?}: {native:?}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    fn observed_result(root: KernelTerm, format: T) -> Proposition {
        use crate::kernel::{IntegerTerm, SharedMachineIntegerTerm};
        let observation = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(
                format,
                root.with_machine_observation_type(format),
            )
            .unwrap(),
        );
        Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(observation, IntegerTerm::constant_i64(0)),
            true,
        )
    }

    #[test]
    fn mathematical_results_keep_unsigned_and_conversion_refusals_without_exports() {
        let _session = VerificationSession::enter();
        let variable = variable(Variable(1006403));
        let converted = KernelTerm::integer_to_machine(
            T::Int32,
            KernelTerm::variable(KernelType::Integer, Variable(1006404)),
        )
        .unwrap();
        let native = KernelTermExport::machine(&converted).unwrap();
        assert!(
            SignedArithmeticAtom::from_term(&crate::kernel::eval::canonical_term(&native))
                .is_none()
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(
            signed_arithmetic_integer_result(&observed_result(variable.clone(), T::UInt32))
                .is_none()
        );
        assert!(
            signed_arithmetic_integer_result(&observed_result(converted.clone(), T::Int32))
                .is_none()
        );
        let composite = KernelTerm::machine_binary_shared(
            T::Int32,
            MachineBinaryOp::Add,
            [converted, variable.clone()],
        );
        assert!(signed_arithmetic_integer_result(&observed_result(composite, T::Int32)).is_none());
        let claim = signed_arithmetic_integer_result(&observed_result(variable, T::Int16)).unwrap();
        assert_eq!(claim.terms.len(), 1);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn native_pure_application_keys_retain_argument_order() {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1006400));
        let y = MachineTerm::Variable(Variable(1006401));
        let call = |arguments| MachineTerm::PureFunctionApplication {
            name: "f".into(),
            arguments,
        };
        let first = SignedArithmeticAtom::from_term(&call(vec![x.clone(), y.clone()])).unwrap();
        let second = SignedArithmeticAtom::from_term(&call(vec![y, x])).unwrap();
        assert!(first.is_opaque_root());
        assert_ne!(first, second);
    }

    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/signed_arithmetic/atom_keys.rs");
    }
}
