//! Fact-free checking readings of wide arithmetic. Stored syntax is unchanged.
use super::shared_comparison::{binary, imported, literal};
use super::*;

thread_local! {
    static READINGS: std::cell::RefCell<HashMap<u64, KernelTerm>> = Default::default();
    static BINARIES: std::cell::RefCell<HashMap<(MachineIntegerType, MachineBinaryOp, u64, u64), KernelTerm>> = Default::default();
}
pub(super) fn clear() {
    READINGS.with(|cache| cache.borrow_mut().clear());
    BINARIES.with(|cache| cache.borrow_mut().clear());
}

impl TermRewrite<'_> {
    /// Iterative, session-memoized syntax work. Casts and non-wide nodes remain
    /// explicit boundaries; their fact-dependent readings belong to the caller.
    pub(in crate::kernel) fn checking_wide_syntax(root: &KernelTerm) -> KernelTerm {
        let get =
            |term: &KernelTerm| READINGS.with(|cache| cache.borrow().get(&term.id()).cloned());
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return root.clone();
            }
            if get(&term).is_some() {
                continue;
            }
            let children = match term.node() {
                KernelTermNode::MachineBinary {
                    format: MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                    arguments,
                    ..
                } => arguments.to_vec(),
                KernelTermNode::MachineUnary {
                    format: MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                    operand,
                    ..
                } => vec![operand.clone()],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term, true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let result = match term.node() {
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } if format.format().bits() == 64 => binary_read(
                    *format,
                    *operator,
                    get(&arguments[0]).unwrap(),
                    get(&arguments[1]).unwrap(),
                ),
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } if format.format().bits() == 64 => {
                    let operand = get(operand).unwrap();
                    match literal(&operand) {
                        Some(value) => imported(
                            *format,
                            MachineTerm::machine_unary(*format, *operator, value),
                        ),
                        None => KernelTerm::machine_unary_shared(*format, *operator, operand),
                    }
                }
                _ => term.clone(),
            };
            let result = result.with_machine_observation_type(
                MachineIntegerType::from_program_type(match term.ty() {
                    KernelType::Program(ty) => *ty,
                    _ => unreachable!("machine operand"),
                })
                .expect("machine operand type"),
            );
            READINGS.with(|cache| cache.borrow_mut().insert(term.id(), result));
        }
        get(root).unwrap()
    }
}

fn wide(term: &KernelTerm) -> Option<u64> {
    MachineOperandView::Shared(term).uint64_constant()
}
fn word(value: u64) -> KernelTerm {
    imported(
        MachineIntegerType::UInt64,
        MachineTerm::uint64_constant(value),
    )
}
fn binary_read(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    let key = (format, op, left.id(), right.id());
    if let Some(result) = BINARIES.with(|cache| cache.borrow().get(&key).cloned()) {
        return result;
    }
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return KernelTerm::machine_binary_shared(format, op, [left, right]);
    }
    let result = binary_uncached(format, op, left, right);
    if !crate::instrumentation::deadline_exceeded_with_work(0) {
        BINARIES.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    }
    result
}
fn binary_uncached(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    let raw = |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
    if let (Some(a), Some(b)) = (literal(&left), literal(&right)) {
        return imported(format, MachineTerm::machine_binary(format, op, a, b));
    }
    // Preserve the native constructor's atomic-only unsigned subtraction rule.
    if op == O::Subtract
        && left == right
        && (format == T::Int64 || MachineOperandView::Shared(&left).variable().is_some())
    {
        return imported(
            format,
            if format == T::Int64 {
                MachineTerm::int64_constant(0)
            } else {
                MachineTerm::uint64_constant(0)
            },
        );
    }
    if op == O::Multiply {
        let number = |term: &KernelTerm| {
            literal(term)
                .and_then(|v| format.constant_from_term(&v))
                .and_then(|v| v.to_i128())
        };
        if number(&left) == Some(1) {
            return right;
        }
        if number(&right) == Some(1) {
            return left;
        }
        if number(&left) == Some(0) || number(&right) == Some(0) {
            return imported(
                format,
                if format == T::Int64 {
                    MachineTerm::int64_constant(0)
                } else {
                    MachineTerm::uint64_constant(0)
                },
            );
        }
    }
    if format != T::UInt64 {
        return raw(left, right);
    }
    match op {
        O::Add | O::Subtract => {
            if wide(&right) == Some(0) {
                return left;
            }
            if op == O::Add && wide(&left) == Some(0) {
                return right;
            }
            let inverse = if op == O::Add { O::Subtract } else { O::Add };
            if let Some([base, taken]) = binary(&left, format, inverse)
                && wide(&right).is_some()
                && wide(&right) == wide(taken)
            {
                return base.clone();
            }
        }
        O::BitwiseAnd => {
            if wide(&left) == Some(0) || wide(&right) == Some(0) {
                return word(0);
            }
            if let Some(mask) = wide(&right) {
                for inner_op in [O::BitwiseAnd, O::BitwiseOr] {
                    if let Some([a, b]) = binary(&left, format, inner_op) {
                        let selected = match (wide(a), wide(b)) {
                            (None, Some(c)) => Some((a, c)),
                            (Some(c), None) => Some((b, c)),
                            _ => None,
                        };
                        if let Some((base, c)) = selected {
                            if inner_op == O::BitwiseAnd {
                                return binary_read(format, op, base.clone(), word(c & mask));
                            }
                            let masked =
                                binary_read(format, O::BitwiseAnd, base.clone(), word(mask));
                            return binary_read(format, O::BitwiseOr, masked, word(c & mask));
                        }
                    }
                }
            }
        }
        O::BitwiseOr => {
            if let Some(c) = wide(&right)
                && let Some([a, b]) = binary(&left, format, O::BitwiseAnd)
                && let Some(mask) = wide(a).or_else(|| wide(b))
                && mask & !c == 0
            {
                return word(c);
            }
            if wide(&left) == Some(0) {
                return right;
            }
            if wide(&right) == Some(0) {
                return left;
            }
        }
        _ => {}
    }
    raw(left, right)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wide_checking_syntax_preserves_native_constructor_readings() {
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let context = PureFactContext::new();
            let x = MachineTerm::Variable(Variable(989601));
            let y = MachineTerm::Variable(Variable(989602));
            let literal = |v: i64| {
                crate::kernel::machine_integer::range::constant_word(format, &v.into()).unwrap()
            };
            let binary = |op, a: MachineTerm, b: MachineTerm| MachineTerm::Binary {
                format,
                op,
                left: a.into(),
                right: b.into(),
            };
            let zero = literal(0);
            let one = literal(1);
            let three = literal(3);
            let seven = literal(7);
            let mut inputs = vec![
                x.clone(),
                y.clone(),
                zero.clone(),
                one.clone(),
                three.clone(),
                seven,
            ];
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
            ] {
                inputs.push(binary(op, x.clone(), three.clone()));
                inputs.push(binary(op, three.clone(), x.clone()));
            }
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                for left in &inputs {
                    for right in &inputs {
                        let native = binary(op, left.clone(), right.clone());
                        let root = imported(format, native.clone());
                        let expected = context.simplify_bitvector_under_assumptions(&native);
                        let exports = KernelTermExport::machine_export_count();
                        let actual = TermRewrite::checking_wide_syntax(&root);
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(
                            actual,
                            imported(format, expected),
                            "{format:?} {op:?}: {left:?}, {right:?}"
                        );
                        // A checking reading never replaces the written term.
                        assert_eq!(root, imported(format, native));
                    }
                }
            }
        }
    }

    #[test]
    fn wide_checking_unary_readings_preserve_observation_signedness() {
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            for observed in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
                for value in [
                    MachineTerm::Variable(Variable(989612)),
                    MachineTerm::int64_constant(0),
                    MachineTerm::uint64_constant(1),
                ] {
                    let native = MachineTerm::Unary {
                        format,
                        op: MachineUnaryOp::BitwiseNot,
                        operand: value.into(),
                    };
                    let root = imported(observed, native.clone());
                    let expected =
                        PureFactContext::new().simplify_bitvector_under_assumptions(&native);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        TermRewrite::checking_wide_syntax(&root),
                        imported(observed, expected)
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn wide_checking_masks_decide_without_exporting_the_shared_tree() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let x = imported(format, MachineTerm::Variable(Variable(989611)));
        let raw = |op, a, b| KernelTerm::machine_binary_shared(format, op, [a, b]);
        let masked = raw(MachineBinaryOp::BitwiseAnd, x.clone(), word(1));
        let tagged = raw(MachineBinaryOp::BitwiseOr, masked, word(3));
        let cleared = raw(MachineBinaryOp::BitwiseAnd, tagged, word(!3));
        let observed =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, cleared).unwrap());
        let exports = KernelTermExport::machine_export_count();
        for (value, expected) in [(0, true), (1, false)] {
            let goal =
                ConditionTerm::integer_equal(observed.clone(), IntegerTerm::constant_i64(value));
            assert_eq!(PureFactContext::new().decide(&goal), Some(expected));
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
