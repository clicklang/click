//! Checking-only arithmetic reconstruction over shared machine operands.
//! This is not lowering: stored operands keep their exact syntax.
use super::*;

thread_local! {
    static BINARY_RESULTS: std::cell::RefCell<HashMap<(MachineIntegerType, MachineBinaryOp, u64, u64), KernelTerm>> = Default::default();
    static COMPARISON_OPERANDS: std::cell::RefCell<HashMap<u64, KernelTerm>> = Default::default();
}

pub(super) fn clear() {
    BINARY_RESULTS.with(|cache| cache.borrow_mut().clear());
    COMPARISON_OPERANDS.with(|cache| cache.borrow_mut().clear());
}

impl TermRewrite<'_> {
    pub(super) fn comparison_operand(&mut self, root: &KernelTerm) -> Option<KernelTerm> {
        // Only the ordinary comparison scope may share work between queries.
        // A nested binder's renamed/opaque reads use this traversal's own memo.
        let cacheable = self.resolve_registered_loads
            && self.scope.c.iter().all(|(a, b)| a == b)
            && self.scope.integer.iter().all(|(a, b)| a == b)
            && self.scope.algebraic.iter().all(|(a, b)| a == b);
        let local = std::cell::RefCell::new(HashMap::<u64, KernelTerm>::new());
        let get = |term: &KernelTerm| {
            local.borrow().get(&term.id()).cloned().or_else(|| {
                cacheable
                    .then(|| {
                        COMPARISON_OPERANDS.with(|cache| cache.borrow().get(&term.id()).cloned())
                    })
                    .flatten()
            })
        };
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, finish)) = pending.pop() {
            self.visit();
            if self.checked_work_exhausted() {
                return None;
            }
            if get(&term).is_some() {
                continue;
            }
            let children: Vec<_> = match term.node() {
                KernelTermNode::MachineBinary { arguments, .. } => arguments.to_vec(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand.clone()],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term.clone(), true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let KernelType::C(ty) = term.ty() else {
                return None;
            };
            let format = MachineIntegerType::from_c_type(*ty)?;
            let value = match term.node() {
                KernelTermNode::Variable(variable) => {
                    let rewritten = self.bits(&MachineTerm::Variable(*variable));
                    KernelTermImport::default().machine_arithmetic(format, &rewritten)?
                }
                KernelTermNode::MachineLiteral(_) => term.clone(),
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => {
                    let [left, right] = arguments
                        .each_ref()
                        .map(|arg| get(arg).expect("visited operand"));
                    comparison_binary(*format, *operator, left, right)
                }
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } => {
                    let operand = get(operand).expect("visited operand");
                    let operand = if matches!(
                        format,
                        MachineIntegerType::Int32 | MachineIntegerType::UInt32
                    ) && let Some(value) = literal(&operand)
                    {
                        imported(*format, value.constant_word32())
                    } else {
                        operand
                    };
                    KernelTerm::machine_unary_shared(*format, *operator, operand)
                }
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    let operand = get(operand).expect("visited operand");
                    if *encoding == MachineCastSpelling::Generic {
                        operand.checking_machine_cast_preserving_sign_pairs(*source, *destination)
                    } else if encoding.unary(*source, *destination).is_width_conversion() {
                        operand.checking_legacy_machine_conversion(*source, *destination)
                    } else {
                        KernelTerm::machine_cast_shared(*encoding, *source, *destination, operand)
                    }
                }
                _ => return None,
            }
            .with_machine_observation_type(format);
            if crate::instrumentation::deadline_exceeded_with_work(0) {
                self.integer_work_exhausted = true;
            }
            if self.refusal().is_some() {
                return None;
            }
            local.borrow_mut().insert(term.id(), value.clone());
            if cacheable {
                COMPARISON_OPERANDS.with(|cache| cache.borrow_mut().insert(term.id(), value));
            }
        }
        get(root)
    }
}

fn literal(term: &KernelTerm) -> Option<MachineTerm> {
    MachineOperandView::Shared(term).literal()
}
fn imported(format: MachineIntegerType, value: MachineTerm) -> KernelTerm {
    KernelTermImport::default()
        .machine_arithmetic(format, &value)
        .expect("machine arithmetic result")
}
fn constant(format: MachineIntegerType, value: u32) -> KernelTerm {
    imported(
        format,
        crate::kernel::machine_integer::range::constant_word(format, &value.into())
            .expect("small constant"),
    )
}
fn word(term: &KernelTerm) -> Option<u32> {
    literal(term)?.as_const()
}
fn binary<'a>(
    term: &'a KernelTerm,
    format: MachineIntegerType,
    op: MachineBinaryOp,
) -> Option<&'a [KernelTerm; 2]> {
    match term.node() {
        KernelTermNode::MachineBinary {
            format: found,
            operator,
            arguments,
        } if *found == format && *operator == op => Some(arguments),
        _ => None,
    }
}
fn comparison_binary(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    let key = (format, op, left.id(), right.id());
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return KernelTerm::machine_binary_shared(format, op, [left, right]);
    }
    if let Some(result) = BINARY_RESULTS.with(|cache| cache.borrow().get(&key).cloned()) {
        return result;
    }
    let result = comparison_binary_uncached(format, op, left, right);
    if !crate::instrumentation::deadline_exceeded_with_work(0) {
        BINARY_RESULTS.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    }
    result
}

fn comparison_binary_uncached(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    let word32 = matches!(format, T::Int32 | T::UInt32);
    let restyle = |term: KernelTerm| {
        if word32 && let Some(value) = literal(&term) {
            imported(format, value.constant_in32(format))
        } else {
            term.with_machine_observation_type(format)
        }
    };
    let (left, right) = (restyle(left), restyle(right));
    let raw = |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
    if op == O::Subtract && left == right {
        return constant(format, 0);
    }
    if !matches!(
        op,
        O::Add
            | O::Subtract
            | O::Multiply
            | O::Divide
            | O::Remainder
            | O::ShiftLeft
            | O::ShiftRight
    ) {
        return raw(left, right);
    }
    // Reuse the established evaluator only for two fixed-size literal leaves.
    // No symbolic child is exported or temporarily represented as a native tree.
    if let (Some(a), Some(b)) = (literal(&left), literal(&right)) {
        return imported(format, MachineTerm::machine_binary(format, op, a, b));
    }
    if word32 {
        match op {
            O::Add => {
                for (a, b) in [(&left, &right), (&right, &left)] {
                    if let Some([base, taken]) = binary(b, format, O::Subtract)
                        && taken == a
                    {
                        return base.clone();
                    }
                    if let (Some([zero, taken]), Some([first, second])) =
                        (binary(a, format, O::Subtract), binary(b, format, O::Add))
                        && word(zero) == Some(0)
                    {
                        if taken == first {
                            return second.clone();
                        }
                        if taken == second {
                            return first.clone();
                        }
                    }
                }
                if word(&right) == Some(0) {
                    return left;
                }
                if word(&left) == Some(0) {
                    return right;
                }
            }
            O::Subtract => {
                if word(&right) == Some(0) {
                    return left;
                }
                let (a, b) = (
                    binary(&left, format, O::Add),
                    binary(&right, format, O::Add),
                );
                if let (Some([a0, a1]), Some([b0, b1])) = (a, b) {
                    for (x, rest, y, other) in [
                        (a0, a1, b0, b1),
                        (a0, a1, b1, b0),
                        (a1, a0, b0, b1),
                        (a1, a0, b1, b0),
                    ] {
                        if x == y {
                            return comparison_binary(format, op, rest.clone(), other.clone());
                        }
                    }
                }
                if let Some([a, b]) = a {
                    if *a == right {
                        return b.clone();
                    }
                    if *b == right {
                        return a.clone();
                    }
                }
                if let Some([a, b]) = b {
                    if left == *a {
                        return comparison_binary(format, op, constant(format, 0), b.clone());
                    }
                    if left == *b {
                        return comparison_binary(format, op, constant(format, 0), a.clone());
                    }
                }
            }
            O::Multiply => {
                if word(&right) == Some(1) {
                    return left;
                }
                if word(&left) == Some(1) {
                    return right;
                }
                if word(&left) == Some(0) || word(&right) == Some(0) {
                    return constant(format, 0);
                }
            }
            O::Divide if word(&right) == Some(1) => return left,
            O::ShiftRight if word(&right) == Some(0) => return left,
            O::ShiftLeft if format == T::UInt32 && word(&right) == Some(0) => return left,
            _ => {}
        }
    } else if matches!(format, T::Int64 | T::UInt64) {
        let numeric = |term: &KernelTerm| {
            literal(term)
                .and_then(|value| format.constant_from_term(&value))
                .and_then(|value| value.to_i128())
        };
        if op == O::Multiply {
            if numeric(&right) == Some(1) {
                return left;
            }
            if numeric(&left) == Some(1) {
                return right;
            }
            if numeric(&left) == Some(0) || numeric(&right) == Some(0) {
                return constant(format, 0);
            }
        }
        if format == T::UInt64 {
            if matches!(op, O::Add | O::Subtract) && numeric(&right) == Some(0) {
                return left;
            }
            if op == O::Add && numeric(&left) == Some(0) {
                return right;
            }
            let inverse = match op {
                O::Add => Some(O::Subtract),
                O::Subtract => Some(O::Add),
                _ => None,
            };
            if let Some(inverse) = inverse
                && let Some([base, taken]) = binary(&left, format, inverse)
                && numeric(&right).is_some()
                && numeric(&right) == numeric(taken)
            {
                return base.clone();
            }
        }
    }
    raw(left, right)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_comparison_reconstruction_matches_native_casts() {
        let _session = crate::kernel::VerificationSession::enter();
        let formats = [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        for source in formats {
            for destination in formats {
                for inner in [
                    MachineTerm::Variable(Variable(992100)),
                    crate::kernel::machine_integer::range::constant_word(source, &1.into())
                        .unwrap(),
                ] {
                    for native in [
                        MachineTerm::Cast {
                            spelling: MachineCastSpelling::Generic,
                            from: source,
                            to: destination,
                            value: Box::new(inner.clone()),
                        },
                        MachineTerm::machine_integer_cast(source, destination, inner.clone()),
                        MachineTerm::Cast {
                            spelling: MachineCastSpelling::Generic,
                            from: source,
                            to: destination,
                            value: Box::new(MachineTerm::Cast {
                                spelling: MachineCastSpelling::Generic,
                                from: destination,
                                to: source,
                                value: Box::new(MachineTerm::Variable(Variable(992101))),
                            }),
                        },
                    ] {
                        let expected = TermRewrite::for_arithmetic_comparison().bits(&native);
                        let root = imported(destination, native.clone());
                        let exports = KernelTermExport::machine_export_count();
                        let actual = TermRewrite::for_arithmetic_comparison()
                            .comparison_operand(&root)
                            .unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(actual, imported(destination, expected), "{native:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn shared_comparison_reconstruction_matches_native_arithmetic() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let x = MachineTerm::Variable(Variable(992001));
            let y = MachineTerm::Variable(Variable(992002));
            let zero =
                crate::kernel::machine_integer::range::constant_word(format, &0.into()).unwrap();
            let one =
                crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap();
            let make = |op, a: MachineTerm, b: MachineTerm| MachineTerm::Binary {
                format,
                op,
                left: Box::new(a),
                right: Box::new(b),
            };
            let add = make(MachineBinaryOp::Add, x.clone(), y.clone());
            let sub = make(MachineBinaryOp::Subtract, x.clone(), y.clone());
            let neg = make(MachineBinaryOp::Subtract, zero.clone(), x.clone());
            let cases = [x.clone(), y, zero, one, add, sub, neg];
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
            ] {
                for left in &cases {
                    for right in &cases {
                        let native = make(op, left.clone(), right.clone());
                        let expected = TermRewrite::for_arithmetic_comparison().bits(&native);
                        let root = imported(format, native);
                        let exports = KernelTermExport::machine_export_count();
                        let result = TermRewrite::for_arithmetic_comparison()
                            .comparison_operand(&root)
                            .unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(
                            result,
                            imported(format, expected),
                            "{format:?} {op:?}: {left:?} {right:?}"
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/proof/shared_comparison.rs");
}
