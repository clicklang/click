//! Numeric identity of retained machine observations. Exact producer payloads
//! remain untouched; opaque leaves use the existing native observation key.
use super::*;

thread_local! {
    static ROOTS: std::cell::RefCell<crate::id_hash::U64Map<KernelTerm>> = Default::default();
}
pub(super) fn clear() {
    ROOTS.with(|roots| roots.borrow_mut().clear());
}

// Boolean guard imports can contain exact generic machine payloads. They
// are numeric observation leaves here, without changing the producer's node
// or admitting arbitrary legacy payloads into the machine operand API.
fn machine_payload(term: &KernelTerm) -> Option<&MachineTerm> {
    if let KernelTermNode::Legacy(value) = term.node()
        && let PureFunctionArgument::Value(value) = value.value()
    {
        return match value {
            ProgramValue::Int8(value)
            | ProgramValue::UInt8(value)
            | ProgramValue::Int16(value)
            | ProgramValue::UInt16(value)
            | ProgramValue::Int32(value)
            | ProgramValue::UInt32(value)
            | ProgramValue::Int64(value)
            | ProgramValue::UInt64(value)
            | ProgramValue::Int128(value)
            | ProgramValue::UInt128(value) => Some(value),
            _ => None,
        };
    }
    term.machine_conversion_leaf()
}

pub(super) fn normalize(root: &KernelTerm) -> KernelTerm {
    if !root.has_opaque_observation_boundary() {
        return root.clone();
    }
    ROOTS.with(|roots| {
        // Key construction may observe a nested call argument recursively.
        // Keep every cache borrow inside its lookup/update, never across the
        // interner or a child reconstruction callback.
        let get = |term: &KernelTerm| roots.borrow()[&term.id()].clone();
        let mut pending = vec![(root.clone(), false)];
        let mut expanded = HashMap::new();
        while let Some((term, finish)) = pending.pop() {
            if roots.borrow().contains_key(&term.id()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if !term.has_opaque_observation_boundary() {
                roots.borrow_mut().insert(term.id(), term);
                continue;
            }
            let format = match term.ty() {
                KernelType::Program(ty) => {
                    MachineIntegerType::from_c_type(*ty).unwrap_or(MachineIntegerType::UInt8)
                }
                _ => MachineIntegerType::UInt8,
            };
            if !finish
                && matches!(term.node(), KernelTermNode::Legacy(_))
                && machine_payload(&term).is_some()
            {
                let value = machine_payload(&term).expect("retained machine leaf");
                let view = MachineOperandView::Legacy(value);
                if view.binary().is_some()
                    || view.unary().is_some()
                    || view.cast().is_some()
                    || matches!(
                        value,
                        MachineTerm::If { .. } | MachineTerm::AlgebraicMatch { .. }
                    )
                {
                    let replacement = KernelTerm::retained_machine_operand(format, view);
                    expanded.insert(term.id(), replacement.clone());
                    pending.push((term, true));
                    pending.push((replacement, false));
                    continue;
                }
            }
            if let Some(replacement) = expanded.remove(&term.id()) {
                let normalized = get(&replacement);
                roots.borrow_mut().insert(term.id(), normalized);
                continue;
            }
            let children = match term.node() {
                KernelTermNode::Match(matched) => matched
                    .arguments
                    .iter()
                    .chain(matched.arms.iter().flat_map(|arm| arm.bindings.iter()))
                    .cloned()
                    .collect(),
                KernelTermNode::Fold(fold) => fold.arguments.to_vec(),
                KernelTermNode::MachineBinary { arguments, .. }
                | KernelTermNode::BoolCompare { arguments, .. }
                | KernelTermNode::IntegerCompare { arguments, .. }
                | KernelTermNode::BoolEqual { arguments } => arguments.to_vec(),
                KernelTermNode::MachineIf { arguments } | KernelTermNode::BoolIf { arguments } => {
                    arguments.to_vec()
                }
                KernelTermNode::IntegerOperation { arguments, .. } => arguments.clone(),
                KernelTermNode::Call { arguments, .. } => arguments.clone(),
                KernelTermNode::MachineObservation { operand, .. }
                | KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand.clone()],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term, true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let normalized = match term.node() {
                KernelTermNode::Match(matched) => {
                    let mut matched = matched.clone();
                    matched.arguments = matched.arguments.iter().map(|child| get(child)).collect();
                    for arm in &mut matched.arms {
                        arm.bindings = arm.bindings.iter().map(|child| get(child)).collect();
                    }
                    matched.into_term().with_machine_observation_type(format)
                }
                KernelTermNode::Fold(fold) => KernelFold {
                    index: fold.index,
                    accumulator: fold.accumulator,
                    item: fold.item,
                    arguments: fold.arguments.each_ref().map(|child| get(child)),
                }
                .into_term()
                .with_machine_observation_type(format),
                KernelTermNode::Legacy(_) | KernelTermNode::Call { .. }
                    if machine_payload(&term).is_some() =>
                {
                    let value = machine_payload(&term).expect("retained machine leaf");
                    let identity = SharedMachineIntegerTerm::intern_key(MachineIntegerKey::native(
                        format,
                        value.clone(),
                    ));
                    KernelTerm::machine_observation_leaf(format, value.clone(), identity)
                }
                KernelTermNode::Legacy(value) => {
                    KernelTerm::native_observation_leaf(value.value().clone())
                }
                KernelTermNode::LegacyBool(_) => {
                    let condition = KernelTermExport::condition(&term).expect("retained guard");
                    let identity = SharedMachineIntegerTerm::intern_key(MachineIntegerKey::native(
                        MachineIntegerType::UInt8,
                        MachineTerm::BoolCast {
                            to: MachineIntegerType::UInt8,
                            value: Box::new(condition.clone()),
                        },
                    ));
                    KernelTerm::bool_observation_leaf(condition, identity)
                }
                KernelTermNode::IntegerCompare {
                    operator,
                    arguments,
                } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::IntegerCompare {
                        operator: *operator,
                        arguments: arguments.each_ref().map(|arg| get(arg)),
                    },
                ),
                KernelTermNode::IntegerOperation {
                    operator,
                    arguments,
                } => KernelTerm::intern(
                    KernelType::Integer,
                    KernelTermNode::IntegerOperation {
                        operator: *operator,
                        arguments: arguments.iter().map(|arg| get(arg)).collect(),
                    },
                ),
                KernelTermNode::MachineObservation { format, operand } => KernelTerm::intern(
                    KernelType::Integer,
                    KernelTermNode::MachineObservation {
                        format: *format,
                        operand: get(operand),
                    },
                ),
                KernelTermNode::MachineIf { arguments } => {
                    KernelTerm::machine_if_shared(format, arguments.each_ref().map(|arg| get(arg)))
                }
                KernelTermNode::BoolIf { arguments } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolIf {
                        arguments: arguments.each_ref().map(|arg| get(arg)),
                    },
                ),
                KernelTermNode::BoolEqual { arguments } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolEqual {
                        arguments: arguments.each_ref().map(|arg| get(arg)),
                    },
                ),
                KernelTermNode::BoolCompare {
                    format,
                    relation,
                    arguments,
                } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolCompare {
                        format: *format,
                        relation: *relation,
                        arguments: arguments.each_ref().map(|arg| get(arg)),
                    },
                ),
                KernelTermNode::Call { name, arguments } if term.ty() == &KernelType::Bool => {
                    KernelTerm::intern(
                        KernelType::Bool,
                        KernelTermNode::Call {
                            name: name.clone(),
                            arguments: arguments.iter().map(|arg| get(arg)).collect(),
                        },
                    )
                }
                KernelTermNode::MachineBinary {
                    format: operation_format,
                    operator,
                    arguments,
                } => KernelTerm::machine_binary_shared_as(
                    format,
                    *operation_format,
                    *operator,
                    [get(&arguments[0]), get(&arguments[1])],
                ),
                KernelTermNode::MachineUnary {
                    format: operation_format,
                    operator,
                    operand,
                } => KernelTerm::machine_unary_shared(*operation_format, *operator, get(operand))
                    .with_machine_observation_type(format),
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    KernelTerm::machine_cast_shared(*encoding, *source, *destination, get(operand))
                        .with_machine_observation_type(format)
                }
                _ => term.clone(),
            };
            roots.borrow_mut().insert(term.id(), normalized);
        }
        get(root)
    })
}

#[cfg(test)]
mod recursive_call_tests {
    use super::*;

    #[test]
    fn mathematical_guards_normalize_nested_call_argument_carriers() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let argument = MachineTerm::constant(7);
        let shared = SharedMachineIntegerTerm::intern(format, argument.clone());
        let call = |argument| MachineTerm::ClickFunctionApplication {
            name: "math_guard_length".into(),
            arguments: vec![argument],
        };
        let native = call(PureFunctionArgument::Value(ProgramValue::UInt64(argument)));
        let retained = call(PureFunctionArgument::SharedMachine(shared));
        let guard = |call: &MachineTerm| {
            let observation = KernelTerm::intern(
                KernelType::Integer,
                KernelTermNode::MachineObservation {
                    format,
                    operand: KernelTermImport::default().machine(format, call),
                },
            );
            let difference = KernelTerm::integer_operation(
                KernelIntegerOperator::Subtract,
                vec![observation, KernelTerm::integer_literal(3.into())],
            )
            .unwrap();
            KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::IntegerCompare {
                    operator: IntegerComparisonOperator::LessThan,
                    arguments: [KernelTerm::integer_literal(1.into()), difference],
                },
            )
        };
        let native_guard = guard(&native);
        let shared_guard = guard(&retained);
        let native_written = KernelTermExport::condition(&native_guard).unwrap();
        let shared_written = KernelTermExport::condition(&shared_guard).unwrap();
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(normalize(&native_guard), normalize(&shared_guard));
        let conditional = |guard| {
            KernelTerm::machine_if_shared(
                format,
                [
                    guard,
                    KernelTermImport::default().machine(format, &MachineTerm::constant(48)),
                    KernelTermImport::default().machine(format, &MachineTerm::constant(49)),
                ],
            )
        };
        let a = SharedMachineIntegerTerm::observe_shared(format, conditional(native_guard.clone()))
            .unwrap();
        let b = SharedMachineIntegerTerm::observe_shared(format, conditional(shared_guard.clone()))
            .unwrap();
        assert_eq!(a, b);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            KernelTermExport::condition(&native_guard).unwrap(),
            native_written
        );
        assert_eq!(
            KernelTermExport::condition(&shared_guard).unwrap(),
            shared_written
        );
        let different = guard(&call(PureFunctionArgument::Value(ProgramValue::UInt64(
            MachineTerm::constant(8),
        ))));
        assert_ne!(normalize(&native_guard), normalize(&different));
    }

    #[test]
    fn observation_identity_allows_nested_shared_opaque_call_arguments() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let call = |name: &str, arguments| MachineTerm::ClickFunctionApplication {
            name: name.into(),
            arguments,
        };
        let inner = call("opaque_nested_argument", vec![]);
        let inner_root = KernelTerm::retained_native_machine_operand(format, &inner);
        let inner_argument = SharedMachineIntegerTerm::from_shared(format, inner_root).unwrap();
        let outer = call(
            "opaque_outer_application",
            vec![PureFunctionArgument::SharedMachine(inner_argument)],
        );
        let root = KernelTerm::retained_native_machine_operand(format, &outer);
        let exports = KernelTermExport::machine_export_count();
        let first = SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap();
        let repeated = SharedMachineIntegerTerm::observe_shared(format, root).unwrap();
        assert_eq!(first, repeated);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let native = SharedMachineIntegerTerm::intern(format, outer.clone());
        assert_eq!(first, native);
        assert_eq!(native.retained_written_operand(), Some(&outer));
    }

    #[test]
    fn opaque_call_identity_preserves_format_order_and_exact_argument_carriers() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let argument = MachineTerm::constant(7);
        let retained = SharedMachineIntegerTerm::intern(format, argument.clone());
        let call = |arguments| MachineTerm::ClickFunctionApplication {
            name: "exact_call_carriers".into(),
            arguments,
        };
        let native_argument = PureFunctionArgument::Value(ProgramValue::Int32(argument));
        let shared_argument = PureFunctionArgument::SharedMachine(retained);
        let marker = PureFunctionArgument::Integer(IntegerTerm::constant(9.into()).into());
        let native = call(vec![native_argument.clone(), marker.clone()]);
        let shared = call(vec![shared_argument.clone(), marker.clone()]);
        let a = SharedMachineIntegerTerm::intern(format, native.clone());
        let b = SharedMachineIntegerTerm::intern(format, shared.clone());
        assert_eq!(a, b);
        assert_eq!(a.retained_written_operand(), Some(&native));
        assert_eq!(b.retained_written_operand(), Some(&shared));
        assert_ne!(
            a,
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, native)
        );
        assert_ne!(
            a,
            SharedMachineIntegerTerm::intern(format, call(vec![marker, shared_argument]))
        );
        let different_argument_sort = call(vec![
            PureFunctionArgument::Value(ProgramValue::UInt32(MachineTerm::constant(7))),
            PureFunctionArgument::Integer(IntegerTerm::constant(9.into()).into()),
        ]);
        assert_ne!(
            a,
            SharedMachineIntegerTerm::intern(format, different_argument_sort)
        );
    }
}
