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
            CValue::Int8(value)
            | CValue::UInt8(value)
            | CValue::Int16(value)
            | CValue::UInt16(value)
            | CValue::Int32(value)
            | CValue::UInt32(value)
            | CValue::Int64(value)
            | CValue::UInt64(value)
            | CValue::Int128(value)
            | CValue::UInt128(value) => Some(value),
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
        let mut roots = roots.borrow_mut();
        let mut pending = vec![(root.clone(), false)];
        let mut expanded = HashMap::new();
        while let Some((term, finish)) = pending.pop() {
            if roots.contains_key(&term.id()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if !term.has_opaque_observation_boundary() {
                roots.insert(term.id(), term);
                continue;
            }
            let format = match term.ty() {
                KernelType::C(ty) => {
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
                    || matches!(value, MachineTerm::If { .. })
                {
                    let replacement = KernelTerm::retained_machine_operand(format, view);
                    expanded.insert(term.id(), replacement.clone());
                    pending.push((term, true));
                    pending.push((replacement, false));
                    continue;
                }
            }
            if let Some(replacement) = expanded.remove(&term.id()) {
                let normalized = roots[&replacement.id()].clone();
                roots.insert(term.id(), normalized);
                continue;
            }
            let children = match term.node() {
                KernelTermNode::MachineBinary { arguments, .. }
                | KernelTermNode::BoolCompare { arguments, .. }
                | KernelTermNode::BoolEqual { arguments } => arguments.to_vec(),
                KernelTermNode::MachineIf { arguments } | KernelTermNode::BoolIf { arguments } => {
                    arguments.to_vec()
                }
                KernelTermNode::Call { arguments, .. } if term.ty() == &KernelType::Bool => {
                    arguments.clone()
                }
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand.clone()],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term, true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let normalized = match term.node() {
                KernelTermNode::Legacy(_) if machine_payload(&term).is_some() => {
                    let value = machine_payload(&term).expect("retained machine leaf");
                    let identity = SharedMachineIntegerTerm::intern_key(MachineIntegerKey::native(
                        format,
                        value.clone(),
                    ));
                    KernelTerm::machine_observation_leaf(format, value.clone(), identity)
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
                KernelTermNode::MachineIf { arguments } => KernelTerm::machine_if_shared(
                    format,
                    arguments.each_ref().map(|arg| roots[&arg.id()].clone()),
                ),
                KernelTermNode::BoolIf { arguments } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolIf {
                        arguments: arguments.each_ref().map(|arg| roots[&arg.id()].clone()),
                    },
                ),
                KernelTermNode::BoolEqual { arguments } => KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolEqual {
                        arguments: arguments.each_ref().map(|arg| roots[&arg.id()].clone()),
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
                        arguments: arguments.each_ref().map(|arg| roots[&arg.id()].clone()),
                    },
                ),
                KernelTermNode::Call { name, arguments } if term.ty() == &KernelType::Bool => {
                    KernelTerm::intern(
                        KernelType::Bool,
                        KernelTermNode::Call {
                            name: name.clone(),
                            arguments: arguments
                                .iter()
                                .map(|arg| roots[&arg.id()].clone())
                                .collect(),
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
                    [
                        roots[&arguments[0].id()].clone(),
                        roots[&arguments[1].id()].clone(),
                    ],
                ),
                KernelTermNode::MachineUnary {
                    format: operation_format,
                    operator,
                    operand,
                } => KernelTerm::machine_unary_shared(
                    *operation_format,
                    *operator,
                    roots[&operand.id()].clone(),
                )
                .with_machine_observation_type(format),
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => KernelTerm::machine_cast_shared(
                    *encoding,
                    *source,
                    *destination,
                    roots[&operand.id()].clone(),
                )
                .with_machine_observation_type(format),
                _ => term.clone(),
            };
            roots.insert(term.id(), normalized);
        }
        roots[&root.id()].clone()
    })
}
