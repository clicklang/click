//! Numeric identity of retained machine observations. Exact producer payloads
//! remain untouched; opaque leaves use the existing native observation key.
use super::*;

thread_local! {
    static ROOTS: std::cell::RefCell<crate::id_hash::U64Map<KernelTerm>> = Default::default();
}
pub(super) fn clear() {
    ROOTS.with(|roots| roots.borrow_mut().clear());
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
            let format = match term.ty() {
                KernelType::C(ty) => {
                    MachineIntegerType::from_c_type(*ty).expect("machine observation")
                }
                _ => unreachable!(),
            };
            if !finish && matches!(term.node(), KernelTermNode::Legacy(_)) {
                let value = term
                    .machine_conversion_leaf()
                    .expect("retained machine leaf");
                let view = MachineOperandView::Legacy(value);
                if view.binary().is_some() || view.unary().is_some() || view.cast().is_some() {
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
                KernelTermNode::MachineBinary { arguments, .. } => arguments.to_vec(),
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
                KernelTermNode::Legacy(_) => {
                    let value = term
                        .machine_conversion_leaf()
                        .expect("retained machine leaf");
                    let identity = SharedMachineIntegerTerm::intern_key(MachineIntegerKey::native(
                        format,
                        value.clone(),
                    ));
                    KernelTerm::machine_observation_leaf(format, value.clone(), identity)
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
