//! Structural signed-certificate identities over shared machine operands.
//! Normalize only the signed atom fragment's literal tags and observation
//! types. The keys are checking metadata, never replacements for stored terms.
use super::*;
use crate::kernel::{
    KernelTerm, KernelTermImport, KernelTermNode, KernelType, MachineOperandView, MachineUnaryOp,
};

thread_local! {
    static KEYS: std::cell::RefCell<HashMap<u64, Option<KernelTerm>>> = Default::default();
}

pub(crate) fn clear_shared_operand_keys() {
    KEYS.with(|keys| keys.borrow_mut().clear());
}

pub(super) fn operands_equal(left: MachineOperandView<'_>, right: MachineOperandView<'_>) -> bool {
    match (left, right) {
        (MachineOperandView::Legacy(left), right) => signed_operand_matches(right, left),
        (left, MachineOperandView::Legacy(right)) => signed_operand_matches(left, right),
        (MachineOperandView::Shared(left), MachineOperandView::Shared(right)) => {
            KEYS.with(|keys| {
                let mut keys = keys.borrow_mut();
                match (shared_key(left, &mut keys), shared_key(right, &mut keys)) {
                    (Some(left), Some(right)) => left == right,
                    _ => false,
                }
            })
        }
    }
}

fn shared_key(
    root: &KernelTerm,
    keys: &mut HashMap<u64, Option<KernelTerm>>,
) -> Option<KernelTerm> {
    let mut pending = vec![(root, false)];
    while let Some((term, finish)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if keys.contains_key(&term.id()) {
            continue;
        }
        let normalized =
            match term.node() {
                KernelTermNode::Variable(variable) => Some(KernelTerm::variable(
                    KernelType::C(crate::kernel::CType::Int32),
                    *variable,
                )),
                KernelTermNode::MachineLiteral(_) => MachineOperandView::Shared(term)
                    .literal()
                    .and_then(|literal| match literal {
                        Bitvector32Term::Constant(bits) | Bitvector32Term::UInt32Constant(bits) => {
                            Some(KernelTermImport::default().machine(
                                MachineIntegerType::Int32,
                                &Bitvector32Term::Constant(bits),
                            ))
                        }
                        _ => None,
                    }),
                KernelTermNode::MachineUnary {
                    format: MachineIntegerType::Int32,
                    operator: MachineUnaryOp::BitwiseNot,
                    operand,
                } => {
                    if !finish {
                        pending.push((term, true));
                        pending.push((operand, false));
                        continue;
                    }
                    keys[&operand.id()].as_ref().map(|operand| {
                        KernelTerm::machine_unary_shared(
                            MachineIntegerType::Int32,
                            MachineUnaryOp::BitwiseNot,
                            operand.clone(),
                        )
                    })
                }
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } if *format == MachineIntegerType::Int32
                    || (*format == MachineIntegerType::UInt32
                        && *operator == MachineBinaryOp::ShiftRight) =>
                {
                    if !finish {
                        pending.push((term, true));
                        pending.push((&arguments[1], false));
                        pending.push((&arguments[0], false));
                        continue;
                    }
                    match (&keys[&arguments[0].id()], &keys[&arguments[1].id()]) {
                        (Some(left), Some(right)) => Some(KernelTerm::machine_binary_shared(
                            *format,
                            *operator,
                            [left.clone(), right.clone()],
                        )),
                        _ => None,
                    }
                }
                _ => None,
            };
        keys.insert(term.id(), normalized);
    }
    keys[&root.id()].clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_keys_survive_state_restore_but_clear_for_a_new_session() {
        {
            let _session = crate::kernel::VerificationSession::enter();
            let snapshot = crate::kernel::VerificationSession::capture_state();
            let format = MachineIntegerType::Int32;
            let mut term =
                KernelTerm::variable(KernelType::C(crate::kernel::CType::Int32), Variable(982501));
            for _ in 0..32 {
                term = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                );
            }
            let view = MachineOperandView::Shared(&term);
            assert!(operands_equal(view, view));
            let count = KEYS.with(|keys| keys.borrow().len());
            assert!(crate::kernel::VerificationSession::restore_state(&snapshot));
            crate::kernel::eval::begin_load_origin_epoch();
            let (same, work) =
                crate::instrumentation::measure_deterministic_work(|| operands_equal(view, view));
            assert!(same);
            assert!(
                work <= 4,
                "a restored context rewalked structural operands: {work}"
            );
            assert_eq!(KEYS.with(|keys| keys.borrow().len()), count);
        }
        let _session = crate::kernel::VerificationSession::enter();
        assert!(KEYS.with(|keys| keys.borrow().is_empty()));
    }
}
