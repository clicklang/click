//! The certificate's existing bounded structural identity, read from either
//! operand representation. The payload bound counts occurrences, as before;
//! sharing is not permission to admit a previously refused certificate shape.
use super::*;
use crate::kernel::{MachineCastSpelling as Encoding, MachineOperandView as View};

fn unwrap_leaf(view: View<'_>) -> View<'_> {
    match view {
        View::Shared(root) => root
            .machine_conversion_leaf()
            .map(View::Legacy)
            .unwrap_or(view),
        _ => view,
    }
}

pub(super) fn binary_supported(format: MachineIntegerType, op: MachineBinaryOp) -> bool {
    use MachineBinaryOp::*;
    matches!(
        (format, op),
        (
            MachineIntegerType::Int32,
            Add | Subtract | BitwiseAnd | BitwiseOr | BitwiseXor
        ) | (MachineIntegerType::Int64, Add)
            | (
                MachineIntegerType::UInt64,
                Add | Subtract | Multiply | Divide | Remainder | BitwiseAnd | BitwiseOr
            )
    )
}

fn cast_supported(encoding: Encoding) -> bool {
    matches!(
        encoding,
        Encoding::Generic
            | Encoding::Int64FromUInt32
            | Encoding::UInt64From32
            | Encoding::UInt32From64
    )
}

fn payload(root: View<'_>) -> Option<usize> {
    let mut pending = vec![root];
    let mut total = 0usize;
    while let Some(term) = pending.pop() {
        let term = unwrap_leaf(term);
        if let View::Legacy(term) = term {
            total = total.checked_add(bitvector_payload(term)?)?;
        } else {
            total = total.checked_add(1)?;
            if term.literal().is_some() || term.variable().is_some() || term.read().is_some() {
            } else if let Some((encoding, _, _, operand)) = term.cast() {
                if !cast_supported(encoding) {
                    return None;
                }
                pending.push(operand);
            } else if let Some((format, op, operands)) = term.binary() {
                if !binary_supported(format, op) {
                    return None;
                }
                pending.extend(operands);
            } else {
                return None;
            }
        }
        if total > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(total)
}

// A read is an opaque scalar value, just as its compatibility name was.
// Ignore the observation's format here; the enclosing comparison checks it,
// while the descriptor retains the load kind, state and address.
fn read_identity(view: View<'_>) -> Option<crate::kernel::KernelTerm> {
    match view {
        View::Shared(term) if view.read().is_some() => {
            Some(term.with_machine_observation_type(MachineIntegerType::Int32))
        }
        View::Legacy(MachineTerm::Variable(variable)) => {
            crate::kernel::eval::registered_scalar_read_term(variable, MachineIntegerType::Int32)
        }
        View::Legacy(value @ MachineTerm::MemoryLoad(..)) => {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, value)
        }
        _ => None,
    }
}

/// Structural equality restricted to precisely the certificate fragment.
/// No identity shortcut may bypass unsupported operators or the payload bound.
pub(super) fn equal(left: View<'_>, right: View<'_>) -> bool {
    if let (View::Legacy(left), View::Legacy(right)) = (left, right) {
        return legacy_bitvector_equal(left, right);
    }
    if !payload(left).is_some_and(charge_payload) || !payload(right).is_some_and(charge_payload) {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let (left, right) = (unwrap_leaf(left), unwrap_leaf(right));
        if let (View::Legacy(left), View::Legacy(right)) = (left, right) {
            if !legacy_bitvector_equal(left, right) {
                return false;
            }
            continue;
        }
        if let (Some(left), Some(right)) = (left.literal(), right.literal()) {
            if !legacy_bitvector_equal(&left, &right) {
                return false;
            }
            continue;
        }
        if left.read().is_some() || right.read().is_some() {
            let (Some(left), Some(right)) = (read_identity(left), read_identity(right)) else {
                return false;
            };
            if left != right {
                return false;
            }
            continue;
        }
        if let (Some(left), Some(right)) = (left.variable(), right.variable()) {
            if left != right {
                return false;
            }
            continue;
        }
        if let (Some((le, ls, ld, l)), Some((re, rs, rd, r))) = (left.cast(), right.cast()) {
            if (le, ls, ld) != (re, rs, rd) || !cast_supported(le) {
                return false;
            }
            pending.push((l, r));
            continue;
        }
        if let (Some((lf, lo, [la, lb])), Some((rf, ro, [ra, rb]))) =
            (left.binary(), right.binary())
        {
            if (lf, lo) != (rf, ro) || !binary_supported(lf, lo) {
                return false;
            }
            pending.push((la, ra));
            pending.push((lb, rb));
            continue;
        }
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm, Variable};

    #[test]
    fn shared_certificate_read_identity_keeps_state_address_and_kind() {
        use crate::kernel::{Address, LoadKind, ProgramValue, SymbolicMemory, VerificationSession};
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(997109));
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let name = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address,
            LoadKind::UInt16,
            2,
        );
        let named = MachineTerm::Variable(name);
        let read = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::UInt16, &named)
            .unwrap();
        let wrong = |memory, address, kind| {
            KernelTermImport::default()
                .machine_arithmetic(
                    MachineIntegerType::UInt16,
                    &MachineTerm::MemoryLoad(memory, Box::new(address), kind),
                )
                .unwrap()
        };
        let other_address = wrong(
            crate::kernel::ProgramPoint::at(&memory),
            address.offset_by_bytes(2),
            LoadKind::UInt16,
        );
        let other_kind = wrong(
            crate::kernel::ProgramPoint::at(&memory),
            address.clone(),
            LoadKind::Int16,
        );
        let raw = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(&memory),
            Box::new(address.clone()),
            LoadKind::UInt16,
        );
        let other_memory_state = wrong(
            crate::kernel::ProgramPoint::at(
                &(crate::kernel::intern_memory(memory.memory().clone().store(
                    address.clone(),
                    ProgramValue::UInt16(MachineTerm::narrow_constant(
                        MachineIntegerType::UInt16,
                        7,
                    )),
                ))),
            ),
            address,
            LoadKind::UInt16,
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(equal(View::Shared(&read), View::Legacy(&named)));
        assert!(equal(View::Shared(&read), View::Legacy(&raw)));
        assert!(equal(View::Legacy(&raw), View::Shared(&read)));
        for other in [&other_address, &other_kind, &other_memory_state] {
            assert!(!equal(View::Shared(&read), View::Shared(other)));
        }
        crate::kernel::eval::clear_load_variable_registry();
        assert!(equal(View::Shared(&read), View::Shared(&read)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_certificate_operand_identity_preserves_supported_and_refused_shapes() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                let native = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(MachineTerm::Variable(Variable(997101))),
                    right: Box::new(MachineTerm::Variable(Variable(997102))),
                };
                let Some(root) = KernelTermImport::default().machine_arithmetic(format, &native)
                else {
                    continue;
                };
                let shared = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
                let exports = KernelTermExport::machine_export_count();
                let expected = legacy_bitvector_equal(&native, &native);
                assert_eq!(
                    equal(shared.operand_view(), shared.operand_view()),
                    expected,
                    "{format:?} {op:?}"
                );
                assert_eq!(
                    equal(shared.operand_view(), View::Legacy(&native)),
                    expected,
                    "mixed {format:?} {op:?}"
                );
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(!shared.has_boxed_operand());
            }
        }
    }
}
