use super::*;
use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};

#[test]
fn shared_index_addresses_preserve_native_queries_and_late_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = OldMachineTerm::Variable(Variable(991401));
    let b = OldMachineTerm::Variable(Variable(991402));
    let inputs = [
        a.clone(),
        OldMachineTerm::add(a.clone(), b),
        OldMachineTerm::subtract(a, 1u32.into()),
        0u32.into(),
        u32::MAX.into(),
    ];
    for input in inputs {
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &input)
            .unwrap();
        for width in [1, 4, 8] {
            for successor in [false, true] {
                for alias_first in [false, true] {
                    let mut graph = EqualityGraph::default();
                    let p = OldAddress::symbolic(Variable(991403));
                    let q = OldAddress::symbolic(Variable(991404)).offset_by_bytes(12);
                    if alias_first {
                        graph.add_equality(&p, &q);
                    }
                    let exports = KernelTermExport::machine_export_count();
                    let native = graph
                        .indexed_address_class(&p, V::Old(&input), successor, width)
                        .unwrap();
                    let shared = graph
                        .indexed_address_class(&p, V::Shared(&root), successor, width)
                        .unwrap();
                    assert_eq!(
                        graph.address_class_root(native),
                        graph.address_class_root(shared),
                        "{input:?} {width} {successor}"
                    );
                    if !alias_first {
                        graph.add_equality(&p, &q);
                    }
                    let aliased = graph
                        .indexed_address_class(&q, V::Old(&input), successor, width)
                        .unwrap();
                    let shared = graph
                        .indexed_address_class(&p, V::Shared(&root), successor, width)
                        .unwrap();
                    assert_eq!(
                        graph.address_class_root(aliased),
                        graph.address_class_root(shared)
                    );
                    let distinct = graph
                        .indexed_address_class(
                            &p.offset_by_bytes(1),
                            V::Shared(&root),
                            successor,
                            width,
                        )
                        .unwrap();
                    assert_ne!(
                        graph.address_class_root(distinct),
                        graph.address_class_root(shared)
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[test]
fn scaled_offset_keys_and_congruence_retain_shared_operands() {
    use crate::kernel::SharedMachineIntegerTerm;
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let offset = |native: OldMachineTerm, stride| {
            let container = if ty == MachineIntegerType::Int32 {
                ty
            } else {
                MachineIntegerType::Int64
            };
            let root = KernelTermImport::default()
                .machine_arithmetic(container, &native)
                .unwrap();
            let value = SharedMachineIntegerTerm::from_shared(container, root).unwrap();
            if ty == MachineIntegerType::Int32 {
                OldAddressOffset::Int32Scaled {
                    value,
                    byte_width: stride,
                }
            } else {
                OldAddressOffset::Int64Scaled {
                    value,
                    byte_width: stride,
                    unsigned: ty == MachineIntegerType::UInt64,
                }
            }
        };
        let expression = |variable| OldMachineTerm::Binary {
            format: ty,
            op: crate::kernel::MachineBinaryOp::Add,
            left: OldMachineTerm::Variable(Variable(variable)).into(),
            right: OldMachineTerm::Variable(Variable(variable)).into(),
        };
        let left = offset(expression(991420), 4);
        let right = offset(expression(991421), 4);
        let different = offset(expression(991421), 8);
        let exports = KernelTermExport::machine_export_count();
        let mut graph = EqualityGraph::default();
        assert_ne!(AffineOffset::of(&left), AffineOffset::of(&right));
        assert!(!graph.are_offsets_equal(&left, &right));
        let sibling = graph.clone();
        graph.add_offset_equality(&left, &right);
        assert!(graph.are_offsets_equal(&left, &right));
        assert!(!sibling.are_offsets_equal(&left, &right));
        assert!(!graph.are_offsets_equal(&left, &different));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/equality_graph/shared_index_tests.rs");
}
