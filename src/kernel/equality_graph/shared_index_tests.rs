use super::*;
use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};

#[test]
fn shared_index_addresses_preserve_native_queries_and_late_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = MachineTerm::Variable(Variable(991401));
    let b = MachineTerm::Variable(Variable(991402));
    let inputs = [
        a.clone(),
        MachineTerm::add(a.clone(), b),
        MachineTerm::subtract(a, 1u32.into()),
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
                    let p = Pointer::symbolic(Variable(991403));
                    let q = Pointer::symbolic(Variable(991404)).offset_by_bytes(12);
                    if alias_first {
                        graph.add_equality(&p, &q);
                    }
                    let exports = KernelTermExport::machine_export_count();
                    let native = graph
                        .indexed_address_class(&p, V::Legacy(&input), successor, width)
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
                        .indexed_address_class(&q, V::Legacy(&input), successor, width)
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
        let offset = |native: MachineTerm, stride| {
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
                PointerOffsetTerm::Int32Scaled {
                    value,
                    byte_width: stride,
                }
            } else {
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width: stride,
                    unsigned: ty == MachineIntegerType::UInt64,
                }
            }
        };
        let expression = |variable| MachineTerm::Binary {
            format: ty,
            op: crate::kernel::MachineBinaryOp::Add,
            left: MachineTerm::Variable(Variable(variable)).into(),
            right: MachineTerm::Variable(Variable(variable)).into(),
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
