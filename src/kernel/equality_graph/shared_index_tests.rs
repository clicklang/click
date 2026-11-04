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

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/equality_graph/shared_index_tests.rs");
}
