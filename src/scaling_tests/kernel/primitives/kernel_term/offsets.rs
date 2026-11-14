use super::*;

#[test]
fn offset_nodes_retain_shared_index_dags_with_constant_work() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(995000 + i)))
            .collect::<Vec<_>>();
        let _unrelated_offsets = (0..unrelated)
            .map(|i| {
                KernelPointerOffset::Variable(Variable(997000 + i))
                    .into_shared()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut index =
                KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(996000));
            for _ in 0..size {
                index = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int64,
                    MachineBinaryOp::Add,
                    [index.clone(), index],
                );
            }
            let operand =
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int64, index.clone())
                    .unwrap();
            let source = PointerOffsetTerm::Int64Scaled {
                value: operand.clone(),
                byte_width: 8,
                unsigned: true,
            };
            let exports = KernelTermExport::machine_export_count();
            let ((root, native), work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelPointerOffset::import(&source);
                let native = KernelPointerOffset::export(&root).unwrap();
                (root, native)
            });
            assert_eq!(root.node().index(), Some(&index));
            assert_eq!(native, source);
            assert!(
                work <= 12,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn offset_chain_import_and_explicit_output_have_linear_work() {
    for size in [16, 64, 256] {
        let mut source = PointerOffsetTerm::Variable(Variable(996001));
        for _ in 0..size {
            source =
                PointerOffsetTerm::Add(Box::new(source), Box::new(PointerOffsetTerm::Constant(0)));
        }
        let ((root, output), work) = crate::instrumentation::measure_deterministic_work(|| {
            let root = KernelPointerOffset::import(&source);
            let output = KernelPointerOffset::export(&root).unwrap();
            (root, output)
        });
        assert_eq!(source, output);
        assert!(matches!(root.node(), KernelPointerOffset::Add(_)));
        assert!(work <= 22 * size + 12, "size={size}, work={work}");
    }
}

#[test]
fn shared_offset_dag_construction_does_not_rewalk_prefixes() {
    for size in [16, 64, 256] {
        let mut root = KernelPointerOffset::Constant(0).into_shared().unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelPointerOffset::Add([root.clone(), root.clone()])
                    .into_shared()
                    .unwrap();
            }
        });
        assert!(work <= 9 * size, "size={size}, work={work}");
        assert_eq!(
            root.node().offset_children()[0],
            root.node().offset_children()[1]
        );
    }
}
