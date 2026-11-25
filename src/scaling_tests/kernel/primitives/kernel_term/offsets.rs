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
                KernelAddressOffset::Variable(Variable(997000 + i))
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
            let source = OldAddressOffset::Int64Scaled {
                value: operand.clone(),
                byte_width: 8,
                unsigned: true,
            };
            let exports = KernelTermExport::machine_export_count();
            let ((root, native), work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelAddressOffset::import(&source);
                let native = KernelAddressOffset::export(&root).unwrap();
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
        let mut source = OldAddressOffset::Variable(Variable(996001));
        for _ in 0..size {
            source =
                OldAddressOffset::Add(Box::new(source), Box::new(OldAddressOffset::Constant(0)));
        }
        let ((root, output), work) = crate::instrumentation::measure_deterministic_work(|| {
            let root = KernelAddressOffset::import(&source);
            let output = KernelAddressOffset::export(&root).unwrap();
            (root, output)
        });
        assert_eq!(source, output);
        assert!(matches!(root.node(), KernelAddressOffset::Add(_)));
        assert!(work <= 22 * size + 12, "size={size}, work={work}");
    }
}

#[test]
fn shared_offset_dag_construction_does_not_rewalk_prefixes() {
    for size in [16, 64, 256] {
        let mut root = KernelAddressOffset::Constant(0).into_shared().unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelAddressOffset::Add([root.clone(), root.clone()])
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

#[test]
fn offset_condition_rewrites_preserve_shared_offset_dags() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut offset = KernelAddressOffset::Int32Scaled {
            value: KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998200)),
            byte_width: 4,
        }
        .into_shared()
        .unwrap();
        for _ in 0..size {
            offset = KernelAddressOffset::Add([offset.clone(), offset])
                .into_shared()
                .unwrap();
        }
        let source = KernelTerm::address_offset_equal_raw([offset.clone(), offset]);
        let exports = KernelTermExport::machine_export_count();
        let ((rewritten, transported), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let rewritten =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                        &source,
                        Variable(998201),
                        &OldMachineTerm::constant(1),
                    )
                    .unwrap();
                let transported = crate::kernel::memory_history::transport_framed_common_condition(
                    &source,
                    &crate::kernel::ProgramPoint::of_memory(&crate::kernel::SymbolicMemory::new()),
                    None,
                )
                .unwrap();
                (rewritten, transported)
            });
        assert_eq!(source, rewritten);
        assert_eq!(source, transported);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 45 * size + 500, "size={size}, work={work}");
    }
}

#[test]
fn growing_offset_guards_reuse_observation_normalization() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut offset = KernelAddressOffset::Int32Scaled {
            value: KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998300)),
            byte_width: 4,
        }
        .into_shared()
        .unwrap();
        let zero = KernelAddressOffset::Constant(0).into_shared().unwrap();
        let word = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &OldMachineTerm::constant(1));
        let exports = KernelTermExport::machine_export_count();
        let mut retained = Vec::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                offset = KernelAddressOffset::Add([offset.clone(), offset.clone()])
                    .into_shared()
                    .unwrap();
                let guard = KernelTerm::address_offset_equal_raw([offset.clone(), zero.clone()]);
                let value = KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [guard, word.clone(), word.clone()],
                );
                retained.push(
                    SharedMachineIntegerTerm::observe_shared(MachineIntegerType::Int32, value)
                        .unwrap(),
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 55 * size + 100, "size={size}, work={work}");
    }
}
