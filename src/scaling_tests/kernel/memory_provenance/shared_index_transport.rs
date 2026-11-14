#[test]
fn framed_index_transport_visits_shared_nodes_without_tree_exports() {
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018910));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let value = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
            let offset = match ty {
                MachineIntegerType::Int32 => PointerOffsetTerm::Int32Scaled {
                    value,
                    byte_width: 4,
                },
                _ => PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width: 4,
                    unsigned: ty == MachineIntegerType::UInt64,
                },
            };
            let after = Memory::new();
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                transport_framed_atomic_pointer_offset(&offset, &after, None).unwrap()
            });
            assert_eq!(exports, KernelTermExport::machine_export_count());
            let (PointerOffsetTerm::Int32Scaled { value: result, .. }
            | PointerOffsetTerm::Int64Scaled { value: result, .. }) = result
            else {
                panic!("retained scaled index")
            };
            assert_eq!(
                result.shared_operand(),
                Some(
                    &root.with_machine_observation_type(if ty == MachineIntegerType::Int32 {
                        ty
                    } else {
                        MachineIntegerType::Int64
                    })
                )
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
            "{samples:?}"
        );
    }
}

#[test]
fn exact_index_normalization_visits_shared_nodes_without_tree_exports() {
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018910));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let value = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
            let offset = match ty {
                MachineIntegerType::Int32 => PointerOffsetTerm::Int32Scaled {
                    value,
                    byte_width: 4,
                },
                _ => PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width: 4,
                    unsigned: ty == MachineIntegerType::UInt64,
                },
            };
            let facts = PureFactContext::new();
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_exact_memory_loads_in_pointer_offset(&offset, &facts)
            });
            assert_eq!(exports, KernelTermExport::machine_export_count());
            let (PointerOffsetTerm::Int32Scaled { value: result, .. }
            | PointerOffsetTerm::Int64Scaled { value: result, .. }) = result
            else {
                panic!("retained scaled index")
            };
            assert_eq!(
                result.shared_operand(),
                Some(
                    &root.with_machine_observation_type(if ty == MachineIntegerType::Int32 {
                        ty
                    } else {
                        MachineIntegerType::Int64
                    })
                )
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
            "{samples:?}"
        );
    }
}

#[test]
fn exact_index_normalization_rewrites_shared_read_dags_without_exports() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let pointer = Memory::global_pointer("exact-scaling");
        let stored = MachineTerm::Variable(Variable(1018970));
        let memory = Memory::new()
            .with_block("exact-scaling", 4)
            .store(pointer.clone(), ProgramValue::Int32(stored.clone()));
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory),
            pointer.into(),
            LoadKind::Int32,
        );
        let mut root = retained(MachineIntegerType::Int32, &load)
            .shared_operand()
            .unwrap()
            .clone();
        let mut expected = retained(MachineIntegerType::Int32, &stored)
            .shared_operand()
            .unwrap()
            .clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
            expected = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [expected.clone(), expected],
            );
        }
        let offset = PointerOffsetTerm::Int32Scaled {
            value: SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
            byte_width: 4,
        };
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_exact_memory_loads_in_pointer_offset(&offset, &facts)
        });
        assert_eq!(exports, KernelTermExport::machine_export_count());
        let PointerOffsetTerm::Int32Scaled { value, .. } = result else {
            panic!("retained index")
        };
        assert_eq!(value.shared_operand(), Some(&expected));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "{samples:?}"
    );
}

#[test]
fn exact_index_normalization_orders_xor_atoms_without_expanding_their_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut a = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018971));
        let mut b = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018972));
        for _ in 0..size {
            a = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [a.clone(), a]);
            b = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [b.clone(), b]);
        }
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::BitwiseXor,
            [b.clone(), a.clone()],
        );
        let value = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let expected = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::BitwiseXor, [a, b]);
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_exact_index(&value, &facts).unwrap()
        });
        assert_eq!(exports, KernelTermExport::machine_export_count());
        assert_eq!(result.shared_operand(), Some(&expected));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "{samples:?}"
    );
}
