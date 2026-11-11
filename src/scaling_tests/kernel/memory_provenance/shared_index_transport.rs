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
            let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1018910));
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
            let after = CMemory::new();
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
