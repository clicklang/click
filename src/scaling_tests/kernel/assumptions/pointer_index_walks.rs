#[test]
fn pointer_index_dependency_comparison_and_hashing_visit_each_dag_node_once() {
    use crate::kernel::{KernelTerm, KernelType};
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1007220));
        for _ in 0..depth {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = offset(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let pointer = Pointer {
            block: PointerBlock::Concrete("r7-scaling".into()),
            offset: index.clone(),
        };
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut loads = Vec::new();
            collect_pointer_offset_memory_loads(
                &index,
                &Memory::new(),
                &mut loads,
                &mut BTreeSet::new(),
            )
            .unwrap();
            assert!(loads.is_empty());
            assert!(offsets_equal_with_load_atoms(&index, &index, &|a, b| a == b));
            memory_blind_pointer_fingerprint(&pointer);
        });
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn growing_pointer_index_fingerprints_reuse_shared_prefixes() {
    use crate::kernel::{KernelTerm, KernelType};
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1007221));
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..count {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
                let pointer = Pointer {
                    block: PointerBlock::Concrete("r7-prefix".into()),
                    offset: offset(
                        SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap(),
                    ),
                };
                memory_blind_pointer_fingerprint(&pointer);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
