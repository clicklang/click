#[test]
fn pointer_index_dependency_comparison_and_hashing_visit_each_dag_node_once() {
    use crate::kernel::{KernelTerm, KernelType};
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1007220));
        for _ in 0..depth {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = offset(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let pointer = Address::new(AddressBase::Concrete("r7-scaling".into()), index.clone());
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut loads = Vec::new();
            collect_pointer_offset_memory_loads(
                &index,
                &SymbolicMemory::new(),
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
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1007221));
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..count {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
                let pointer = Address::new(
                    AddressBase::Concrete("r7-prefix".into()),
                    offset(SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap()),
                );
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

#[test]
fn float_conversion_index_fingerprints_share_growing_float_prefixes() {
    use crate::kernel::{FloatBinaryOperator, KernelFloatType, KernelTerm, KernelType};
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Float32), Variable(999981));
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..count {
                root = KernelTerm::float_binary(
                    KernelFloatType::Float32,
                    FloatBinaryOperator::Add,
                    [root.clone(), root],
                )
                .unwrap();
                let converted = KernelTerm::numeric_float_convert(
                    ProgramType::Int32,
                    ProgramType::Float32,
                    root.clone(),
                )
                .unwrap();
                for policy in [
                    OperandFingerprintPolicy::MemoryBlind,
                    OperandFingerprintPolicy::MemoryState(false),
                    OperandFingerprintPolicy::MemoryState(true),
                ] {
                    let first = operand_fingerprint(MachineOperandView::Shared(&converted), policy);
                    assert_eq!(
                        operand_fingerprint(MachineOperandView::Shared(&converted), policy),
                        first
                    );
                }
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn float_call_index_fingerprints_share_growing_float_prefixes() {
    use crate::kernel::{KernelFloatType, KernelTerm, KernelType};
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Float32), Variable(999981));
        let before = KernelTermExport::float_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..count {
                root = KernelTerm::float_call(
                    KernelFloatType::Float32,
                    "step".into(),
                    vec![(root.clone(), None), (root, None)],
                );
                let converted = KernelTerm::numeric_float_convert(
                    ProgramType::Int32,
                    ProgramType::Float32,
                    root.clone(),
                )
                .unwrap();
                for policy in [
                    OperandFingerprintPolicy::MemoryBlind,
                    OperandFingerprintPolicy::MemoryState(false),
                    OperandFingerprintPolicy::MemoryState(true),
                ] {
                    let first = operand_fingerprint(MachineOperandView::Shared(&converted), policy);
                    assert_eq!(
                        operand_fingerprint(MachineOperandView::Shared(&converted), policy),
                        first
                    );
                }
            }
        });
        assert_eq!(KernelTermExport::float_export_count(), before);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
