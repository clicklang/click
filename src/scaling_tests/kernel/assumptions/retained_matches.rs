use super::*;
use crate::kernel::{KernelMatchArm, KernelTerm, KernelTermExport, KernelTermImport};

#[test]
fn match_dependencies_visit_shared_arm_bodies_once() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let current = CMemory::new();
        let pointer = Pointer::symbolic(Variable(991930));
        let read = MachineTerm::MemoryLoad(
            intern_c_memory_ref(&current),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let mut body = KernelTermImport::default().machine(MachineIntegerType::Int32, &read);
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [body.clone(), body],
            );
        }
        let scrutinee = KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(
            KernelMatch::test_scrutinee(vec![]),
        ));
        let arms = (0..size)
            .map(|_| {
                (
                    KernelMatchArm {
                        variant: "Arm".into(),
                        binding_names: Default::default(),
                        bindings: vec![],
                    },
                    body.clone(),
                )
            })
            .collect();
        let matched = KernelMatch::new(KernelType::C(ProgramType::Int32), scrutinee, arms).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let ((result, loads), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut loads = Vec::new();
            let result = collect_match_memory_loads(
                &matched,
                &current,
                &mut loads,
                Some(4),
                &mut BTreeSet::new(),
            );
            (result, loads)
        });
        assert_eq!(result, Ok(()));
        assert_eq!(loads, vec![(pointer, 4)]);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 100, "size={size}, work={work}");
    }
}
