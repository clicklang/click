use super::*;
use crate::kernel::{KernelFoldIndex, KernelIntegerOperator, KernelTermExport, KernelTermImport};

#[test]
fn common_fold_read_dependencies_visit_shared_bodies_once_and_recheck_snapshots() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let current = CMemory::new();
        let pointer = Pointer::symbolic(Variable(972000));
        let later = current
            .clone()
            .store(pointer.clone(), CValue::Int32(MachineTerm::constant(1)));
        let read = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&current),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            ),
        ));
        let mut body = KernelTermImport::default().integer(&read.into());
        for _ in 0..size {
            body =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            Variable(972001),
            Variable(972002),
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        for memory in [&current, &later, &current] {
            let mut loads = Vec::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                collect_fold_memory_loads(&fold, memory, &mut loads, None, &mut BTreeSet::new())
            });
            result.unwrap();
            assert!(work <= 8 * (size + 1) + 64, "size={size}, work={work}");
            if std::ptr::eq(memory, &current) {
                assert_eq!(loads, vec![(pointer.clone(), 4)]);
            } else {
                assert!(loads.is_empty());
            }
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
