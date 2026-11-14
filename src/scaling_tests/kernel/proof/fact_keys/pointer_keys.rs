use super::*;
use crate::kernel::{
    KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, VerificationSession,
};
#[test]
fn pointer_key_dags_visit_each_offset_and_numeric_root_once() {
    let _session = VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| snapshot_offset(&O::Constant(i).into_shared().unwrap()))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut number =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1011000));
            for _ in 0..size {
                number = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [number.clone(), number],
                );
            }
            let mut offset = O::Constant(0).into_shared().unwrap();
            for width in 0..size {
                let leaf = O::Int32Scaled {
                    value: number.clone(),
                    byte_width: width as i64,
                }
                .into_shared()
                .unwrap();
                offset = O::Add([offset.clone(), offset]).into_shared().unwrap();
                offset = O::Add([offset, leaf]).into_shared().unwrap();
            }
            clear_snapshot_operand_keys();
            let exports = KernelTermExport::machine_export_count();
            let ((snapshot, alpha), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    (
                        snapshot_offset(&offset),
                        alpha_offset::<true>(&offset, &mut fold_keys::bindings(), &mut 0).unwrap(),
                    )
                });
            assert!(!snapshot.requires_checked_match());
            let (_, compare_work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut h = std::collections::hash_map::DefaultHasher::new();
                snapshot.hash(&mut h);
                alpha.hash(&mut h);
                assert_eq!(snapshot, snapshot.clone());
                h.finish()
            });
            assert_eq!(compare_work, 0);
            assert!(
                work <= 40 * size + 100,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
