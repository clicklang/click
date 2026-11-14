use super::*;

#[test]
fn growing_coordinate_guards_retain_shared_indices_without_exports() {
    use MachineIntegerType as T;
    for ty in [T::Int32, T::Int64, T::UInt64] {
        let mut samples = vec![];
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut index =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(993300));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    index = KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [index.clone(), index],
                    );
                    let value = MachineOperandView::Shared(&index).retain(ty);
                    let offset = if ty == T::Int32 {
                        PointerOffsetTerm::Int32Scaled {
                            value,
                            byte_width: 4,
                        }
                    } else {
                        PointerOffsetTerm::Int64Scaled {
                            value,
                            byte_width: 4,
                            unsigned: ty == T::UInt64,
                        }
                    };
                    let mut guards = vec![];
                    let result =
                        exact_pointer_offset_i64_with_guards(&offset, &mut guards).unwrap();
                    assert!(result.shared_operand().is_some());
                    assert!(!guards.is_empty());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|p| p[1] <= 5 * p[0] + 100),
            "{ty:?}: {samples:?}"
        );
    }
}
