use super::*;
use crate::kernel::{KernelTerm, KernelTermExport, KernelType, VerificationSession};
#[test]
fn pointer_surface_index_readers_retain_shared_dags() {
    let _session = VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| {
                KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(1014100 + i),
                )
            })
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let _scope = SurfaceSynthesisScope::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1014700));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let value =
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root.clone())
                    .unwrap();
            let base = OldAddress {
                base: AddressBase::Concrete("surface-index-dag".into()),
                offset: crate::kernel::AddressOffset::from(
                    crate::kernel::OldAddressOffset::Constant(0),
                ),
            };
            let pointer = OldAddress {
                base: base.base.clone(),
                offset: crate::kernel::AddressOffset::from(
                    crate::kernel::OldAddressOffset::Int32Scaled {
                        value,
                        byte_width: 4,
                    },
                ),
            };
            let exports = KernelTermExport::machine_export_count();
            let (index, work) = crate::instrumentation::measure_deterministic_work(|| {
                let index = synthesis_element_index(&pointer, &base, 4).unwrap();
                assert!(load_free(index.operand_view()));
                index
            });
            assert_eq!(index.shared_operand(), Some(&root));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work >= size && work <= 4 * size + 40,
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}
