use super::*;
use crate::kernel::{KernelTermExport, VerificationSession};
#[test]
fn shared_pointer_equality_visits_offset_pairs_and_load_pairs_once() {
    let _session = VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| SharedPointerAddress::import(&Pointer::symbolic(Variable(1013000 + i))))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let cell = Memory::global_pointer("shared-check-scaling");
            let before = Memory::new().with_block("shared-check-scaling", 16);
            let after = before
                .clone()
                .store(cell.clone(), ProgramValue::Int32(MachineTerm::constant(1)));
            let make = |memory| {
                let native = Pointer {
                    block: PointerBlock::Concrete("shared-check-array".into()),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: SharedMachineIntegerTerm::index(
                            MachineIntegerType::Int32,
                            MachineTerm::MemoryLoad(
                                crate::kernel::intern_memory(memory),
                                Box::new(cell.clone()),
                                LoadKind::Int32,
                            ),
                        ),
                        byte_width: 4,
                    },
                };
                let initial = SharedPointerAddress::import(&native);
                let mut offset = initial.node().offset.clone();
                for _ in 0..size {
                    offset = O::Add([offset.clone(), offset]).into_shared().unwrap();
                }
                SharedPointerAddress::new(initial.node().block.clone(), offset)
            };
            let a = make(before);
            let b = make(after);
            let calls = std::cell::Cell::new(0);
            let loads = |_: &MachineTerm, _: &MachineTerm| {
                calls.set(calls.get() + 1);
                true
            };
            let exports = KernelTermExport::machine_export_count();
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                shared_addresses_equal_with_load_atoms(&a, &b, &loads)
            });
            assert!(equal);
            assert_eq!(calls.get(), 1);
            assert!(
                work <= 8 * size + 100,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert!(!shared_addresses_equal_with_load_atoms(&a, &b, &|_, _| {
                false
            }));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
