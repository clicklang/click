#[test]
fn loadable_count_production_retains_growing_bound_dags() {
    let mut baselines = [None, None];
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        for wide in [false, true] {
            let format = if wide {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::Int32
            };
            let zero = if wide {
                OldMachineTerm::uint64_constant(0)
            } else {
                OldMachineTerm::constant(0)
            };
            let mut end = KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Old(&OldMachineTerm::Variable(Variable(10993702))),
            );
            for _ in 0..size {
                end = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [end.clone(), end],
                );
            }
            let mut range = if wide {
                MemoryRange::new_wide(Address::symbolic(Variable(10993703)), zero.clone(), zero, 1)
            } else {
                MemoryRange::new_with_element_width(
                    Address::symbolic(Variable(10993703)),
                    zero.clone(),
                    zero,
                    1,
                )
            };
            range.end_bound = StoredMachineTerm::from_value(end.clone().into()).unwrap();
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    let Proposition::MemoryLoadable { bytes, .. } =
                        range.loadable_fact(&SymbolicMemory::new())
                    else {
                        unreachable!()
                    };
                    assert_eq!(bytes.root(), Some(&end));
                }
            });
            assert_eq!(
                crate::kernel::KernelTermExport::machine_export_count(),
                exports
            );
            assert!(!end.has_cached_native_argument());
            assert_eq!(
                work,
                *baselines[usize::from(wide)].get_or_insert(work),
                "size={size}, wide={wide}"
            );
        }
    }
}
