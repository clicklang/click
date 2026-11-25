#[test]
fn retained_range_and_allocation_handoffs_ignore_growing_operand_dags() {
    for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut baseline = None;
        for size in [4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(10993614));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let pointer = OldPointer::new(
                OldAddress::symbolic(Variable(10993615)),
                ProgramType::Int32Pointer,
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let range = MemoryRange::from_retained_bounds(
                    &pointer,
                    root.clone().into(),
                    root.clone().into(),
                    4,
                )
                .unwrap();
                let bytes = AllocationSize::from_value(root.clone().into()).unwrap();
                let token = ResourceFact::own_designated_allocation(pointer.clone(), &bytes);
                if ty == MachineIntegerType::Int32 {
                    assert!(range.wide_bounds().is_none());
                } else {
                    assert!(range.int32_bounds().is_none());
                    assert!(bytes.int32_bytes().is_none());
                }
                for _ in 0..32 {
                    let copy = range.clone().spatial_key();
                    assert_eq!(copy.retained_bounds().0.root(), Some(&root));
                    let (_, bytes) = token.allocation_size().unwrap();
                    let token = ResourceFact::own_designated_allocation(pointer.clone(), &bytes);
                    let Resource::Token { arguments, .. } = token.resource() else {
                        panic!("token");
                    };
                    assert_eq!(arguments.program_value(1).unwrap().shared(), Some(&root));
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "size={size}, type={ty:?}"
            );
        }
    }
}
