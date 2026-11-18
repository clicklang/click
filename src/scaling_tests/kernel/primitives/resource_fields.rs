#[test]
fn resource_field_handoffs_preserve_growing_dags_without_native_exports() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let atom =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993309));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let fields = ResourceFieldValues::from_stored([StoredResourceField::from_program(
                ExecutionValue::Shared(root.clone()),
            )]);
            let value = instance(fields, ProgramType::UInt32);
            for _ in 0..32 {
                let copy = value.clone();
                let selected =
                    ResourceFieldValues::from_stored([copy.fields.stored_field(0).unwrap()]);
                assert_eq!(selected.program_value(0).unwrap().shared(), Some(&root));
            }
        });
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
