use super::*;

#[test]
fn float_atom_views_do_constant_work_beside_growing_arenas() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let unrelated = (0..size)
            .map(|index| KernelTerm::variable(KernelType::Integer, Variable(999900 + index)))
            .collect::<Vec<_>>();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let native = match format {
                KernelFloatType::Float32 => MachineTerm::constant(0x7fc00001),
                KernelFloatType::Float64 => MachineTerm::uint64_constant(0x7ff8000000000001),
            };
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelTermImport::default().float(format, &native);
                let view = FloatOperandView::from_shared(&root).unwrap();
                assert_eq!(view.format(), format);
                assert!(view.literal().is_some());
                assert_eq!(view.variable(), None);
                assert_eq!(view.native_compat(), Some(&native));
                root
            });
            assert!(work <= 4, "size={size}, work={work}");
            assert!(root.children().is_empty());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(unrelated.len(), size as usize);
        }
    }
}
