use super::*;

#[test]
fn identity_cast_chains_keep_all_integer_roots_without_exports() {
    for format in FORMATS {
        let mut previous = None;
        for size in [16, 32, 64] {
            let _session = VerificationSession::enter();
            let root = KernelTermImport::default()
                .machine(format, &MachineTerm::Variable(Variable(995412)));
            let exports = KernelTermExport::machine_export_count();
            let (path, work) = cast_chain(&root, format.program_type(), size);
            assert_eq!(path.value, SpecValue::Shared(root));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(before) = previous {
                assert!(
                    work <= before * 3 + 8,
                    "{format:?}: {size}: {work} vs {before}"
                );
            }
            previous = Some(work);
        }
    }
}
