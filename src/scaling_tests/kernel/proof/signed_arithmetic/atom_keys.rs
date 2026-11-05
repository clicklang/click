#[test]
fn signed_atom_keys_retain_cold_and_growing_dags() {
    for prefixes in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root = variable(Variable(1006402));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        T::Int32,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    if prefixes || index + 1 == size {
                        let atom = from_shared(&root).unwrap();
                        assert!(!atom.is_opaque_root());
                        assert_eq!(atom.work(), 1);
                        assert_eq!(from_shared(&root), Some(atom.clone()));
                        let claim = signed_arithmetic_integer_result(&observed_result(
                            root.clone(),
                            T::Int32,
                        ))
                        .unwrap();
                        assert_eq!(claim.terms.len(), 1);
                        assert_eq!(claim.terms.keys().next(), Some(&atom));
                    }
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "prefixes={prefixes}: {samples:?}");
        }
    }
}
