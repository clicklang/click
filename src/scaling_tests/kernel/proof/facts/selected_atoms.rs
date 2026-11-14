#[test]
fn shared_selected_atoms_reuse_growing_prefixes_and_cold_dags() {
    for prefixes in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let format = MachineIntegerType::Int32;
            let mut root =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1005400));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    if prefixes || index + 1 == size {
                        let machine =
                            SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                        let mut atoms = BTreeSet::new();
                        collect(&machine, &mut atoms);
                        assert_eq!(
                            atoms,
                            BTreeSet::from([BitvectorEqualityAtomKey::Variable(Variable(1005400))])
                        );
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
