use super::*;

#[test]
fn growing_antecedent_operands_do_not_export_shared_prefixes() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let variable = Variable(997711);
        let variables = BTreeSet::from([variable]);
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), variable);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let guard = bound(format, root.clone(), 7, true);
                assert!(uint64_antecedent_ranges(&variables, &guard).is_empty());
                let ranges = antecedent_ranges(&variables, &guard).unwrap();
                assert_eq!(ranges[&variable].upper, None);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{samples:?}");
    }
}
