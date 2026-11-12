use super::*;
#[test]
fn retained_syntax_comparison_visits_each_shared_pair_once() {
    let mut work = Vec::new();
    for depth in [8, 32, 96] {
        let _session = VerificationSession::enter();
        let prefix = || {
            let mut root = retained_leaf(7);
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            condition(root)
        };
        let (left, right) = (prefix(), prefix());
        let exports = KernelTermExport::machine_export_count();
        let (equal, cost) =
            crate::instrumentation::measure_deterministic_work(|| conditions_equal(&left, &right));
        assert!(equal);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(cost);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 32, "{work:?}");
    }
}
