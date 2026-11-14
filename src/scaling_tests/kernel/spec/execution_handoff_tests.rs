use super::*;

#[test]
fn specification_execution_adapter_retains_growing_machine_results() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = sum(MachineIntegerType::UInt32);
        for _ in 1..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::UInt32(
                    MachineTerm::Variable(Variable(998253)),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| adapter(&expression));
        assert_eq!(paths.len(), 1);
        let CExpressionOutcome::Value(SpecValue::Shared(root)) = &paths[0].outcome else {
            panic!("the adapter must retain the produced machine root");
        };
        assert_eq!(root.ty(), &KernelType::C(ProgramType::UInt32));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}
