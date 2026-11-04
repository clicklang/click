use super::*;

#[test]
fn shared_dependency_admission_and_singleton_queries_scale_with_new_nodes() {
    let measure = |size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        let mut root = variable(995000);
        let exports = KernelTermExport::machine_export_count();
        let (context, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = product(root.clone(), variable(995001 + index));
                let condition = bound(root.clone(), index as i64);
                context = context.assume_condition(condition.clone(), true);
                assert_eq!(
                    context.singleton_condition_variable(Variable(995001 + index)),
                    Some((&condition, true))
                );
                assert_eq!(
                    context
                        .singleton_condition_variable(Variable(995000))
                        .is_some(),
                    index == 0
                );
                assert!(!context.has_condition_variable(Variable(996000)));
            }
            context
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let enumerated = context
            .condition_variable_facts(Variable(995000))
            .collect::<Vec<_>>();
        assert_eq!(enumerated.len(), size as usize);
        work
    };
    let samples = [32, 64, 128].map(measure);
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5 / 2 + 100, "{samples:?}");
    }
}
