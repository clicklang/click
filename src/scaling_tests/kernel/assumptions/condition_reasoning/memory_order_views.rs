#[test]
fn memory_order_queries_scale_across_growing_prefixes_and_fact_contexts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(CType::Int32), Variable(993211));
        let target =
            IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(993212))).unwrap();
        let mut facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(
                        0u32.into(),
                        MachineTerm::Variable(Variable(994000 + index)),
                    ),
                    true,
                );
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                let query = ConditionTerm::integer_less_than(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                    ),
                    target.clone(),
                );
                assert!(!facts.proves_order_condition_for_memory_resolution(&query, true));
                let child = facts.clone().assume_condition(query.clone(), true);
                assert!(
                    child.proves_order_condition_for_memory_resolution(&query, true),
                    "size {size}, prefix {index}: exact {:?}, graph {}",
                    child.exact_condition_value(&query),
                    child.difference_graph_proves(&query)
                );
                assert!(!facts.proves_order_condition_for_memory_resolution(&query, true));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
