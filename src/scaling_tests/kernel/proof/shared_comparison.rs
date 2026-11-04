#[test]
fn shared_comparison_growing_prefixes_scale_linearly() {
    let measure = |count| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = |n| KernelTerm::variable(KernelType::C(CType::Int32), Variable(n));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut root = variable(993000);
            for index in 0..count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root, variable(993001 + index)],
                );
                let condition = Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(
                            SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                        ),
                        IntegerTerm::constant_i64(7),
                    ),
                    true,
                );
                assert!(TermRewrite::arithmetic_comparison(&condition).is_none());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work
    };
    let small = measure(64);
    let large = measure(256);
    assert!(
        large <= small * 5,
        "prefix reconstruction grew from {small} to {large}"
    );
}

#[test]
fn comparison_read_prefixes_retain_conversions_without_exports() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let value = MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(992202)).into(),
            destination: format,
        };
        let (load, _) = comparison_read_fixture(value.clone());
        let mut root = imported(format, MachineTerm::Variable(load));
        let mut expected = imported(format, value);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                expected = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [expected.clone(), expected.clone()],
                );
                let proposition = |value| {
                    Proposition::ConditionIs(
                        ConditionTerm::integer_less_than(
                            IntegerTerm::Machine(
                                SharedMachineIntegerTerm::from_shared(format, value).unwrap(),
                            ),
                            IntegerTerm::constant_i64(0),
                        ),
                        true,
                    )
                };
                assert_eq!(
                    TermRewrite::arithmetic_comparison(&proposition(root.clone())),
                    Some(proposition(expected.clone()))
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}

#[test]
fn quantified_variable_substitution_visits_shared_nodes_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let source = MachineTerm::Variable(Variable(993101));
        let replacement = MachineTerm::Variable(Variable(993102));
        let mut root = imported(format, source.clone());
        let mut expected = imported(format, replacement.clone());
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
            expected = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [expected.clone(), expected.clone()],
            );
        }
        let observed = |root| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
        };
        let input = observed(root);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits_checked(&source, &replacement).integer(&input)
        });
        assert_eq!(result, observed(expected));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
