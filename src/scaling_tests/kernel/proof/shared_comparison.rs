#[test]
fn shared_comparison_growing_prefixes_scale_linearly() {
    let measure = |count| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable =
            |n| KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(n));
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

#[test]
fn exact_integer_machine_rewrites_preserve_shared_dag_work() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let source: SharedIntegerTerm = IntegerTerm::Variable(Variable(993201)).into();
        let replacement: SharedIntegerTerm = IntegerTerm::constant_i64(7).into();
        let leaf = |value| {
            imported(
                format,
                MachineTerm::IntegerToMachine {
                    value,
                    destination: format,
                },
            )
        };
        let mut input = leaf(source.clone());
        let mut expected = leaf(replacement.clone());
        for _ in 0..size {
            input = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [input.clone(), input.clone()],
            );
            expected = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [expected.clone(), expected.clone()],
            );
        }
        let observe = |root| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
        };
        let input = observe(input);
        let exports = KernelTermExport::machine_export_count();
        let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_integer_exact(&source, &replacement).integer(&input)
        });
        assert_eq!(actual, observe(expected));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}

#[test]
fn compound_source_rewrites_import_the_selected_source_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut source = MachineTerm::Variable(Variable(993202));
        for n in 0..size {
            source = MachineTerm::add(source, MachineTerm::Variable(Variable(994000 + n)));
        }
        let replacement = MachineTerm::add(source.clone(), 1u32.into());
        let mut input = imported(format, source.clone());
        let mut expected = imported(format, replacement.clone());
        for _ in 0..size {
            input = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [input.clone(), input.clone()],
            );
            expected = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [expected.clone(), expected.clone()],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits_checked(&source, &replacement)
                .shared_machine_operand(&input)
                .unwrap()
        });
        assert_eq!(actual, expected);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}

#[test]
fn conditional_remainder_queries_skip_unchanged_shared_prefixes() {
    use crate::kernel::MachineOperandView as V;
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let mut root = imported(ty, MachineTerm::Variable(Variable(985101)));
        let one = constant(ty, 1);
        let five = constant(ty, 5);
        let mut selected = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root, one.clone()],
                );
                let guard = condition_for_operand_views(
                    ty,
                    CompareRelation::LessThan,
                    [V::Shared(&root), V::Shared(&five)],
                );
                selected = selected.assume_condition(guard.clone(), true);
                let conditions = HashMap::from([(guard, true)]);
                let input = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Remainder,
                    [root.clone(), five.clone()],
                );
                let actual = TermRewrite::for_cited_conditions_with_context(
                    &conditions,
                    &selected,
                    &selected,
                )
                .shared_machine_operand(&input)
                .unwrap();
                assert_eq!(actual, root);
                let missing = HashMap::new();
                assert_eq!(
                    TermRewrite::for_conditions(&missing)
                        .shared_machine_operand(&input)
                        .unwrap(),
                    input
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn wide_checking_syntax_growing_prefixes_retain_shared_work() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut root = imported(format, MachineTerm::Variable(Variable(989621)));
        let mask = imported(format, MachineTerm::uint64_constant(7));
        let zero = imported(format, MachineTerm::uint64_constant(0));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let fresh = imported(format, MachineTerm::Variable(Variable(989622 + index)));
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root.clone(), fresh],
                );
                let masked = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::BitwiseAnd,
                    [root.clone(), mask.clone()],
                );
                let unchanged = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::BitwiseOr,
                    [masked.clone(), zero.clone()],
                );
                assert_eq!(TermRewrite::checking_wide_syntax(&unchanged), masked);
                assert_eq!(TermRewrite::checking_wide_syntax(&root), root);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
