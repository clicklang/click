#[test]
fn comparison_output_producers_keep_growing_logical_and_integer_roots() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut logical = KernelTerm::variable(KernelType::Bool, Variable(10993731));
        let other_logical = KernelTerm::variable(KernelType::Bool, Variable(10993732));
        let mut integer = KernelTerm::variable(KernelType::Integer, Variable(10993733));
        let other_integer = KernelTerm::variable(KernelType::Integer, Variable(10993734));
        for _ in 0..size {
            logical = KernelTerm::boolean_equal_raw([logical.clone(), logical]);
            integer = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![integer.clone(), integer],
            )
            .unwrap();
        }
        let expected_logical = KernelTerm::boolean_equal([logical.clone(), other_logical.clone()]);
        let expected_integer = KernelTerm::integer_comparison(
            IntegerComparisonOperator::LessThan,
            [integer.clone(), other_integer.clone()],
        )
        .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let logical_output = SpecValue::Shared(logical.clone())
                .comparison(
                    ComparisonOperator::Equal,
                    &SpecValue::Shared(other_logical.clone()),
                )
                .unwrap()
                .unwrap();
            let literal_output = SpecValue::Shared(logical.clone())
                .comparison(
                    ComparisonOperator::Equal,
                    &SpecValue::Native(ProgramValue::bool_constant(true)),
                )
                .unwrap()
                .unwrap();
            let Proposition::ConditionIs(literal_condition, literal_truth) = literal_output else {
                unreachable!();
            };
            assert_eq!(literal_condition.root(), Some(&logical));
            assert!(literal_truth);
            let integer_output = retained_integer_comparison(
                &IntegerResult::from_kernel(integer.clone()),
                IntegerComparisonOperator::LessThan,
                &IntegerResult::from_kernel(other_integer.clone()),
            );
            for _ in 0..32 {
                let Proposition::ConditionIs(value, truth) = logical_output.clone() else {
                    unreachable!();
                };
                assert_eq!(value.root(), Some(&expected_logical));
                assert!(truth);
                assert_eq!(integer_output.0.clone().root(), Some(&expected_integer));
                assert!(integer_output.1);
            }
        });
        for root in [
            &logical,
            &other_logical,
            &integer,
            &other_integer,
            &expected_logical,
            &expected_integer,
        ] {
            assert!(!root.has_cached_native_argument());
        }
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}

#[test]
fn float_comparison_outputs_read_shared_constant_and_symbolic_dags_once() {
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            for constant in [false, true] {
                let mut root = if constant {
                    KernelTermImport::default().argument(&PureFunctionArgument::Value(
                        format.value(match format {
                            KernelFloatType::Float32 => {
                                OldMachineTerm::uint32_constant(0x3f80_0000)
                            }
                            KernelFloatType::Float64 => {
                                OldMachineTerm::uint64_constant(0x3ff0_0000_0000_0000)
                            }
                        }),
                    ))
                } else {
                    KernelTerm::variable(
                        KernelType::Program(format.program_type()),
                        Variable(10993735),
                    )
                };
                for _ in 0..size {
                    root = KernelTerm::float_binary(
                        format,
                        FloatBinaryOperator::Add,
                        [root.clone(), root],
                    )
                    .unwrap();
                }
                let exports = KernelTermExport::float_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let output = SpecValue::Shared(root.clone())
                        .comparison(ComparisonOperator::Equal, &SpecValue::Shared(root.clone()))
                        .unwrap()
                        .unwrap();
                    let Proposition::ConditionIs(condition, truth) = output else {
                        unreachable!();
                    };
                    assert!(truth);
                    let retained = condition.root().unwrap();
                    if constant {
                        assert!(matches!(retained.node(), KernelTermNode::BoolLiteral(true)));
                    } else {
                        let KernelTermNode::FloatCompare { arguments, .. } = retained.node() else {
                            panic!("shared comparison");
                        };
                        assert_eq!(arguments, &[root.clone(), root.clone()]);
                    }
                });
                assert_eq!(KernelTermExport::float_export_count(), exports);
                assert!(!root.has_cached_native_argument());
                assert!(
                    work <= 128 * size + 256,
                    "size={size} constant={constant} work={work}"
                );
            }
        }
    }
}
