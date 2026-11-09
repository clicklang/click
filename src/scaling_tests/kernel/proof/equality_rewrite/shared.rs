#[test]
fn exact_rewrite_keeps_cold_and_growing_shared_goals() {
    for ty in [T::Int32, T::UInt64] {
        for fold in [false, true] {
            for prefixes in [false, true] {
                let mut samples = Vec::new();
                for size in [16, 64, 256] {
                    let _session = VerificationSession::enter();
                    let x = Variable(1006300);
                    let y = Variable(1006301);
                    let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), x);
                    let mut expected = KernelTerm::variable(KernelType::C(ty.c_type()), y);
                    let goal = |root: KernelTerm| {
                        let value = if fold {
                            let start =
                                SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(x))
                                    // The endpoint wrapper currently uses an Int32
                                    // observation tag even for UInt64 fold syntax.
                                    .with_shared_operand(
                                        root.with_machine_observation_type(T::Int32),
                                    )
                                    .unwrap();
                            let end = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(
                                Variable(1006303),
                            ));
                            IntegerTerm::RangeFold {
                                index: if ty == T::Int32 {
                                    IntegerRangeFoldIndex::Int32 { start, end }
                                } else {
                                    IntegerRangeFoldIndex::UInt64 { start, end }
                                },
                                initial: IntegerTerm::Constant(0.into()).into(),
                                accumulator: Variable(1006304),
                                item: Variable(1006305),
                                body: IntegerTerm::Variable(Variable(1006304)).into(),
                            }
                        } else {
                            IntegerTerm::Machine(
                                SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
                            )
                        };
                        Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(
                                value.into(),
                                IntegerTerm::Variable(Variable(1006302)).into(),
                            ),
                            true,
                        )
                    };
                    let equality = Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: if ty == T::Int32 { T::Int32 } else { T::Int64 },
                            relation: CompareRelation::Equal,
                            left: Box::new(MachineTerm::Variable(x)),
                            right: Box::new(MachineTerm::Variable(y)),
                        },
                        true,
                    );
                    let exports = KernelTermExport::machine_export_count();
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        for i in 0..size {
                            root = KernelTerm::machine_binary_shared(
                                ty,
                                O::Add,
                                [root.clone(), root.clone()],
                            );
                            expected = KernelTerm::machine_binary_shared(
                                ty,
                                O::Add,
                                [expected.clone(), expected.clone()],
                            );
                            if prefixes || i + 1 == size {
                                let rewritten =
                                    super::super::super::rewrite_with_admitted_equality_as_written(
                                        &goal(root.clone()),
                                        &equality,
                                    )
                                    .unwrap();
                                assert_eq!(rewritten, goal(expected.clone()));
                            }
                        }
                    });
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    samples.push(work);
                }
                for pair in samples.windows(2) {
                    assert!(
                        pair[1] <= pair[0] * 5,
                        "{ty:?}, fold={fold}, prefixes={prefixes}: {samples:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn opaque_replacement_rewrites_keep_cold_dags_shared() {
    for exact in [false, true] {
        for ty in [T::Int32, T::UInt64] {
            let mut samples = Vec::new();
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let x = MachineTerm::Variable(Variable(1006500));
                let to = MachineTerm::If {
                    condition: ConditionTerm::Variable(Variable(1006501)).into(),
                    then_term: x.clone().into(),
                    else_term: MachineTerm::Variable(Variable(1006502)).into(),
                };
                let mut root = imported(ty, &x);
                for _ in 0..size {
                    root = KernelTerm::machine_binary_shared(ty, O::Add, [root.clone(), root]);
                }
                let input = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap(),
                );
                let exports = KernelTermExport::machine_export_count();
                let (mut result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    if exact {
                        rewrite(&root, &x, &to, |leaf| {
                            super::super::super::rewrite_term(leaf, &x, &to)
                        })
                        .unwrap()
                    } else {
                        let mut rewrite =
                            crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(
                                &x, &to,
                            );
                        let IntegerTerm::Machine(value) = rewrite.integer(&input) else {
                            panic!("observation")
                        };
                        assert!(rewrite.refusal().is_none());
                        value.shared_operand().unwrap().clone()
                    }
                });
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                for _ in 0..size {
                    let KernelTermNode::MachineBinary { arguments, .. } = result.node() else {
                        panic!("shared sum")
                    };
                    assert_eq!(arguments[0], arguments[1]);
                    result = arguments[0].clone();
                }
                assert_eq!(KernelTermExport::machine(&result).unwrap(), to);
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(pair[1] <= pair[0] * 5, "exact={exact}, {ty:?}: {samples:?}");
            }
        }
    }
}
