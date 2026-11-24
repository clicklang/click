use super::*;

#[test]
fn exact_float_bound_checks_only_the_input_endpoint() {
    let _session = VerificationSession::enter();
    let ty = KernelType::Program(ProgramType::Float32);
    let input = KernelTerm::variable(ty.clone(), Variable(995728));
    let other = KernelTerm::variable(ty, Variable(995729));
    let narrow = KernelFloatType::Float32;
    let wide = KernelFloatType::Float64;
    let upper = |format, operand, endpoint: MachineTerm| {
        let literal = KernelTermImport::default().float(format, &endpoint);
        let condition =
            KernelTerm::float_compare(format, ComparisonOperator::LessThan, [operand, literal])
                .unwrap();
        Proposition::condition_is(StoredConditionTerm::from_root(condition).unwrap(), true)
    };
    let widened = KernelTerm::float_convert(wide, ProgramType::Float32, input.clone()).unwrap();
    let goal = upper(
        wide,
        widened,
        MachineTerm::uint64_constant(1.0f64.to_bits()),
    );
    let required = upper(
        narrow,
        input.clone(),
        MachineTerm::constant(1.0f32.to_bits()),
    );
    for related in [false, true] {
        let mut cost = Vec::new();
        for size in [8, 32, 128] {
            let mut facts = (0..size)
                .map(|index| {
                    upper(
                        narrow,
                        if related {
                            input.clone()
                        } else {
                            other.clone()
                        },
                        MachineTerm::constant((index as f32 + 2.0).to_bits()),
                    )
                })
                .collect::<Vec<_>>();
            let missing = PureFactStore::from_ordered(&facts);
            facts.push(required.clone());
            let present = PureFactStore::from_ordered(&facts);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(known_bridge_leaf(&goal, &|p| present.pure_known_available(p)));
                assert!(!known_bridge_leaf(&goal, &|p| missing.pure_known_available(p)));
            });
            cost.push(work);
        }
        assert!(
            cost.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
            "{cost:?}"
        );
    }
}

#[test]
fn signed_product_bound_checks_only_the_exact_guards() {
    let _session = VerificationSession::enter();
    let ty = MachineIntegerType::Int32;
    let observed = |id| IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(id))).unwrap();
    let x = observed(995725);
    let y = observed(995726);
    let maximum = IntegerTerm::constant_i64(i64::from(i32::MAX));
    let goal = le(
        IntegerTerm::Multiply(x.clone().into(), y.into()),
        maximum.clone(),
    );
    let guards = crate::kernel::proof::arithmetic_special::signed_product_guard_candidates(&goal)
        .next()
        .unwrap();
    assert_eq!(guards.len(), 3);
    for related in [false, true] {
        let mut cost = Vec::new();
        for size in [8, 32, 128] {
            let mut facts = (0..size)
                .map(|index| {
                    le(
                        if related { x.clone() } else { observed(995727) },
                        IntegerTerm::constant_i64(i64::from(index + 1)),
                    )
                })
                .collect::<Vec<_>>();
            facts.extend(guards[..2].iter().cloned());
            let missing = PureFactStore::from_ordered(&facts);
            facts.push(guards[2].clone());
            let present = PureFactStore::from_ordered(&facts);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(known_bridge_leaf(&goal, &|p| present.pure_known_available(p)));
                assert!(!known_bridge_leaf(&goal, &|p| missing.pure_known_available(p)));
            });
            cost.push(work);
        }
        assert!(
            cost.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
            "{cost:?}"
        );
    }
}

#[test]
fn shift_definedness_bridges_read_only_the_exact_count_bounds() {
    use crate::kernel::machine_integer::{
        comparison::condition_for_operand_views, range::constant_word,
    };
    for (signed, unsigned) in [
        (MachineIntegerType::Int32, MachineIntegerType::UInt32),
        (MachineIntegerType::Int64, MachineIntegerType::UInt64),
    ] {
        let _session = VerificationSession::enter();
        let count = MachineTerm::Variable(Variable(995760));
        let other = MachineTerm::Variable(Variable(995761));
        let width = unsigned.format().bits();
        let maximum = signed.format().bounds().1;
        let observe = |ty, op, left, right| {
            IntegerTerm::from_machine(
                ty,
                MachineTerm::Binary {
                    format: ty,
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            )
            .unwrap()
        };
        let masked = observe(
            unsigned,
            MachineBinaryOp::BitwiseAnd,
            count.clone(),
            constant_word(unsigned, &(width - 1).into()).unwrap(),
        );
        let mask_goal = equality(
            masked,
            IntegerTerm::from_machine(unsigned, count.clone()).unwrap(),
        );
        let shift = |ty, d| {
            observe(
                ty,
                MachineBinaryOp::ShiftRight,
                constant_word(ty, &maximum).unwrap(),
                d,
            )
        };
        let right_shift = shift(signed, count.clone());
        let shift_goal = equality(right_shift.clone(), shift(unsigned, count.clone()));
        let different_count = equality(right_shift, shift(unsigned, other.clone()));
        let bound = |d, endpoint: u32| {
            let endpoint = constant_word(unsigned, &endpoint.into()).unwrap();
            condition_for_operand_views(
                unsigned,
                CompareRelation::LessThan,
                [
                    MachineOperandView::Legacy(d),
                    MachineOperandView::Legacy(&endpoint),
                ],
            )
            .truth_claim(true)
        };
        for related in [false, true] {
            let mut expected_work = None;
            for size in [8, 32, 128] {
                let noise = (0..size)
                    .map(|i| bound(if related { &count } else { &other }, width + i + 1))
                    .collect::<Vec<_>>();
                let missing = PureFactStore::from_ordered(&noise);
                let mut premises = noise;
                premises.extend([bound(&count, width), bound(&other, width)]);
                let present = PureFactStore::from_ordered(&premises);
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for goal in [&mask_goal, &shift_goal] {
                        assert!(known_bridge_leaf(goal, &|p| present.pure_known_available(p)));
                        assert!(!known_bridge_leaf(goal, &|p| missing.pure_known_available(p)));
                    }
                    assert!(
                        !known_bridge_leaf(&different_count, &|p| present.pure_known_available(p))
                    );
                });
                let baseline = *expected_work.get_or_insert(work);
                // Indexed lookups can visit a different number of nodes as
                // the fact store grows. A scan of either bucket would exceed
                // this fixed allowance.
                assert!(
                    work <= baseline + 16,
                    "{unsigned:?}, related={related}, facts={size}: {work} > {baseline} + 16"
                );
            }
        }
    }
}

#[test]
fn local_observation_rules_ignore_unrelated_facts_and_related_bound_buckets() {
    for related in [false, true] {
        let _session = VerificationSession::enter();
        let (observed, exact) = operation(MachineIntegerType::Int64, Operation::Add).unwrap();
        let goal = equality(observed, exact.clone());
        let mut costs = Vec::new();
        for size in [8, 32, 128] {
            let mut premises = Vec::new();
            for i in 0..size {
                premises.push(if related {
                    le(
                        exact.clone(),
                        IntegerTerm::Constant(BigInt::from(i) + (BigInt::from(1) << 64usize)),
                    )
                } else {
                    equality(
                        IntegerTerm::var(Variable(996000 + i)),
                        IntegerTerm::var(Variable(997000 + i)),
                    )
                });
            }
            let missing = PureFactStore::from_ordered(&premises);
            premises.extend(bounds(&exact, MachineIntegerType::Int64));
            let facts = PureFactStore::from_ordered(&premises);
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|p| facts.pure_known_available(p))
            });
            assert!(accepted);
            let (_, miss) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(!known_bridge_leaf(&goal, &|p| missing.pure_known_available(p)));
            });
            costs.push(work + miss);
        }
        assert!(
            costs.windows(2).all(|p| p[1] <= 2 * p[0]),
            "related={related}: {costs:?}"
        );
    }
}

#[test]
fn observation_leaves_keep_growing_arithmetic_and_comparison_dags_shared() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int64;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(995720));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let operand =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap());
        let exact = IntegerTerm::Add(operand.clone().into(), operand.clone().into());
        let operation = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [root.clone(), root.clone()],
        );
        let observed =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, operation).unwrap());
        let guard = KernelTerm::boolean_comparison_raw(
            ty,
            CompareRelation::LessEqual,
            [
                root.clone(),
                KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(995721)),
            ],
        );
        let condition = written_guard(BooleanOperandView::Shared(&guard)).unwrap();
        let (_, _, operands) = BooleanOperandView::Shared(&guard).comparison().unwrap();
        let complementary = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            ty,
            CompareRelation::GreaterThan,
            operands,
        );
        let complementary = PureFactStore::from_ordered(&[complementary.truth_claim(true)]);
        let narrow = MachineIntegerType::UInt8;
        let narrow_arm =
            KernelTerm::machine_cast_shared(MachineCastSpelling::Generic, ty, narrow, root.clone());
        let other_arm =
            KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(995722));
        let narrow_other = KernelTerm::machine_cast_shared(
            MachineCastSpelling::Generic,
            ty,
            narrow,
            other_arm.clone(),
        );
        let narrow_conditional = KernelTerm::machine_if_shared(
            narrow,
            [guard.clone(), narrow_other, narrow_arm.clone()],
        );
        let narrow_comparison = StoredConditionTerm::from_root(KernelTerm::boolean_comparison_raw(
            narrow,
            CompareRelation::Equal,
            [narrow_conditional, narrow_arm],
        ))
        .unwrap();
        let narrow_goal = Proposition::condition_is(narrow_comparison.clone(), true);
        let conditional = KernelTerm::machine_if_shared(ty, [guard, root, other_arm.clone()]);
        let conditional =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, conditional).unwrap());
        let other_arm =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, other_arm).unwrap());
        let mut premises = bounds(&exact, ty).to_vec();
        premises.push(Proposition::condition_is(condition, true));
        let facts = PureFactStore::from_ordered(&premises);
        let missing = PureFactStore::from_ordered(&[]);
        let operation_goal = equality(observed, exact);
        let conditional_goal = equality(conditional.clone(), operand);
        let complementary_goal = equality(conditional, other_arm);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..2 {
                assert!(known_bridge_leaf(&operation_goal, &|p| facts.pure_known_available(p)));
                assert!(!known_bridge_leaf(&operation_goal, &|p| missing.pure_known_available(p)));
                assert!(known_bridge_leaf(&conditional_goal, &|p| facts.pure_known_available(p)));
                assert!(known_bridge_leaf(&complementary_goal, &|p| complementary
                    .pure_known_available(p)));
                assert!(!known_bridge_leaf(&conditional_goal, &|p| missing.pure_known_available(p)));
                assert!(known_bridge_leaf(&narrow_goal, &|p| complementary.pure_known_available(p)));
                assert!(
                    !narrow_machine_arm(&narrow_comparison, &|p| missing.pure_known_available(p))
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(samples.windows(2).all(|p| p[1] <= 5 * p[0]), "{samples:?}");
}

#[test]
fn neutral_bitwise_leaves_keep_large_operands_shared_without_fact_queries() {
    let mut costs = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996500));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let operand =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap());
        let zero = KernelTerm::retained_machine_operand(
            ty,
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(0)),
        );
        let mut goals = Vec::new();
        for op in [MachineBinaryOp::BitwiseAnd, MachineBinaryOp::BitwiseOr] {
            for parts in [[root.clone(), zero.clone()], [zero.clone(), root.clone()]] {
                let word = KernelTerm::machine_binary_shared(ty, op, parts);
                let observed =
                    IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, word).unwrap());
                let result = if op == MachineBinaryOp::BitwiseAnd {
                    IntegerTerm::constant_i64(0)
                } else {
                    operand.clone()
                };
                goals.push(equality(observed.clone(), result));
                goals.push(equality(observed, IntegerTerm::constant_i64(1)));
            }
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (i, goal) in goals.iter().enumerate() {
                assert_eq!(
                    known_bridge_leaf(goal, &|_| panic!("neutral computation queried facts")),
                    i % 2 == 0
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(work);
    }
    assert!(costs.windows(2).all(|p| p[0] == p[1]), "{costs:?}");
}

#[test]
fn finite_float_reflexivity_uses_one_exact_classification() {
    let _session = VerificationSession::enter();
    let finite = |id| {
        Proposition::condition_is(
            ConditionTerm::float32_classification(
                MachineTerm::Variable(Variable(id)),
                FloatClassification::Finite,
            ),
            true,
        )
    };
    let operand = MachineTerm::Variable(Variable(996800));
    let goal = Proposition::condition_is(
        ConditionTerm::float32_compare(operand.clone(), operand, ComparisonOperator::Equal),
        true,
    );
    let mut costs = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut premises = (0..size).map(|i| finite(997000 + i)).collect::<Vec<_>>();
        let missing = PureFactStore::from_ordered(&premises);
        premises.push(finite(996800));
        let facts = PureFactStore::from_ordered(&premises);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (context, expected) in [(&missing, false), (&facts, true)] {
                let lookups = std::cell::Cell::new(0);
                assert_eq!(
                    known_bridge_leaf(&goal, &|premise| {
                        lookups.set(lookups.get() + 1);
                        assert_eq!(premise, &finite(996800));
                        context.pure_known_available(premise)
                    }),
                    expected
                );
                assert_eq!(lookups.get(), 1);
            }
        });
        costs.push(work);
    }
    assert!(costs.windows(2).all(|p| p[1] <= 2 * p[0]), "{costs:?}");
}

#[test]
fn non_numeric_arm_equations_use_only_the_written_guard() {
    let _session = VerificationSession::enter();
    let guard = ConditionTerm::Variable(Variable(998000));
    let a = ConditionTerm::Variable(Variable(998001));
    let b = ConditionTerm::Variable(Variable(998002));
    let boolean = Proposition::condition_is(
        ConditionTerm::bool_equal(ConditionTerm::bool_if(guard.clone(), a.clone(), b), a),
        true,
    );
    let variants: std::sync::Arc<[AlgebraicVariantType]> = ["A", "B"]
        .into_iter()
        .map(|name| AlgebraicVariantType {
            name: name.into(),
            fields: vec![],
        })
        .collect::<Vec<_>>()
        .into();
    let key = AlgebraicValueType::Algebraic {
        name: "ConditionalTest".into(),
        arguments: vec![],
    };
    let ty = AlgebraicType {
        rigid: false,
        name: "ConditionalTest".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
            key, variants,
        )]))),
    };
    let constructor = |name: &str| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: name.into(),
            fields: vec![],
        },
    };
    let a = constructor("A");
    let algebraic = Proposition::Equal(
        Term::Algebraic(
            AlgebraicTerm::if_then_else(guard.clone(), a.clone(), constructor("B")).into(),
        ),
        Term::Algebraic(a.into()),
    );
    let mut costs = Vec::new();
    for size in [8, 32, 128, 512] {
        let unrelated = (0..size)
            .map(|index| ConditionTerm::Variable(Variable(998100 + index)).truth_claim(true))
            .collect::<Vec<_>>();
        let contexts = [None, Some(false), Some(true)].map(|polarity| {
            let mut premises = unrelated.clone();
            premises.extend(polarity.map(|polarity| guard.truth_claim(polarity)));
            (polarity, PureFactStore::from_ordered(&premises))
        });
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (polarity, facts) in &contexts {
                for goal in [&boolean, &algebraic] {
                    assert_eq!(
                        known_bridge_leaf(goal, &|premise| {
                            assert!(
                                premise == &guard.truth_claim(true)
                                    || premise == &guard.truth_claim(false)
                            );
                            facts.pure_known_available(premise)
                        }),
                        *polarity == Some(true),
                    );
                }
            }
        });
        costs.push(work);
    }
    assert!(costs.windows(2).all(|p| p[1] <= 2 * p[0]), "{costs:?}");
}
