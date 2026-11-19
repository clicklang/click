// Scaling tests of `src/kernel/spec.rs` (module `algebraic_term_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn algebraic_integer_match_scales_with_nested_depth() {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![AlgebraicValueType::Integer],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "Box".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Box".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let mut previous = None;
    for depth in [8, 16, 32, 64] {
        let mut expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Constructor {
                variant: "Box".into(),
                fields: vec![SpecAlgebraicValue::Integer(SpecIntegerExpression::Term(
                    IntegerTerm::var(Variable(100_000 + depth as u64 - 1)),
                ))],
            },
        };
        for level in (0..depth).rev() {
            expression = SpecAlgebraicExpression {
                algebraic_type: ty.clone(),
                node: SpecAlgebraicExpressionNode::Match {
                    scrutinee: Box::new(SpecAlgebraicExpression {
                        algebraic_type: ty.clone(),
                        node: SpecAlgebraicExpressionNode::Variable(Variable(
                            200_000 + level as u64,
                        )),
                    }),
                    arms: vec![SpecAlgebraicResultMatchArm {
                        variant: "Box".into(),
                        bindings: vec![format!("n{level}").into()],
                        binding_types: vec![AlgebraicValueType::Integer],
                        binding_variables: vec![Some(Variable(100_000 + level as u64))],
                        body: Box::new(expression),
                    }],
                },
            };
        }
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::algebraic_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_algebraic_at_state_in(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap()
        });
        assert!(
            budget.integer_bindings.is_empty(),
            "arm scopes must be restored"
        );
        assert_eq!(paths.len(), 1);
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        let AlgebraicResult::Shared(mut value) = paths[0].value.clone() else {
            panic!("retained result");
        };
        let mut last_binding = None;
        for _ in 0..depth {
            let crate::kernel::KernelTermNode::Match(matched) = value.node() else {
                panic!("expected nested common match");
            };
            let crate::kernel::KernelTermNode::Variable(variable) =
                matched.arms[0].bindings[0].node()
            else {
                panic!("Integer declaration");
            };
            last_binding = Some(AlgebraicValue::Integer(IntegerTerm::var(*variable)));
            value = matched.arguments[1].clone();
        }
        let crate::kernel::KernelTermNode::Constructor(constructor) = value.node() else {
            panic!("common constructor");
        };
        assert_eq!(constructor.algebraic_type, ty);
        assert_eq!(constructor.variant, "Box");
        assert_eq!(constructor.fields.len(), 1);
        let AlgebraicValue::Integer(binding) = last_binding.unwrap() else {
            unreachable!();
        };
        assert_eq!(
            constructor.fields[0],
            KernelTermImport::default().integer(&binding.into())
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        let (native, export_work) = crate::instrumentation::measure_deterministic_work(|| {
            paths[0].value.clone().into_native_compat()
        });
        assert!(matches!(native.node, AlgebraicTermNode::Match { .. }));
        assert!(
            export_work <= 20 * depth + 20,
            "depth={depth}, export work={export_work}"
        );
        assert!(work <= 256 * depth + 128, "depth {depth}: {work}");
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5 / 2 + 64,
                "nested match work must remain linear: {previous} -> {work}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn signed_match_definedness_does_not_scan_constructor_facts() {
    for related in [false, true] {
        let mut work = Vec::new();
        for size in [8u64, 16, 32, 64] {
            let mut context = PureFactContext::new();
            let constructor = maybe_constructor(Some(int32(7)));
            for index in 0..size {
                let right = if related && index > 0 {
                    maybe_variable(Variable(1_000 + index - 1))
                } else {
                    constructor.clone()
                };
                context = context.assume_proposition(Proposition::Equal(
                    Term::Algebraic(maybe_variable(Variable(1_000 + index)).into()),
                    Term::Algebraic(right.into()),
                ));
            }
            let expression = signed_value_or_match(Variable(1_000 + size - 1));
            let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
                evaluate_spec_expression_paths_with_loop_entry_in(
                    &ExecutionState::new(),
                    &expression,
                    None,
                    &context,
                    &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
                )
                .unwrap()
            });
            assert_eq!(paths.len(), 1);
            assert!(!paths[0].obligations.is_empty());
            work.push(measured);
        }
        assert!(
            work.windows(2)
                .all(|pair| pair[1] <= pair[0] + pair[0] / 4 + 16),
            "related={related}, work={work:?}"
        );
    }
}

#[test]
fn nested_algebraic_calls_retain_shared_arguments_with_linear_work() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = maybe_type();
        let mut expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(999705)),
        };
        for _ in 0..size {
            expression = SpecAlgebraicExpression {
                algebraic_type: ty.clone(),
                node: SpecAlgebraicExpressionNode::PureFunctionApplication {
                    name: "nested_algebraic_call".into(),
                    arguments: vec![SpecPureFunctionArgument::Algebraic(expression)],
                },
            };
        }
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::algebraic_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_algebraic_at_state_in(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert!(work <= 100 * size + 100, "size={size} work={work}");
        let AlgebraicResult::Shared(mut root) = paths[0].value.clone() else {
            panic!("retained call");
        };
        for _ in 0..size {
            let KernelTermNode::AlgebraicCall(call) = root.node() else {
                panic!("nested common call");
            };
            assert_eq!(call.shared_machine_arguments, vec![None]);
            root = call.arguments[0].clone();
        }
        assert!(
            matches!(root.node(), KernelTermNode::Variable(variable) if *variable == Variable(999705))
        );
    }
}

#[test]
fn nested_algebraic_conditionals_retain_branches_with_linear_work() {
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = maybe_type();
        let leaf = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(999725)),
        };
        let mut expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(999726)),
        };
        for _ in 0..size {
            expression = SpecAlgebraicExpression {
                algebraic_type: ty.clone(),
                node: SpecAlgebraicExpressionNode::If {
                    condition: Box::new(SpecProposition::IntegerComparison {
                        left: SpecIntegerExpression::Term(IntegerTerm::var(Variable(999727))),
                        operator: IntegerComparisonOperator::Equal,
                        right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                    }),
                    then_branch: Box::new(expression),
                    else_branch: Box::new(leaf.clone()),
                },
            };
        }
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::algebraic_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_algebraic_at_state_in(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert!(work <= 200 * size + 200, "size={size} work={work}");
        let AlgebraicResult::Shared(mut root) = paths[0].value.clone() else {
            panic!("retained conditional")
        };
        for _ in 0..size {
            let KernelTermNode::AlgebraicIf { arguments } = root.node() else {
                panic!("nested conditional")
            };
            root = arguments[1].clone();
        }
        assert!(
            matches!(root.node(), KernelTermNode::Variable(variable) if *variable == Variable(999726))
        );
    }
}

#[test]
fn algebraic_constructor_handoffs_do_not_export_growing_fields() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let inner = maybe_type();
        let outer = envelope_type(&inner);
        let mut field =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999763));
        for _ in 0..size {
            field = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [field.clone(), field],
            );
        }
        let root = crate::kernel::KernelConstructor {
            algebraic_type: inner.clone(),
            variant: "Some".into(),
            fields: vec![field],
        }
        .into_term();
        let mut values = crate::persistent::PersistentMap::default();
        values.insert("seed".into(), root.clone());
        let expression = SpecAlgebraicExpression {
            algebraic_type: outer,
            node: SpecAlgebraicExpressionNode::Constructor {
                variant: "Present".into(),
                fields: vec![SpecAlgebraicValue::Algebraic(SpecAlgebraicExpression {
                    algebraic_type: inner,
                    node: SpecAlgebraicExpressionNode::Binding("seed".into()),
                })],
            },
        };
        let state = ExecutionState::new();
        let scope = SpecScope {
            values: Some(&values),
            ..SpecScope::unbound(&state, None)
        };
        let exports = (
            KernelTermExport::algebraic_export_count(),
            KernelTermExport::machine_export_count(),
        );
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
            )
            .unwrap()
        });
        let AlgebraicResult::Shared(result) = &paths[0].value else {
            panic!("retained result");
        };
        let KernelTermNode::Constructor(constructor) = result.node() else {
            panic!("constructor");
        };
        assert_eq!(constructor.fields, vec![root]);
        assert_eq!(
            (
                KernelTermExport::algebraic_export_count(),
                KernelTermExport::machine_export_count()
            ),
            exports
        );
        assert!(work < 100, "size={size} work={work}");
    }
}

#[test]
fn algebraic_proposition_handoffs_keep_growing_scrutinees_without_export() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = maybe_type();
        let plain = KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(998_310));
        let guard = KernelTerm::variable(KernelType::Bool, Variable(998_311));
        let mut shared = plain.clone();
        for _ in 0..size {
            shared =
                KernelTerm::algebraic_if_raw(ty.clone(), [guard.clone(), shared.clone(), shared]);
        }
        let state = ExecutionState::new();
        let mut values = crate::persistent::PersistentMap::default();
        values.insert("adt".into(), shared.clone());
        let scope = SpecScope {
            values: Some(&values),
            ..SpecScope::unbound(&state, None)
        };
        let left = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Binding("adt".into()),
        };
        let right = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(998_310)),
        };
        let exports = KernelTermExport::algebraic_export_count();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            let paths = lower_spec_algebraic_comparison_at_state_in(
                scope,
                &left,
                true,
                &right,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap();
            let [path] = paths.as_slice() else {
                panic!("one equality path")
            };
            let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) =
                &path.proposition
            else {
                panic!("evaluated algebraic equality")
            };
            assert_eq!(left.root(), Some(&shared));
            assert_eq!(right.root(), Some(&plain));

            let mut execution = ExecutionBudget::new();
            let cases = algebraic_case_paths_in(
                &AlgebraicResult::Shared(shared.clone()),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap();
            assert_eq!(cases.len(), ty.variants.len());
            for case in cases {
                assert_eq!(case.facts.len(), 1);
                let fact = &case.facts[0];
                let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) =
                    fact.proposition()
                else {
                    panic!("algebraic case equation")
                };
                assert_eq!(left.root(), Some(&shared));
                assert!(
                    matches!(right.root().unwrap().node(), KernelTermNode::Constructor(constructor) if constructor.variant == case.variant)
                );
            }
        });
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert!(!shared.has_cached_native_argument());
        assert!(work <= 24 * size + 512, "size={size} work={work}");
    }
}
