use super::*;

fn maybe_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::C(CType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "None".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Some".to_string(),
            fields: vec![AlgebraicValueType::C(CType::Int32)],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Maybe".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Maybe".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

#[test]
fn algebraic_integer_match_reconnects_symbolic_and_concrete_fields() {
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
    let payload = IntegerTerm::constant_i64(7);
    let constructor = |field| SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Box".into(),
            fields: vec![SpecAlgebraicValue::Integer(SpecIntegerExpression::Term(
                field,
            ))],
        },
    };
    let arm = SpecAlgebraicResultMatchArm {
        variant: "Box".into(),
        bindings: vec!["n".into()],
        binding_types: vec![AlgebraicValueType::Integer],
        binding_variables: vec![Some(Variable(12345))],
        body: Box::new(constructor(IntegerTerm::var(Variable(12345)))),
    };
    for scrutinee in [
        SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(23456)),
        },
        constructor(payload.clone()),
    ] {
        let concrete = matches!(
            scrutinee.node,
            SpecAlgebraicExpressionNode::Constructor { .. }
        );
        let expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![arm.clone()],
            },
        };
        let paths = evaluate_spec_algebraic_at_state_in(
            &CState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        let (body, expected) = if concrete {
            (&paths[0].value, AlgebraicValue::Integer(payload.clone()))
        } else {
            let AlgebraicTermNode::Match { arms, .. } = &paths[0].value.node else {
                panic!("symbolic match must remain a match");
            };
            (&arms[0].body, arms[0].bindings[0].clone())
        };
        let AlgebraicTermNode::Constructor { fields, .. } = &body.node else {
            panic!("arm must return its constructor");
        };
        assert_eq!(fields, &vec![expected]);
    }
    // Missing IDs, mismatched carriers, and duplicate field names cannot
    // authorize an ambiguous payload substitution.
    assert!(spec_algebraic_result_match_arms_are_well_formed(
        &ty,
        std::slice::from_ref(&arm)
    ));
    for metadata in [
        vec![],
        vec![None],
        vec![Some(Variable(1)), Some(Variable(1))],
    ] {
        let mut bad = arm.clone();
        bad.binding_variables = metadata;
        assert!(!spec_algebraic_result_match_arms_are_well_formed(
            &ty,
            &[bad]
        ));
    }
    let mut pair_ty = ty.clone();
    pair_ty.name = "Pair".into();
    pair_ty.variants = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![AlgebraicValueType::Integer; 2],
    }]
    .into();
    pair_ty.schemas = std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        AlgebraicValueType::Algebraic {
            name: "Pair".into(),
            arguments: vec![],
        },
        pair_ty.variants.clone(),
    )])));
    let mut pair_arm = arm.clone();
    pair_arm.bindings = vec!["a".into(), "b".into()];
    pair_arm.binding_types = vec![AlgebraicValueType::Integer; 2];
    pair_arm.binding_variables = vec![Some(Variable(1)), Some(Variable(2))];
    assert!(spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm.clone()]
    ));
    pair_arm.binding_variables = vec![Some(Variable(1)); 2];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm.clone()]
    ));
    pair_arm.binding_variables = vec![Some(Variable(1)), Some(Variable(2))];
    pair_arm.bindings = vec!["a".into(), "a".into()];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm]
    ));
    let mut bad = arm;
    bad.binding_types = vec![AlgebraicValueType::C(CType::Int32)];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &ty,
        &[bad]
    ));
}

fn value_or_match(scrutinee: SpecAlgebraicExpression) -> SpecExpression {
    SpecExpression::AlgebraicMatch {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            SpecAlgebraicMatchArm {
                variant: "None".to_string(),
                bindings: Vec::new(),
                binding_types: Vec::new(),
                body: SpecExpression::Value(int32(9)),
            },
            SpecAlgebraicMatchArm {
                variant: "Some".to_string(),
                bindings: vec!["value".to_string()],
                binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                body: SpecExpression::CExpression(CExpression::Variable("value".to_string())),
            },
        ],
    }
}

fn envelope_type(maybe_type: &AlgebraicType) -> AlgebraicType {
    let maybe_value_type = maybe_type.value_type();
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Missing".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Present".to_string(),
            fields: vec![maybe_value_type.clone()],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Envelope".to_string(),
        arguments: vec![AlgebraicValueType::C(CType::Int32)],
    };
    let mut schemas = maybe_type.schemas.definitions().clone();
    schemas.insert(value_type, variants.clone());
    AlgebraicType {
        rigid: false,
        name: "Envelope".to_string(),
        arguments: vec![AlgebraicValueType::C(CType::Int32)],
        variants,
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(schemas)),
    }
}

fn recursive_list_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::C(CType::Int32)];
    let value_type = AlgebraicValueType::Algebraic {
        name: "List".to_string(),
        arguments: arguments.clone(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Nil".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Cons".to_string(),
            fields: vec![AlgebraicValueType::C(CType::Int32), value_type.clone()],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: "List".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn ungrounded_recursive_type() -> AlgebraicType {
    let value_type = AlgebraicValueType::Algebraic {
        name: "Loop".to_string(),
        arguments: Vec::new(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Again".to_string(),
        fields: vec![value_type.clone()],
    }]
    .into();
    AlgebraicType {
        rigid: false,
        name: "Loop".to_string(),
        arguments: Vec::new(),
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn wide_type(variant_count: usize) -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::C(CType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = (0..variant_count)
        .map(|index| AlgebraicVariantType {
            name: format!("V{index}"),
            fields: vec![AlgebraicValueType::C(CType::Int32)],
        })
        .collect::<Vec<_>>()
        .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Wide".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Wide".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

#[test]
fn resource_initializer_capture_keeps_unknowns_and_calls_symbolic() {
    for variant_count in [1, 8, 128] {
        let ty = wide_type(variant_count);
        let variable = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
        };
        let captured =
            capture_spec_algebraic_value(&CState::new(), &variable, None, &PureFactContext::new())
                .unwrap();
        assert_eq!(captured.node, AlgebraicTermNode::Variable(Variable(41)));
        let call = SpecAlgebraicExpression {
            algebraic_type: ty,
            node: SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: "identity".into(),
                arguments: vec![SpecPureFunctionArgument::Algebraic(variable)],
            },
        };
        let captured =
            capture_spec_algebraic_value(&CState::new(), &call, None, &PureFactContext::new())
                .unwrap();
        assert!(matches!(
            captured.node,
            AlgebraicTermNode::PureFunctionApplication { .. }
        ));
    }
}

#[test]
fn arbitrary_algebraic_value_is_one_variable_without_eager_cases() {
    for variant_count in [1, 8, 128] {
        let algebraic_type = wide_type(variant_count);
        let expression = SpecAlgebraicExpression {
            algebraic_type: algebraic_type.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
        };
        let mut execution_budget = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution_budget);
        let next_variable = budget.next_kernel_variable;
        let paths = evaluate_spec_algebraic_at_state_in(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("a logical ADT variable lowers without case analysis");

        assert_eq!(paths.len(), 1);
        assert_eq!(budget.next_kernel_variable, next_variable);
        assert_eq!(
            paths[0].value,
            AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(Variable(41)),
            }
        );
    }
}

#[test]
fn cached_pointer_read_equations_do_not_escape_symbolic_match_arms() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer_type = AlgebraicValueType::C(CType::Int64Pointer);
    let value_type = AlgebraicValueType::Algebraic {
        name: "PointerBox".into(),
        arguments: vec![],
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![pointer_type],
    }]
    .into();
    let result_type = AlgebraicType {
        rigid: false,
        name: "PointerBox".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    };
    let address = Pointer::symbolic(Variable(71_040));
    let value = Pointer::symbolic(Variable(71_041));
    let memory = CMemory::new().store(
        address.clone(),
        CValue::typed_pointer(value, CType::Int64Pointer),
    );
    let body = SpecAlgebraicExpression {
        algebraic_type: result_type.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Box".into(),
            fields: vec![SpecAlgebraicValue::C(SpecExpression::MemoryLoad {
                memory: SpecMemory::Fixed(memory),
                pointer: Box::new(SpecExpression::Value(CValue::typed_pointer(
                    address,
                    CType::Int64PointerPointer,
                ))),
                value_type: CType::Int64Pointer,
            })],
        },
    };
    let state = CState::new();
    let context = PureFactContext::new();
    let direct = evaluate_spec_algebraic_at_state_in(
        &state,
        &body,
        None,
        &context,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    assert_eq!(direct[0].facts.len(), 1);
    assert!(direct[0].facts[0].is_logical_read_equation());
    assert!(capture_spec_algebraic_value(&state, &body, None, &context).is_ok());
    let expression = SpecAlgebraicExpression {
        algebraic_type: result_type,
        node: SpecAlgebraicExpressionNode::Match {
            scrutinee: Box::new(SpecAlgebraicExpression {
                algebraic_type: maybe_type(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(71_042)),
            }),
            arms: vec![
                SpecAlgebraicResultMatchArm {
                    variant: "None".into(),
                    bindings: vec![],
                    binding_types: vec![],
                    binding_variables: vec![],
                    body: Box::new(body.clone()),
                },
                SpecAlgebraicResultMatchArm {
                    variant: "Some".into(),
                    bindings: vec!["unused".into()],
                    binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                    binding_variables: vec![None],
                    body: Box::new(body),
                },
            ],
        },
    };
    let paths = evaluate_spec_algebraic_at_state_in(
        &state,
        &expression,
        None,
        &context,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    assert!(
        paths[0].facts.is_empty(),
        "arm-local equations must not become ambient facts"
    );
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn algebraic_type_schema_is_shared_by_variable_and_constructor_terms() {
    let algebraic_type = wide_type(128);
    let variable = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(7)),
    };
    let constructor = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "V0".to_string(),
            fields: vec![AlgebraicValue::C(int32(9))],
        },
    };

    assert!(std::sync::Arc::ptr_eq(
        &variable.algebraic_type.variants,
        &constructor.algebraic_type.variants,
    ));
}

#[test]
fn grounded_recursive_schema_accepts_symbolic_recursive_fields() {
    let algebraic_type = recursive_list_type();
    let tail = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(8)),
    };
    let cons = AlgebraicTerm {
        algebraic_type,
        node: AlgebraicTermNode::Constructor {
            variant: "Cons".to_string(),
            fields: vec![AlgebraicValue::C(int32(7)), AlgebraicValue::Algebraic(tail)],
        },
    };

    assert!(cons.is_well_formed());
}

#[test]
fn ungrounded_recursive_schema_rejects_an_arbitrary_variable() {
    let term = AlgebraicTerm {
        algebraic_type: ungrounded_recursive_type(),
        node: AlgebraicTermNode::Variable(Variable(9)),
    };

    assert!(!term.is_well_formed());
}

#[test]
fn match_on_symbolic_algebraic_value_remains_one_expression_path() {
    let algebraic_type = maybe_type();
    let expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
    });
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a pure match is a symbolic expression, not a path split");

    assert_eq!(paths.len(), 1);
    assert!(paths[0].facts.is_empty());
    assert!(paths[0].obligations.is_empty());
    let CValue::Int32(Bitvector32Term::AlgebraicMatch { scrutinee, arms }) = &paths[0].value else {
        panic!("unknown match should lower to an algebraic-match term");
    };
    assert_eq!(
        scrutinee.as_ref(),
        &AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(41)),
        }
    );
    assert_eq!(arms.len(), 2);
    assert_eq!(arms[0].variant, "None");
    assert_eq!(arms[1].variant, "Some");
}

#[test]
fn nested_match_binder_remains_symbolic_inside_its_arm() {
    let maybe_type = maybe_type();
    let maybe_value_type = maybe_type.value_type();
    let envelope_type = envelope_type(&maybe_type);
    let expression = SpecExpression::AlgebraicMatch {
        scrutinee: Box::new(SpecAlgebraicExpression {
            algebraic_type: envelope_type.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(80)),
        }),
        arms: vec![
            SpecAlgebraicMatchArm {
                variant: "Missing".to_string(),
                bindings: Vec::new(),
                binding_types: Vec::new(),
                body: SpecExpression::Value(int32(9)),
            },
            SpecAlgebraicMatchArm {
                variant: "Present".to_string(),
                bindings: vec!["maybe".to_string()],
                binding_types: vec![maybe_value_type],
                body: value_or_match(SpecAlgebraicExpression {
                    algebraic_type: maybe_type,
                    node: SpecAlgebraicExpressionNode::Binding("maybe".to_string()),
                }),
            },
        ],
    };

    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a nested algebraic binder should remain available to the arm body");

    assert_eq!(paths.len(), 1);
    let CValue::Int32(Bitvector32Term::AlgebraicMatch { arms, .. }) = &paths[0].value else {
        panic!("the outer match should remain symbolic");
    };
    let Bitvector32Term::AlgebraicMatch { .. } = &arms[1].body else {
        panic!("the nested binder should lower to the inner symbolic match");
    };
}

#[test]
fn algebraic_result_match_on_symbolic_value_remains_one_term() {
    let algebraic_type = maybe_type();
    let expression = SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Match {
            scrutinee: Box::new(SpecAlgebraicExpression {
                algebraic_type: algebraic_type.clone(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(52)),
            }),
            arms: vec![
                SpecAlgebraicResultMatchArm {
                    variant: "None".to_string(),
                    bindings: Vec::new(),
                    binding_types: Vec::new(),
                    binding_variables: vec![],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: algebraic_type.clone(),
                        node: SpecAlgebraicExpressionNode::Constructor {
                            variant: "None".to_string(),
                            fields: Vec::new(),
                        },
                    }),
                },
                SpecAlgebraicResultMatchArm {
                    variant: "Some".to_string(),
                    bindings: vec!["value".to_string()],
                    binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                    binding_variables: vec![None],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: algebraic_type.clone(),
                        node: SpecAlgebraicExpressionNode::Constructor {
                            variant: "Some".to_string(),
                            fields: vec![SpecAlgebraicValue::C(SpecExpression::CExpression(
                                CExpression::Variable("value".to_string()),
                            ))],
                        },
                    }),
                },
            ],
        },
    };
    let paths = evaluate_spec_algebraic_at_state_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("an algebraic-valued match should stay symbolic");

    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].value.node,
        AlgebraicTermNode::Match { .. }
    ));
    assert!(paths[0].value.is_well_formed());
}

#[test]
fn match_on_known_constructor_reduces_to_selected_arm() {
    let algebraic_type = maybe_type();
    let expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Some".to_string(),
            fields: vec![SpecAlgebraicValue::C(SpecExpression::Value(int32(7)))],
        },
    });
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a match on a checked constructor should reduce");

    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].value, int32(7));
}

#[test]
fn pure_pointer_result_preserves_type_and_unsupported_results_are_explicit() {
    for result_type in [CType::Int32Pointer, CType::VoidPointer, CType::Void] {
        let expression = SpecExpression::PureFunctionApplication {
            name: "select".into(),
            arguments: vec![],
            result_type,
            result_object_class: Some(crate::kernel::effective_type::CAccessClass::Struct(
                crate::kernel::effective_type::CStructClass::opaque("node"),
            )),
        };
        let result = evaluate_spec_expression_paths_with_loop_entry_in(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        );
        if result_type == CType::Void {
            assert!(matches!(
                result,
                Err(ExecutionLimit::UnsupportedPureFunctionResult(CType::Void))
            ));
        } else {
            let paths = result.expect("a pointer-valued pure call has one opaque result");
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].value.c_type(), result_type);
            // The declared return type's class reaches the pointer result.
            let crate::kernel::CValue::Pointer(pointer) = &paths[0].value else {
                panic!("a pointer result");
            };
            assert_eq!(
                pointer.object_class().map(|class| class.spelling()),
                Some("struct node".to_string())
            );
            let CValue::Pointer(pointer) = &paths[0].value else {
                panic!("lost pointer sort")
            };
            assert!(matches!(
                pointer.block,
                PointerBlock::PureFunctionApplication(_)
            ));
            assert!(paths[0].facts.is_empty());
            assert!(paths[0].obligations.is_empty());
        }
    }
}

#[test]
fn pure_function_application_is_not_eagerly_evaluated() {
    let expression = SpecExpression::PureFunctionApplication {
        name: "increment".to_string(),
        arguments: vec![SpecPureFunctionArgument::Value(SpecExpression::Value(
            int32(41),
        ))],
        result_type: CType::Int32,
        result_object_class: None,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("pure calls should lower to logical applications");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        paths[0].value,
        CValue::Int32(Bitvector32Term::ClickFunctionApplication {
            name: "increment".to_string(),
            arguments: vec![PureFunctionArgument::Value(int32(41))],
        })
    );
}

#[test]
fn pure_function_application_retains_symbolic_algebraic_argument() {
    let algebraic_type = maybe_type();
    let expression = SpecExpression::PureFunctionApplication {
        name: "tag".to_string(),
        arguments: vec![SpecPureFunctionArgument::Algebraic(
            SpecAlgebraicExpression {
                algebraic_type: algebraic_type.clone(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(61)),
            },
        )],
        result_type: CType::Int32,
        result_object_class: None,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &CState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("an ADT argument should remain one typed term");

    assert_eq!(paths.len(), 1);
    let CValue::Int32(Bitvector32Term::ClickFunctionApplication { arguments, .. }) =
        &paths[0].value
    else {
        panic!("pure call should remain an application");
    };
    assert_eq!(
        arguments,
        &[PureFunctionArgument::Algebraic(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(61)),
        })]
    );
}

#[test]
fn malformed_symbolic_match_is_rejected_before_term_construction() {
    let algebraic_type = maybe_type();
    let mut expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type,
        node: SpecAlgebraicExpressionNode::Variable(Variable(70)),
    });
    let SpecExpression::AlgebraicMatch { arms, .. } = &mut expression else {
        unreachable!()
    };
    arms.pop();

    assert!(
        evaluate_spec_expression_paths_with_loop_entry_in(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .is_err()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/algebraic_term_tests.rs");
}
