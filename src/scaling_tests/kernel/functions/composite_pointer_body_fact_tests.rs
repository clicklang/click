// Scaling tests of `src/kernel/functions.rs` (module `composite_pointer_body_fact_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A fold's packed-word equation can use a new name for a checked copy.
// Rewriting that name must remain scoped, full-width, and independent
// of unrelated facts. No memory observation or ownership is invented.
#[test]
fn fold_copied_wide_word_preserves_scope_width_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let word = Bitvector32Term::Variable(Variable(710_000));
    let copied = Bitvector32Term::Variable(Variable(710_001));
    let changed = Bitvector32Term::Variable(Variable(710_002));
    let address = Bitvector32Term::PointerAddress(
        Box::new(Pointer::symbolic(Variable(710_003))),
        crate::kernel::AddressObjectClass::NONE,
    );
    let packed = |word: &Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(word.clone()),
                Box::new(Bitvector32Term::UInt64Add(
                    Box::new(address.clone()),
                    Box::new(Bitvector32Term::UInt64BitwiseAnd(
                        Box::new(word.clone()),
                        Box::new(Bitvector32Term::UInt64Constant(1)),
                    )),
                )),
            ),
            true,
        )
    };
    let alias = Proposition::ConditionIs(
        ConditionTerm::Bitvector64Equal(Box::new(copied.clone()), Box::new(word.clone())),
        true,
    );
    // Force the selected-alias route rather than general condition reasoning.
    let parent = PureFactContext::new()
        .defer_non_exact_condition_reasoning()
        .assume_proposition(packed(&word));
    let context = parent.clone().assume_proposition(alias.clone());
    assert!(resource_body_fact_is_established(
        &context,
        &packed(&copied)
    ));
    assert!(!resource_body_fact_is_established(
        &parent,
        &packed(&copied)
    ));
    assert!(!resource_body_fact_is_established(
        &context,
        &packed(&changed)
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(alias),
        &packed(&copied),
    ));
    let mut previous = None;
    for count in [16_u64, 64, 256, 1024] {
        let mut padded = context.clone();
        for index in 0..count {
            padded = padded.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(
                    Box::new(Bitvector32Term::Variable(Variable(720_000 + index))),
                    Box::new(Bitvector32Term::UInt64Constant(index)),
                ),
                true,
            ));
        }
        padded.build_stated_proposition_index();
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            resource_body_fact_is_established(&padded, &packed(&copied))
        });
        assert!(proved);
        if let Some(previous) = previous {
            assert!(work <= previous + 64, "{count}: {work} after {previous}");
        }
        previous = Some(work);
    }
}

/// A 32-bit equality between two 64-bit words is not the 64-bit alias the
/// fold needs. Debug builds refuse the mixed-width context outright; a
/// release build must still not establish the fact through it.
#[test]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "a variable used at another width")
)]
fn a_narrow_equality_between_wide_words_is_not_an_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    let word = Bitvector32Term::Variable(Variable(730_000));
    let copied = Bitvector32Term::Variable(Variable(730_001));
    let address = Bitvector32Term::PointerAddress(
        Box::new(Pointer::symbolic(Variable(730_003))),
        crate::kernel::AddressObjectClass::NONE,
    );
    let packed = |word: &Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(word.clone()),
                Box::new(Bitvector32Term::UInt64Add(
                    Box::new(address.clone()),
                    Box::new(Bitvector32Term::UInt64BitwiseAnd(
                        Box::new(word.clone()),
                        Box::new(Bitvector32Term::UInt64Constant(1)),
                    )),
                )),
            ),
            true,
        )
    };
    let narrow = PureFactContext::new()
        .defer_non_exact_condition_reasoning()
        .assume_proposition(packed(&word))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(copied.clone()), Box::new(word.clone())),
            true,
        ));
    assert!(!resource_body_fact_is_established(
        &narrow,
        &packed(&copied)
    ));
}

#[test]
fn fold_nonnull_fact_uses_an_exact_composite_pointer_alias() {
    let model = Pointer::symbolic(Variable(700));
    let program = Pointer {
        block: PointerBlock::Symbolic(Variable(701)),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(702))),
            byte_width: 4,
        },
    };
    let null = Pointer::null();
    let alias = pointer_fact(&model, &program, true);
    let nonnull = pointer_fact(&model, &null, false);
    let needed = pointer_fact(&program, &null, false);
    let context = PureFactContext::new()
        .assume_proposition(alias.clone())
        .assume_proposition(nonnull.clone());
    assert!(resource_body_fact_is_established(&context, &needed));
    assert!(!resource_body_fact_is_established(
        &context,
        &pointer_fact(&program, &null, true),
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(alias.clone()),
        &needed,
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(nonnull.clone()),
        &needed,
    ));
    let parent_fact = |pointer: &Pointer, value: u32| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::ClickFunctionApplication {
                    name: "parent_is".into(),
                    arguments: vec![PureFunctionArgument::Value(CValue::typed_pointer(
                        pointer.clone(),
                        CType::Int32Pointer,
                    ))],
                }),
                Box::new(Bitvector32Term::Constant(value)),
            ),
            true,
        )
    };
    let model_parent = parent_fact(&model, 1);
    let needed_parent = parent_fact(&program, 1);
    let context = context.assume_proposition(model_parent.clone());
    assert!(!resource_body_fact_is_established(&context, &needed_parent));
    // A pure pointer argument observes the complete value; a numeric address
    // alias suffices for nonnull above, but cannot rewrite this argument.
    let context = context.assume_condition(
        ConditionTerm::pointer_value_equal(
            CPointerValue::new(model.clone(), CType::Int32Pointer),
            CPointerValue::new(program.clone(), CType::Int32Pointer),
        ),
        true,
    );
    assert!(resource_body_fact_is_established(&context, &needed_parent));
    assert!(!resource_body_fact_is_established(
        &context,
        &parent_fact(&program, 0)
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(model_parent),
        &needed_parent,
    ));
    let mut work = Vec::new();
    for count in [16, 64, 256] {
        let mut padded = context.clone();
        for index in 0..count {
            padded = padded.assume_proposition(pointer_fact(
                &Pointer::symbolic(Variable(10_000 + index)),
                &Pointer::symbolic(Variable(20_000 + index)),
                true,
            ));
            padded = padded.assume_proposition(pointer_fact(
                &Pointer::symbolic(Variable(30_000 + index)),
                &null,
                true,
            ));
        }
        // Charge the deferred insertion of these new facts to building
        // the context, then measure only the fold's indexed query.
        padded.build_stated_proposition_index();
        let (proved, units) = crate::instrumentation::measure_deterministic_work(|| {
            let proved = resource_body_fact_is_established(&padded, &needed);
            assert!(resource_body_fact_is_established(&padded, &needed_parent));
            assert!(!resource_body_fact_is_established(
                &padded,
                &parent_fact(&program, 0)
            ));
            assert!(!resource_body_fact_is_established(
                &padded,
                &pointer_fact(&program, &null, true),
            ));
            proved
        });
        assert!(proved);
        work.push(units);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 8,
            "unrelated aliases increased fold work: {work:?}"
        );
    }
}

#[test]
fn binding_free_scalar_facts_do_not_prepare_unused_arm_memory() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(718_000));
        let state =
            CState::new().with_local("p", CValue::typed_pointer(pointer, CType::Int32Pointer));
        let arm = CResourceMatchArm {
            variant: "Held".into(),
            bindings: vec![],
            binding_types: vec![],
            binding_variables: vec![],
            children: vec![],
            contains: (0..size)
                .map(|index| {
                    CResourceSpec::owned_memory(CMemorySegment::new(
                        CExpression::Value(CValue::typed_pointer(
                            Pointer::symbolic(Variable(719_000 + index)),
                            CType::Int32Pointer,
                        )),
                        c_int32_literal(0),
                        c_int32_literal(1),
                    ))
                })
                .collect(),
            facts: vec![SpecProposition::Comparison {
                left: SpecExpression::CExpression(c_variable("p")),
                operator: CComparisonOperator::NotEqual,
                right: SpecExpression::CExpression(c_int32_literal(0)),
            }],
        };
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            arm_binding_free_facts(&state, &arm, &PureFactContext::new()).collect::<Vec<_>>()
        });
        assert_eq!(facts.len(), 1);
        assert!(matches!(&facts[0], Proposition::ConditionIs(_, false)));
        assert!(work <= 128, "{size} unused clauses: {work}");
    }
}

#[test]
fn arm_refutation_stops_before_unneeded_memory_facts() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = CState::new().with_local(
            "p",
            CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
        );
        let arm = CResourceMatchArm {
            variant: "Held".into(),
            bindings: vec![],
            binding_types: vec![],
            binding_variables: vec![],
            children: vec![],
            contains: (0..size)
                .map(|index| {
                    CResourceSpec::owned_memory(CMemorySegment::new(
                        CExpression::Value(CValue::typed_pointer(
                            Pointer::symbolic(Variable(719_000 + index)),
                            CType::Int32Pointer,
                        )),
                        c_int32_literal(0),
                        c_int32_literal(1),
                    ))
                })
                .collect(),
            facts: vec![
                SpecProposition::Comparison {
                    left: SpecExpression::CExpression(c_variable("p")),
                    operator: CComparisonOperator::NotEqual,
                    right: SpecExpression::CExpression(c_int32_literal(0)),
                },
                SpecProposition::Comparison {
                    left: SpecExpression::CExpression(CExpression::Load(Box::new(c_variable("p")))),
                    operator: CComparisonOperator::Equal,
                    right: SpecExpression::CExpression(c_int32_literal(0)),
                },
            ],
        };
        let (refuted, work) = crate::instrumentation::measure_deterministic_work(|| {
            arm_is_refuted_by_a_binding_free_fact(
                &state,
                &arm,
                &PureFactContext::new(),
                &PureFactContext::new(),
            )
        });
        assert!(refuted);
        assert!(work <= 128, "{size} unused clauses: {work}");
    }
}

#[test]
fn numeric_resource_facts_do_not_repeat_the_canonical_read_walk() {
    let mut costs = Vec::new();
    for size in [2u64, 4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let input = |name| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(name)), 4),
        };
        let word = input(719_100);
        let context = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .keep_spec_loads_symbolic()
            .prefer_symbolic_external_loads();
        let definition = CCompositeResourceDefinition::new(
            "unrelated_word",
            vec![c_parameter("slot", CType::UInt64Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment {
                base: c_variable("slot"),
                start: c_int32_literal(0),
                end: c_int32_literal(1),
                element_width: 8,
                guard: None,
            })],
            vec![],
        );
        let residual = ResourceContext::new().unchecked_with_facts((0..size).map(|i| {
            CResourceFact::own(CResource::Composite {
                name: "unrelated_word".into(),
                arguments: vec![
                    CValue::typed_pointer(input(720_000 + i), CType::UInt64Pointer).into(),
                ]
                .into(),
            })
        }));
        let kept = crate::kernel::primitives::CallKeptOwnership::new(
            residual,
            crate::kernel::primitives::CallKeptRanges::new(
                ResourceContext::new(),
                vec![],
                Some(std::sync::Arc::new(vec![definition])),
            ),
            &context,
        );
        let memory = CMemory::new().with_call_memory_havoc(
            Variable(719_101),
            &[CMemoryRange::new_with_element_width(
                input(719_102),
                0u32.into(),
                1u32.into(),
                8,
            )],
            &context,
            Some(&kept),
        );
        // Each query uses another unconstrained address in the same block,
        // so the canonical walk cannot be warmed by the preceding measurement.
        let (_, canonical_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::canonicalize_atomic_loads(
                &Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(&memory),
                    Box::new(input(719_104)),
                    LoadKind::Bits64,
                ),
            )
        });
        let state = CState::new()
            .with_memory(memory)
            .with_local("p", CValue::typed_pointer(word, CType::UInt64Pointer));
        let arm = CResourceMatchArm {
            variant: "Held".into(),
            bindings: vec![],
            binding_types: vec![],
            binding_variables: vec![],
            children: vec![],
            contains: vec![CResourceSpec::owned_memory(CMemorySegment {
                base: c_variable("p"),
                start: c_int32_literal(0),
                end: c_int32_literal(1),
                element_width: 8,
                guard: None,
            })],
            facts: vec![SpecProposition::Comparison {
                left: SpecExpression::CExpression(CExpression::Load(Box::new(c_variable("p")))),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::CExpression(CExpression::Value(CValue::UInt64(
                    Bitvector32Term::UInt64Constant(0),
                ))),
            }],
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            arm_premises_at_symbolic_bindings(&state, &arm, &[], &context, &context)
        });
        assert!(result.is_some());
        let publishing_state = state.clone().with_local(
            "p",
            CValue::typed_pointer(input(719_103), CType::UInt64Pointer),
        );
        let (published, publication_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                lower_selected_resource_body_clauses(
                    &publishing_state,
                    &arm.facts,
                    Some("Held"),
                    &BTreeMap::new(),
                    &BTreeMap::new(),
                    &context,
                    None,
                    &mut ExecutionBudget::default(),
                )
            });
        assert!(published.is_ok(), "{published:?}");
        costs.push([canonical_work, work, publication_work]);
    }
    assert!(
        costs.iter().all(|[canonical, hypothetical, published]| {
            *hypothetical <= canonical + 256 && *published <= canonical + 256
        }),
        "[canonical, hypothetical, published]: {costs:?}"
    );
}

// A failed predicate comparison must not search unrelated memory equations.
#[test]
fn predicate_constructor_comparison_ignores_unrelated_load_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Empty".into(),
        fields: vec![],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "ComparisonModel".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "ComparisonModel".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let variable = Variable(740_000);
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(variable),
    };
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Empty".into(),
            fields: vec![],
        },
    };
    crate::kernel::register_pure_function_definition(crate::kernel::CPureFunctionDefinition::new(
        "comparison_value",
        vec![
            crate::kernel::CPureFunctionParameter::algebraic("model", ty),
            crate::kernel::CPureFunctionParameter::c("value", CType::Int32),
        ],
        SpecExpression::CExpression(CExpression::Variable("value".into())),
    ))
    .unwrap();
    let value = Bitvector32Term::Variable(Variable(740_001));
    let premise = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::ClickFunctionApplication {
                name: "comparison_value".into(),
                arguments: vec![
                    PureFunctionArgument::Algebraic(model),
                    PureFunctionArgument::Value(CValue::Int32(value.clone())),
                ],
            },
            Bitvector32Term::Constant(1),
        ),
        true,
    );
    let mut costs = Vec::new();
    for count in [4u64, 8, 16, 32] {
        let mut assumptions = PureFactContext::new();
        for index in 0..count {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        intern_c_memory_ref(&CMemory::new()),
                        Box::new(Pointer::symbolic(Variable(741_000 + index))),
                        LoadKind::Bits32,
                    ),
                    Bitvector32Term::Constant(index as u32 + 2),
                ),
                true,
            ));
        }
        assumptions.build_stated_proposition_index();
        let (refuted, work) = crate::instrumentation::measure_deterministic_work(|| {
            predicate_fact_refutes_constructor(
                &premise,
                &variable,
                &constructor,
                &assumptions,
                &mut ExecutionBudget::beside_live_state(),
            )
        });
        assert!(!refuted, "unrelated loads cannot settle the predicate");
        costs.push(work);
        let known = assumptions
            .clone()
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(0)),
                true,
            ));
        assert!(predicate_fact_refutes_constructor(
            &premise,
            &variable,
            &constructor,
            &known,
            &mut ExecutionBudget::beside_live_state()
        ));
        let possible = assumptions.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
            true,
        ));
        assert!(!predicate_fact_refutes_constructor(
            &premise,
            &variable,
            &constructor,
            &possible,
            &mut ExecutionBudget::beside_live_state()
        ));
    }
    assert!(
        costs.iter().all(|work| *work <= costs[0] + 16),
        "predicate comparison searched unrelated load equations: {costs:?}"
    );
}
