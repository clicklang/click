use super::*;

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Pointer {
    Pointer {
        block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn argument(pointer: Pointer) -> PureFunctionArgument {
    PureFunctionArgument::Value(CValue::typed_pointer(pointer, CType::Int32Pointer))
}

#[test]
fn pure_pointer_calls_preserve_identity_and_do_not_imply_separation() {
    let p = Pointer::symbolic(Variable(410));
    let q = Pointer::symbolic(Variable(411));
    let a = call("select", vec![argument(p.clone())]);
    let b = call("select", vec![argument(q)]);
    assert_eq!(a, call("select", vec![argument(p)]));
    assert_ne!(a, b);
    assert!(!a.blocks_proven_distinct(&b));
    let heap = Pointer {
        block: PointerBlock::Heap(55),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(!a.blocks_proven_distinct(&heap));
    assert!(!heap.blocks_proven_distinct(&a));
    assert_ne!(a, call("different", vec![]));
}

#[test]
fn pure_pointer_rewrite_preserves_offsets_and_distinct_arguments() {
    let p = Pointer::symbolic(Variable(410));
    let q = Pointer::symbolic(Variable(411));
    let mut input = call("select", vec![argument(p.clone()), argument(q.clone())]);
    input.offset = PointerOffsetTerm::Constant(8);
    let replacement = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let mut expected = call("select", vec![argument(replacement.clone()), argument(q)]);
    expected.offset = input.offset.clone();
    let mut rewrite = TermRewrite::for_pointer_variable(Variable(410), &replacement);
    assert_eq!(rewrite.pointer(&input), expected);
    assert_eq!(rewrite.refusal(), None);
}

#[test]
fn pure_pointer_dag_substitution_and_capture_collection_scale_linearly() {
    let source = Variable(410);
    let replacement = Pointer::symbolic(Variable(411));
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut input = Pointer::symbolic(source);
        let mut expected = replacement.clone();
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_pointer_variable(source, &replacement);
            let result = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            result
        });
        assert!(result == expected);
        let (_, capture_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = CarrierVariables::for_rewrite(false);
            collect_pointer_carriers(&input, &mut variables);
            assert_eq!(variables.c, BTreeSet::from([source]));
            let mut captured = BTreeSet::new();
            crate::kernel::prelude::collect_proposition_capture_variables(
                &Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(Box::new(input.clone()), Box::new(input.clone())),
                    true,
                ),
                &mut captured,
            );
            assert!(captured.contains(&source));
        });
        measurements.push(work + capture_work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}

#[test]
fn pure_pointer_arguments_respect_match_binders_and_avoid_capture() {
    let bound = Variable(500);
    let free = Variable(501);
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
    }]
    .into();
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "PointerScope".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "PointerScope".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let input = Bitvector32Term::AlgebraicMatch {
        scrutinee: Box::new(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(502)),
        }),
        arms: vec![AlgebraicBitvectorMatchArm {
            variant: "Node".into(),
            bindings: vec![AlgebraicValue::C(CValue::typed_pointer(
                Pointer::symbolic(bound),
                CType::Int32Pointer,
            ))],
            body: Bitvector32Term::ClickFunctionApplication {
                name: "observe".into(),
                arguments: vec![argument(call(
                    "select",
                    vec![
                        argument(Pointer::symbolic(bound)),
                        argument(Pointer::symbolic(free)),
                    ],
                ))],
            },
        }],
    };
    let replacement = call("replacement", vec![argument(Pointer::symbolic(bound))]);
    let mut rewrite = TermRewrite::for_pointer_variable(free, &replacement);
    let Bitvector32Term::AlgebraicMatch { arms, .. } = rewrite.bits(&input) else {
        panic!("lost match")
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::C(CValue::Pointer(renamed)) = &arms[0].bindings[0] else {
        panic!("lost binder")
    };
    assert_ne!(renamed.pointer(), &Pointer::symbolic(bound));
    let expected = Bitvector32Term::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(call(
            "select",
            vec![
                argument(renamed.pointer().clone()),
                argument(replacement.clone()),
            ],
        ))],
    };
    assert_eq!(arms[0].body, expected);
    let unrelated = Pointer::symbolic(Variable(503));
    let mut shadowed = TermRewrite::for_pointer_variable(bound, &unrelated);
    assert_eq!(shadowed.bits(&input), input);
    assert_eq!(shadowed.refusal(), None);

    let source = Pointer::symbolic(free);
    let mut exact = TermRewrite::for_pointer_exact(&source, &replacement);
    let _ = exact.bits(&input);
    assert_eq!(exact.refusal(), Some(RewriteRefusal::UnsupportedScope));
}

#[test]
fn pure_pointer_capture_cache_does_not_hide_a_free_occurrence_after_a_fold() {
    let item = Variable(610);
    let application = call(
        "select",
        vec![PureFunctionArgument::Value(CValue::Int32(
            Bitvector32Term::Variable(item),
        ))],
    );
    let observed = Bitvector32Term::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(application)],
    };
    let fold = Bitvector32Term::RangeFold {
        start: Box::new(Bitvector32Term::Constant(0)),
        end: Box::new(Bitvector32Term::Constant(4)),
        initial: Box::new(Bitvector32Term::Constant(0)),
        accumulator: Variable(611),
        item,
        body: Box::new(observed.clone()),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(fold), Box::new(observed)),
        true,
    );
    let mut variables = BTreeSet::new();
    crate::kernel::prelude::collect_proposition_capture_variables(&proposition, &mut variables);
    assert!(
        variables.contains(&item),
        "the right occurrence is outside the fold's binder"
    );
}

#[test]
fn pure_pointer_legacy_scalar_substitution_visits_the_shared_dag_once() {
    let variable = Variable(710);
    let replacement = Bitvector32Term::Constant(9);
    let mut measurements = Vec::new();
    for depth in [8, 16, 32] {
        let mut input = call(
            "scalar",
            vec![PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(variable),
            ))],
        );
        let mut expected = call(
            "scalar",
            vec![PureFunctionArgument::Value(CValue::Int32(
                replacement.clone(),
            ))],
        );
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::prelude::substitute_bitvector_variable_in_pointer(
                &input,
                variable,
                &replacement,
            )
        });
        assert!(result == expected);
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}
