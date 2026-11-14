use super::*;
use crate::kernel::*;

fn resource_index_type(name: &str, fields: Vec<AlgebraicValueType>) -> AlgebraicType {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Clear".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Set".into(),
            fields,
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: name.into(),
        arguments: vec![],
    };
    AlgebraicType {
        rigid: false,
        name: name.into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn resource_index_variable(ty: &AlgebraicType, id: u64) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(id)),
    }
}

fn check_resource_publication_work(
    fold: bool,
    prepare_requirements: bool,
    retain_requirements: bool,
) {
    let samples = [4_u64, 16, 64].map(|size| {
        let _session = VerificationSession::enter();
        let ty = resource_index_type("IntegerModel", vec![AlgebraicValueType::Integer]);
        let model = resource_index_variable(&ty, 991_001);
        let constructor = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Set".into(),
                fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
            },
        };
        let schema = ResourceFieldSchema::new(vec![(
            "model".into(),
            ResourceFieldType::Algebraic(ty.clone()),
        )])
        .unwrap();
        let instance = ResourceInstance::new(
            Variable(991_000),
            "integer_box".into(),
            vec![].into(),
            schema.clone(),
            vec![AlgebraicValue::Algebraic(model.clone())].into(),
        )
        .unwrap();
        let binding = Variable(9_100_000_000);
        let mut definition =
            CompositeResourceDefinition::new("integer_box", vec![], None, false, vec![], vec![])
                .with_instance_schema(Some(schema));
        definition.matched = Some(ResourceMatchBody {
            field_index: 0,
            algebraic_type: ty.clone(),
            arms: vec![
                ResourceMatchArm {
                    variant: "Clear".into(),
                    bindings: vec![],
                    binding_types: vec![],
                    binding_variables: vec![],
                    contains: vec![],
                    facts: vec![],
                    children: vec![],
                },
                ResourceMatchArm {
                    variant: "Set".into(),
                    bindings: vec!["value".into()],
                    binding_types: vec![AlgebraicValueType::Integer],
                    binding_variables: vec![Some(binding)],
                    contains: vec![],
                    facts: vec![SpecProposition::IntegerComparison {
                        left: SpecIntegerExpression::Term(IntegerTerm::var(binding)),
                        operator: IntegerComparisonOperator::GreaterEqual,
                        right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                    }],
                    children: vec![],
                },
            ],
        });
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
            Term::Algebraic(model),
            Term::Algebraic(constructor),
        ));

        let (opened, clauses) =
            rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).unwrap();
        let body = clauses
            .into_iter()
            .find(|fact| matches!(fact, Proposition::ConditionIs(..)))
            .expect("pure body clause");
        let mut assumptions = assumptions.assume_proposition(body.clone());
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(8_000_000 + index * 2)),
                    Pointer::symbolic(Variable(8_000_001 + index * 2)),
                ),
                true,
            );
        }
        // Fold's existing prerequisite check also uses stated identity.
        // Prepare that separate query when isolating publication cost.
        if prepare_requirements {
            assumptions.build_stated_proposition_index();
        }
        if retain_requirements {
            assumptions = assumptions.retaining_required_obligations();
        }
        let mut interface = FunctionContractInterface::new(ProgramType::Void, vec![]);
        interface.composite_resource_definitions = vec![definition.clone()];
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            if fold {
                let rewrite = rewrite_resource_instance_selecting_children(
                    &opened,
                    &instance,
                    &definition,
                    std::slice::from_ref(&definition),
                    &assumptions,
                    false,
                    None,
                )
                .unwrap();
                assert_eq!(rewrite.body_clauses.len(), 1);
                assert_eq!(rewrite.body_clauses[0].obligation().proposition(), &body);
                rewrite.semantic_facts
            } else {
                checked_returned_instance_body_facts(
                    state.resources(),
                    &interface,
                    &state,
                    &assumptions,
                )
            }
        });
        assert!(
            facts.contains(&body),
            "already-held body clause must still be published: {facts:?}"
        );
        let ((once, twice), admission) = crate::instrumentation::measure_deterministic_work(|| {
            let admit = |context| {
                facts
                    .iter()
                    .cloned()
                    .fold(context, PureFactContext::assume_proposition)
            };
            let once = admit(assumptions.clone());
            let twice = admit(once.clone());
            (once, twice)
        });
        assert_eq!(once.fact_counts(), twice.fact_counts());
        assert!(twice.contains_assumed_exact(&body));
        (work, admission)
    });
    eprintln!("fold={fold}, publication/admission={samples:?}");
    assert_eq!(samples[0], samples[1]);
    assert_eq!(samples[1], samples[2]);
}

#[test]
fn resource_publication_ignores_unrelated_stated_facts() {
    check_resource_publication_work(false, false, false);
    check_resource_publication_work(true, true, false);
}

#[test]
#[ignore = "red diagnostic: fold prerequisite checking forces the cold stated-fact index"]
fn legacy_checked_fold_requirements_ignore_unrelated_stated_facts() {
    check_resource_publication_work(true, false, false);
}

/// The driver prepares written folds with obligation retention enabled, then
/// proves the returned clauses at the input state. No warm-up of fact indexes
/// belongs in this measurement of the actual preparation mode.
#[test]
fn prepared_fold_emits_body_obligation_without_indexing_ambient_facts() {
    check_resource_publication_work(true, false, true);
}
