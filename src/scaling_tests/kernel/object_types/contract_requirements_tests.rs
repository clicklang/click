use super::*;

#[test]
fn nested_typed_uses_share_pointer_origin_analysis() {
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut expression = variable("p");
        for _ in 0..count {
            expression = SpecExpression::PureFunctionApplication {
                name: "pointer_identity".to_string(),
                result_type: CType::Int32Pointer,
                result_object_class: None,
                pointer_result: Some(Arc::new(PurePointerResult {
                    classes: Default::default(),
                    arguments: BTreeSet::from([0]),
                })),
                arguments: vec![SpecPureFunctionArgument::ObjectPointer {
                    argument: Box::new(SpecPureFunctionArgument::Value(expression)),
                    object_class: class(),
                }],
            };
        }
        let interface = interface(SpecProposition::Defined(typed(expression)));
        let (required, work) = crate::instrumentation::measure_deterministic_work(|| {
            declared_requirements(&interface)
        });
        assert_eq!(required, ObjectTypeRequirements::unit(0, class()));
        assert!(work > 0);
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) * 2,
            "{samples:?}"
        );
    }
}

#[test]
fn conditional_origins_form_a_shared_graph_instead_of_expanded_prefix_sets() {
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut expression = variable("p0");
        for index in 1..count {
            expression = SpecExpression::If {
                condition: Box::new(SpecProposition::Comparison {
                    left: SpecExpression::Value(CValue::Int32(Bitvector32Term::constant(0))),
                    operator: CComparisonOperator::Equal,
                    right: SpecExpression::Value(CValue::Int32(Bitvector32Term::constant(0))),
                }),
                then_branch: Box::new(expression),
                else_branch: Box::new(variable(&format!("p{index}"))),
            };
        }
        let mut interface = CFunctionContractInterface::new(
            CType::Void,
            (0..count)
                .map(|i| CParameter::new(format!("p{i}"), CType::Int32Pointer))
                .collect(),
        );
        interface.contract_ensures = vec![SpecProposition::Defined(typed(expression))];
        let (required, work) = crate::instrumentation::measure_deterministic_work(|| {
            declared_requirements(&interface)
        });
        assert_eq!(required.len(), count);
        assert!(work > 0);
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) * 2,
            "{samples:?}"
        );
    }
}


#[test]
fn return_guarantee_analysis_visits_only_the_selected_declaration() {
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut interface = returning(return_check());
        interface.contract_ensures.extend((0..count).map(|_| SpecProposition::Defined(typed(variable("other")))));
        let (class_found, work) = crate::instrumentation::measure_deterministic_work(|| declared_return_class(&interface));
        assert_eq!(class_found, Some(class()));
        assert!(work >= count);
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) * 2, "{samples:?}");
    }
}
