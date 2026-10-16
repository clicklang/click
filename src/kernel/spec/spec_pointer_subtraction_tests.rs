use super::*;

#[test]
fn specification_subtraction_retains_pointer_provenance_and_overflow_guards() {
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let left = external(32_000);
    let right = external(32_001);
    let state = CState::new()
        .with_local("left", CValue::pointer(left.clone()))
        .with_local("right", CValue::pointer(right.clone()));
    let expression = SpecExpression::Subtract(
        Box::new(SpecExpression::CExpression(c_variable("right"))),
        Box::new(SpecExpression::CExpression(c_variable("left"))),
    );

    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &state,
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("pointer subtraction should stay within its specification budget");
    assert_eq!(paths.len(), 1);
    assert_eq!(
        paths[0].value,
        int32(Bitvector32Term::subtract(
            Bitvector32Term::Variable(Variable(32_001)),
            Bitvector32Term::Variable(Variable(32_000)),
        ))
    );
    assert!(paths[0].facts.contains(&ExecutionPureFact::condition(
        pointer_object_is_null_condition(&right),
        false,
    )));
    assert!(paths[0].facts.contains(&ExecutionPureFact::condition(
        pointer_object_is_null_condition(&left),
        false,
    )));
    assert!(paths[0].facts.contains(&ExecutionPureFact::condition(
        pointer_object_identity_condition(&right, &left),
        true,
    )));
    assert!(paths[0].facts.contains(&ExecutionPureFact::condition(
        ConditionTerm::signed_subtract_overflows(
            Bitvector32Term::Variable(Variable(32_001)),
            Bitvector32Term::Variable(Variable(32_000)),
        ),
        false,
    )));
}
