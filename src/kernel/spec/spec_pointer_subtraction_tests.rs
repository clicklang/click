use super::*;

#[test]
fn specification_subtraction_widens_coordinates_and_retains_pointer_provenance() {
    let external = |variable| Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::scaled_int32_node(
            OldMachineTerm::Variable(Variable(variable)),
            4,
        ),
    };
    let left = external(32_000);
    let right = external(32_001);
    let state = ExecutionState::new()
        .with_local("left", ProgramValue::pointer(left.clone()))
        .with_local("right", ProgramValue::pointer(right.clone()));
    let expression = SpecExpression::Subtract(
        Box::new(SpecExpression::ProgramExpression(
            crate::kernel::program_expression::variable("right"),
        )),
        Box::new(SpecExpression::ProgramExpression(
            crate::kernel::program_expression::variable("left"),
        )),
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
        paths[0].value.clone().into_native(),
        ProgramValue::Int64(OldMachineTerm::int64_subtract(
            OldMachineTerm::int64_from_32(OldMachineTerm::Variable(Variable(32_001))),
            OldMachineTerm::int64_from_32(OldMachineTerm::Variable(Variable(32_000))),
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
    // The precondition is one `same_allocation(right, left)` fact, which
    // raises as written (`design/pointer-model.md`).
    assert!(paths[0].facts.iter().any(|fact| {
        crate::kernel::assumptions::same_allocation_pointers(fact.proposition())
            .is_some_and(|(r, l)| r.address() == &right && l.address() == &left)
    }));
}
