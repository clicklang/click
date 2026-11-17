use super::*;
use crate::kernel::program_expression::{int32_literal, variable};

pub(super) fn definition() -> CompositeResourceDefinition {
    CompositeResourceDefinition::new(
        "packet",
        vec![
            program_parameter("base", ProgramType::Int32Pointer),
            program_parameter("length", ProgramType::Int32),
        ],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("base"),
            int32_literal(0),
            variable("length"),
        ))],
        vec![],
    )
}

pub(super) fn contract() -> ProgramFunction {
    let template = super::summary_transfer_tests::symbolic_contract();
    let input = template.resource_requires()[0].clone();
    let output = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "packet".into(),
        vec![variable("p"), variable("n")],
        vec![ProgramType::Int32Pointer, ProgramType::Int32],
    )
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post);
    template
        .with_resource_summary(vec![input], vec![output])
        .with_composite_resource_definitions(vec![definition()])
}

pub(super) fn returned(
    function: &ProgramFunction,
    state: &ExecutionState,
    transfer: &FunctionResourceTransfer,
    composition: ReturnResourceComposition<'_>,
    facts: &PureFactContext,
) -> Result<ContractReturnResources, RuntimeError> {
    evaluate_contract_return_resources(
        &transfer.caller_resources_after_requirements,
        escrowed_owners(transfer),
        &transfer.canonical_borrowed_owners,
        &transfer.borrowed_inputs,
        &transfer_entry_clauses(transfer),
        state,
        state,
        function.name(),
        function.contract_interface(),
        &[],
        composition,
        facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
}

#[test]
fn symbolic_composite_child_retains_selected_custody_and_an_empty_new_boundary() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, owner) = super::summary_transfer_tests::symbolic_state();
    let function = contract();
    let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
    let selected = transfer.consumed_cell_returns.children[&vec![0, 0]];
    let composition = ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns);
    let evaluated =
        super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &evaluated,
        function.composite_resource_definitions(),
        &state,
        composition,
        &facts,
    )
    .unwrap();
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert!(body.boundary.is_empty());
    assert_eq!(
        body.transfers[0].origin,
        ReturnOwnershipOrigin::ConsumedCell(selected)
    );
    assert_eq!(body.transfers[0].fact, owner);
    for _ in 0..2 {
        let result = returned(&function, &state, &transfer, composition, &facts).unwrap();
        assert!(
            result
                .return_resources
                .contains_exact_representation(&evaluated.resources.facts()[0])
        );
    }
    assert!(state.resources().contains_exact_representation(&owner));
}

#[test]
fn raw_composite_descriptions_cannot_use_selected_child_custody() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, _) = super::summary_transfer_tests::symbolic_state();
    let function = contract();
    let mut transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
    transfer.caller_resources_after_requirements = state.resources().clone();
    assert!(matches!(
        returned(
            &function,
            &state,
            &transfer,
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        ),
        Err(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
    ));
}

#[test]
fn a_consumed_input_cannot_supply_two_composite_children_or_a_flat_sibling() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, _) = super::summary_transfer_tests::symbolic_state();
    let function = contract();
    let input = function.resource_requires()[0].clone();
    let output = function.resource_ensures()[0].clone();
    let duplicate = function
        .clone()
        .with_resource_summary(vec![input.clone()], vec![output.clone(), output.clone()]);
    let transfer = super::tests::prepare_mixed_scalar(&duplicate, &state, &facts);
    assert_eq!(transfer.consumed_cell_returns.children.len(), 1);
    assert!(
        transfer
            .consumed_cell_returns
            .children
            .contains_key(&vec![0, 0])
    );
    let flat = input
        .clone()
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
    let mixed = function.with_resource_summary(vec![input], vec![output, flat]);
    let transfer = super::tests::prepare_mixed_scalar(&mixed, &state, &facts);
    assert!(transfer.consumed_cell_returns.children.is_empty());
    assert!(transfer.consumed_cell_returns.get(1).is_some());
}

#[test]
fn replacing_composite_definitions_rebuilds_the_child_rule_in_either_builder_order() {
    let function = contract();
    let retained = function.contract_interface().resource_transfer_rule.clone();
    assert_eq!(retained.inputs_by_child, BTreeMap::from([(vec![0, 0], 0)]));
    let mut changed = definition();
    changed.contains = vec![ResourceSpec::owned_memory(MemorySegment::new(
        variable("base"),
        int32_literal(0),
        int32_literal(32),
    ))];
    let changed = function
        .clone()
        .with_composite_resource_definitions(vec![changed]);
    assert!(
        changed
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_child
            .is_empty()
    );
    let rebuilt = changed
        .with_composite_resource_definitions(vec![definition()])
        .with_resource_summary(
            function.resource_requires().to_vec(),
            function.resource_ensures().to_vec(),
        );
    assert_eq!(
        rebuilt
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_child,
        retained.inputs_by_child
    );
}

#[test]
fn converted_composite_arguments_do_not_authorize_unchanged_child_footprints() {
    let function = contract();
    let mut converted = definition();
    converted.parameters[1] = program_parameter("length", ProgramType::Int64);
    let function = function.with_composite_resource_definitions(vec![converted]);
    assert!(
        function
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_child
            .is_empty()
    );
}

#[test]
fn borrowed_parameter_bounded_bodies_keep_entry_footprint_provenance() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, owner) = super::summary_transfer_tests::symbolic_state();
    let head = ResourceFact::own_composite(
        "packet".into(),
        vec![
            ProgramValue::pointer(owner.memory_own_range().unwrap().base().clone()),
            ProgramValue::Int32(owner.memory_own_range().unwrap().end().clone()),
        ],
    );
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head, ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &evaluated,
        &[definition()],
        &state,
        ReturnResourceComposition::RestoreEntryBorrows,
        &facts,
    )
    .unwrap();
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert!(body.boundary.is_empty());
    assert_eq!(body.transfers[0].origin, ReturnOwnershipOrigin::EntryBorrow);
    let raw = ConstructedReturnBodies::construct(&evaluated, &[definition()], &state, &facts);
    assert_eq!(
        raw.get(evaluated.occurrences[0].source)
            .unwrap()
            .boundary
            .len(),
        1
    );
    let mut guarded = definition();
    guarded.condition = Some(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(int32_literal(1)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(int32_literal(1)),
    });
    let guarded = ConstructedReturnBodies::try_construct(
        &evaluated,
        &[guarded],
        &state,
        ReturnResourceComposition::RestoreEntryBorrows,
        &facts,
    )
    .unwrap();
    assert_eq!(
        guarded
            .get(evaluated.occurrences[0].source)
            .unwrap()
            .boundary
            .len(),
        1
    );
}
