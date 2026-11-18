//! Conservative boundary metadata for an opaque matched instance. These
//! ranges are possible ownership, never unfolded children or read authority.
use super::*;

pub(super) fn construct(
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<ResourceFact>> {
    let matched = definition.matched.as_ref()?;
    if definition.is_recursive() || !definition.witnesses.is_empty() {
        return None;
    }
    let mut evaluation = ExecutionState::at_point(&state.program_point());
    bind(
        definition,
        &(instance.arguments()).native_values(),
        &mut evaluation,
    )?;
    let parameters = definition
        .parameters()
        .iter()
        .map(|p| p.binding_name())
        .collect();
    let mut bounds = BTreeSet::new();
    leaves(
        &parameters,
        &definition.contains,
        &evaluation,
        assumptions,
        &mut bounds,
    )?;
    for arm in &matched.arms {
        crate::instrumentation::record_deterministic_work(1);
        // No model decision or constructor binding is needed: every possible
        // arm must fit the envelope, independently of its logical fields.
        leaves(
            &parameters,
            &arm.contains,
            &evaluation,
            assumptions,
            &mut bounds,
        )?;
        for child in &arm.children {
            crate::instrumentation::record_deterministic_work(1);
            let child_definition = &definitions[definitions
                .binary_search_by(|definition| {
                    crate::instrumentation::record_deterministic_work(1);
                    definition.name().cmp(&child.resource)
                })
                .ok()?];
            if child_definition.is_recursive()
                || child_definition.matched.is_some()
                || !child_definition.witnesses.is_empty()
                || !child_definition.children.is_empty()
            {
                return None;
            }
            let mut arguments = Vec::new();
            for argument in &child.arguments {
                let expression = match argument {
                    SpecExpression::ProgramExpression(expression) => expression.clone(),
                    SpecExpression::Value(value) => ProgramExpression::Value(value.clone()),
                    _ => return None,
                };
                if !summary_transfer::invariant_parameter_expression(&expression, &parameters) {
                    return None;
                }
                let paths = crate::kernel::spec::evaluate_resource_child_argument_paths(
                    &evaluation,
                    argument,
                    assumptions,
                    &BTreeMap::new(),
                    &BTreeMap::new(),
                    &mut ExecutionBudget::beside_live_state(),
                )
                .ok()?;
                let [path] = paths.as_slice() else {
                    return None;
                };
                let ExpressionOutcome::Value(value) = &path.outcome else {
                    return None;
                };
                arguments.push(AlgebraicValue::Program(value.native().as_ref().clone()));
            }
            let mut child_state = ExecutionState::at_point(&state.program_point());
            bind(child_definition, &arguments, &mut child_state)?;
            // Field bindings may depend on the undecided constructor. Only
            // parameter-based ownership is admitted, so they are not needed.
            leaves(
                &child_definition
                    .parameters()
                    .iter()
                    .map(|p| p.binding_name())
                    .collect(),
                child_definition.contains(),
                &child_state,
                assumptions,
                &mut bounds,
            )?;
        }
    }
    if !definition.children.is_empty() {
        return None;
    }
    let bounds = bounds.into_iter().collect::<Vec<_>>();
    // Alternatives may repeat a leaf. Exact repetitions were deduplicated;
    // other overlapping/unsupported envelopes remain opaque. No discovery.
    ResourceContext::new_with_equalities(assumptions)
        .try_compose_checked_ownership_and_occurrences(bounds.clone(), assumptions)
        .ok()?;
    Some(bounds)
}

fn bind(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    evaluation: &mut ExecutionState,
) -> Option<()> {
    if arguments.len() != definition.parameters().len() {
        return None;
    }
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        let value = coerce_program_function_argument_without_obligations(
            argument.as_program_value()?,
            parameter,
        )?;
        evaluation.locals.bind_logical_typed(
            parameter.binding_name().clone(),
            value,
            parameter.program_type(),
        );
    }
    Some(())
}

fn leaves(
    parameters: &BTreeSet<&BindingName>,
    specs: &[ResourceSpec],
    evaluation: &ExecutionState,
    assumptions: &PureFactContext,
    bounds: &mut BTreeSet<ResourceFact>,
) -> Option<()> {
    for spec in specs {
        crate::instrumentation::record_deterministic_work(1);
        if spec.is_view() || matches!(spec.term(), ResourceTerm::Token { .. }) {
            continue;
        }
        if !summary_transfer::invariant_memory_shape(spec, parameters) {
            return None;
        }
        let fact = evaluate_function_resource_spec(
            evaluation,
            spec,
            assumptions,
            &mut ExecutionBudget::beside_live_state(),
        )
        .ok()?
        .ok()?;
        bounds.insert(fact);
    }
    Some(())
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::kernel::program_expression::{int32_literal, variable};

    pub(crate) fn case(
        p: Address,
        leaves: u32,
        identity: u64,
    ) -> (ResourceFact, Vec<CompositeResourceDefinition>) {
        let (head, mut root) = super::super::specialized_return_tests::matched(
            AlgebraicTerm {
                algebraic_type: super::super::specialized_return_tests::matched_type(),
                node: AlgebraicTermNode::Variable(Variable(identity + 1)),
            },
            identity,
        );
        let Resource::Instance(instance) = head.resource() else {
            unreachable!()
        };
        let head = ResourceFact::own(Resource::Instance(
            ResourceInstance::new(
                instance.identity,
                instance.name().to_owned(),
                vec![ProgramValue::pointer(p).into()].into(),
                instance.schema().clone(),
                instance.fields().to_vec().into(),
            )
            .unwrap(),
        ));
        root.parameters = vec![program_parameter("p", ProgramType::Int32Pointer)];
        for (index, arm) in root.matched.as_mut().unwrap().arms.iter_mut().enumerate() {
            arm.contains.clear();
            arm.children = vec![ResourceChildSpec {
                name: "child".into(),
                resource: "bound_cell".into(),
                binding: Variable(identity + 10 + index as u64),
                arguments: vec![SpecExpression::ProgramExpression(variable("p"))],
                field_bindings: vec![],
            }];
        }
        let child = CompositeResourceDefinition::new(
            "bound_cell",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            (0..leaves)
                .map(|i| {
                    ResourceSpec::owned_memory(MemorySegment::new(
                        variable("p"),
                        int32_literal(i * 2),
                        int32_literal(i * 2 + 1),
                    ))
                })
                .collect(),
            vec![],
        )
        .with_instance_schema(Some(ResourceFieldSchema::new(vec![]).unwrap()));
        (head, vec![child, root])
    }

    #[test]
    fn opaque_envelopes_preserve_identity_and_check_overlap_without_exposing_children() {
        let facts = PureFactContext::new();
        let p = Address::symbolic(Variable(8_930_000));
        let (head, definitions) = case(p.clone(), 1, 8_930_100);
        let outputs = EvaluatedReturnResources::new(&facts)
            .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        let _fast = crate::kernel::search::FastOperationScope::enter("opaque matched envelope");
        let bodies = ConstructedReturnBodies::construct(
            &outputs,
            &definitions,
            &ExecutionState::new(),
            &facts,
        );
        let source = outputs.occurrences[0].source;
        let body = bodies.get(source).unwrap();
        assert_eq!(body.expansion, vec![head]);
        assert!(
            body.frontier.is_empty()
                && body.viewed_children.is_empty()
                && body.transfers.is_empty()
        );
        assert!(body.folded.is_empty());
        assert_eq!(body.boundary.len(), 1);
        let mut boundary = EscrowRecoveryBoundary::default();
        boundary.record(source, vec![], body.escrow_boundary());
        for (start, succeeds) in [(0, false), (2, true)] {
            let held = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(
                    p.clone(),
                    start.into(),
                    (start + 1).into(),
                )),
            );
            assert_eq!(
                boundary
                    .admit(&held, false, &outputs.resources, &facts)
                    .is_ok(),
                succeeds
            );
        }
    }

    #[test]
    fn viewed_instances_are_refused_before_envelope_construction() {
        let facts = PureFactContext::new();
        let (head, _) = case(Address::symbolic(Variable(8_930_800)), 1, 8_930_900);
        let view = ResourceFact::View(head.resource().clone());
        let _fast = crate::kernel::search::FastOperationScope::enter("viewed opaque envelope");
        assert!(matches!(
            EvaluatedReturnResources::new(&facts).admit(
                view,
                ReturnOwnershipOrigin::Description,
                &facts
            ),
            Err(ResourceContextValidityError::InvalidExclusiveAccess(_))
        ));
    }

    #[test]
    fn opaque_envelopes_reserve_shared_input_supply_once() {
        let facts = PureFactContext::new();
        let p = Address::symbolic(Variable(8_930_200));
        let (head, definitions) = case(p.clone(), 1, 8_930_300);
        let mut plan = ConsumedCellReturns::default();
        plan.retain_frontier(
            [MemoryRange::new(p.clone(), 0u32.into(), 1u32.into())],
            &facts,
        );
        let composition = ReturnResourceComposition::ApplyTransfers(&plan);
        let outputs = EvaluatedReturnResources::for_composition(composition, &facts)
            .admit(head, ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        let _fast =
            crate::kernel::search::FastOperationScope::enter("opaque envelope input custody");
        let bodies = ConstructedReturnBodies::try_construct(
            &outputs,
            &definitions,
            &ExecutionState::new(),
            composition,
            &facts,
        )
        .unwrap();
        assert!(
            bodies
                .get(outputs.occurrences[0].source)
                .unwrap()
                .escrow_boundary()
                .is_empty()
        );
        let (second, _) = case(p, 1, 8_930_400);
        let repeated = outputs
            .admit(second, ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        assert!(
            ConstructedReturnBodies::try_construct(
                &repeated,
                &definitions,
                &ExecutionState::new(),
                composition,
                &facts
            )
            .is_none()
        );
    }

    #[test]
    fn constructor_dependent_child_addresses_keep_an_opaque_refusal() {
        let facts = PureFactContext::new();
        let (head, mut definitions) = case(Address::symbolic(Variable(8_930_500)), 1, 8_930_600);
        definitions[1].matched.as_mut().unwrap().arms[1].children[0].arguments[0] =
            SpecExpression::ProgramExpression(variable("ptr"));
        let outputs = EvaluatedReturnResources::new(&facts)
            .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        let _fast = crate::kernel::search::FastOperationScope::enter("unsupported opaque envelope");
        let bodies = ConstructedReturnBodies::construct(
            &outputs,
            &definitions,
            &ExecutionState::new(),
            &facts,
        );
        let body = bodies.get(outputs.occurrences[0].source).unwrap();
        assert_eq!(body.folded, vec![(head, outputs.occurrences[0].source)]);
        assert!(body.boundary.is_empty());
    }
}
