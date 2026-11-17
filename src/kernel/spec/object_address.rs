//! State-selected address operands with no execution-local binder.
use super::*;

pub(super) fn evaluate(
    scope: SpecScope<'_>,
    address: &SpecObjectAddress,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut result = Vec::new();
    for base in evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        &address.base,
        assumptions,
        budget,
    )? {
        let context = assumptions_with_path_context(assumptions, &base.facts, &base.obligations);
        let expression =
            SpecExpression::ProgramExpression(address.program_expression(base.value.into_native()));
        for path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            &expression,
            &context,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &base.facts,
                &base.obligations,
                &path.facts,
                &path.obligations,
                assumptions,
                &context,
            ) else {
                continue;
            };
            result.push(SpecExpressionPath {
                value: path.value,
                facts,
                obligations,
            });
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    fn evaluate_one(scope: SpecScope<'_>, expression: &SpecExpression) -> SpecExpressionPath {
        let mut execution = ExecutionBudget::new();
        let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        paths.pop().unwrap()
    }

    fn address(base: SpecExpression, checked: bool) -> SpecExpression {
        SpecExpression::ObjectAddress(Box::new(SpecObjectAddress {
            base: Box::new(base),
            steps: vec![
                SpecAddressStep::Subobject { width: 4 },
                SpecAddressStep::OffsetBytes { bytes: 8 },
            ],
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
            checked,
        }))
    }

    #[test]
    fn selected_address_base_preserves_c_provenance_qualifiers_and_debts() {
        let _session = VerificationSession::enter();
        let first = Memory::global_pointer("first");
        let second = Memory::global_pointer("second");
        let first_value = ProgramValue::Pointer(
            PointerValue::new(first.clone(), ProgramType::UInt8Pointer)
                .with_pointee_constant(true)
                .with_pointee_volatile(true),
        );
        let second_value = ProgramValue::typed_pointer(second.clone(), ProgramType::UInt8Pointer);
        let memory = Memory::new()
            .with_block(first.block.clone(), 24)
            .with_block(second.block.clone(), 24);
        let mut old = ExecutionState::new().with_memory(memory.clone());
        old.locals.set_typed_with_all_qualifiers(
            "p",
            first_value.clone(),
            ProgramType::UInt8Pointer,
            false,
            true,
            false,
            true,
        );
        let current = ExecutionState::new()
            .with_memory(memory)
            .with_local("p", second_value)
            .with_local("<spec-address-operand>", int32(99));
        let scope = SpecScope::unbound(&current, Some(&old));
        for checked in [false, true] {
            let base = SpecExpression::LoopEntryState(Box::new(SpecExpression::ProgramExpression(
                ProgramExpression::Variable("p".into()),
            )));
            let typed = evaluate_one(scope, &address(base, checked));
            let target = Box::new(crate::kernel::program_expression::typed_load(
                ProgramExpression::Subobject {
                    pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                        pointer: Box::new(ProgramExpression::Value(first_value.clone())),
                        bytes: 8,
                    }),
                    width: 4,
                },
                ProgramType::Int32,
            ));
            let direct = if checked {
                ProgramExpression::CheckedObjectAddress(target)
            } else {
                ProgramExpression::AddressOf(target)
            };
            let expected = evaluate_one(scope, &SpecExpression::ProgramExpression(direct));
            assert_eq!(typed, expected);
            let ProgramValue::Pointer(pointer) = typed.value.into_native() else {
                panic!("an address")
            };
            assert_eq!(pointer.pointer(), &first.offset_by_bytes(8));
            assert!(pointer.pointee_volatile());
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/spec/object_address/tests.rs");
    }
}
