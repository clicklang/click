use super::*;

fn adapter(expression: &SpecExpression) -> Vec<ExpressionPath<SpecValue>> {
    evaluate_resource_child_argument_paths(
        &ExecutionState::new(),
        expression,
        &PureFactContext::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut ExecutionBudget::new(),
    )
    .unwrap()
}

fn sum(format: MachineIntegerType) -> SpecExpression {
    SpecExpression::Add(
        Box::new(SpecExpression::Value(
            format.value_from_term(MachineTerm::Variable(Variable(998252))),
        )),
        Box::new(SpecExpression::Value(format.value_from_term(
            match format {
                MachineIntegerType::Int32 => MachineTerm::constant(1),
                MachineIntegerType::UInt32 => MachineTerm::uint32_constant(1),
                MachineIntegerType::Int64 => MachineTerm::int64_constant(1),
                MachineIntegerType::UInt64 => MachineTerm::uint64_constant(1),
                _ => unreachable!(),
            },
        ))),
    )
}

#[test]
fn specification_execution_handoff_keeps_the_produced_root_and_debts() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let expression = sum(format);
        let mut budget = ExecutionBudget::new();
        let expected = evaluate_spec_expression_paths_with_bindings_in(
            &ExecutionState::new(),
            &expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut SpecEvaluation::checked(&mut budget),
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let actual = adapter(&expression);
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert!(matches!(expected.value, SpecValue::Shared(_)));
            assert_eq!(actual.outcome, ExpressionOutcome::Value(expected.value));
            assert_eq!(actual.facts, expected.facts);
            assert_eq!(actual.obligations, expected.obligations);
            if format.format().is_signed() {
                assert!(!actual.obligations.is_empty());
            }
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn program_expression_handoff_preserves_values_and_errors() {
    let _session = crate::kernel::VerificationSession::enter();
    for expression in [
        ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::uint32_constant(7))),
        ProgramExpression::Variable("missing".into()),
        ProgramExpression::Divide(
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(1),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(0),
            ))),
        ),
    ] {
        let expected = {
            let _scope = crate::kernel::eval::SpecificationReadScope::enter();
            evaluate_program_expression_paths(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        };
        let actual = adapter(&SpecExpression::ProgramExpression(expression));
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert_eq!(
                actual.outcome.map_value(SpecValue::into_native),
                expected.outcome
            );
            assert_eq!(actual.facts, expected.facts);
            assert_eq!(actual.obligations, expected.obligations);
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/execution_handoff_tests.rs");
}

#[test]
fn symbolic_integer_conversions_produce_shared_roots_with_the_same_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    for destination in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
        MachineIntegerType::Int128,
        MachineIntegerType::UInt128,
    ] {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::Variable(
                Variable(999996),
            ))),
            destination,
        };
        let evaluate = |disabled| {
            let mut budget = ExecutionBudget::new();
            let mut evaluation = SpecEvaluation::logical(&mut budget);
            evaluation.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &BTreeMap::new(),
                &mut evaluation,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let native = evaluate(true);
        let exports = KernelTermExport::machine_export_count();
        let retained = evaluate(false);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let root = retained.value.shared().expect("retained conversion");
        assert!(
            matches!(root.node(), KernelTermNode::IntegerToMachine { destination: actual, .. } if *actual == destination)
        );
        assert_eq!(retained.facts, native.facts);
        assert_eq!(retained.obligations, native.obligations);
        assert!(!retained.obligations.is_empty());
        assert_eq!(retained.value.into_native(), native.value.into_native());
    }
}

#[test]
fn specification_machine_expression_handoff_keeps_the_execution_root() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let source = ProgramExpression::Add(
            Box::new(ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(999997))),
            )),
            Box::new(ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(999998))),
            )),
        );
        let state = ExecutionState::new();
        let assumptions = PureFactContext::new();
        let expected = {
            let _scope = crate::kernel::eval::SpecificationReadScope::enter();
            evaluate_expression_value_paths(
                &state,
                &source,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap()
            .into_iter()
            .find(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
            .expect("the defined execution path")
        };
        let ExpressionOutcome::Value(expected_value) = expected.outcome else {
            panic!()
        };
        assert!(expected_value.shared().is_some());
        let expression = SpecExpression::ProgramExpression(source);
        let evaluate = |disabled| {
            let mut budget = ExecutionBudget::new();
            let mut evaluation = SpecEvaluation::logical(&mut budget);
            evaluation.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &state,
                &expression,
                &assumptions,
                &BTreeMap::new(),
                &mut evaluation,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let exports = KernelTermExport::machine_export_count();
        let actual = evaluate(false);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(actual.value.shared(), expected_value.shared());
        assert_eq!(actual.obligations, expected.obligations);
        assert_eq!(actual.facts, expected.facts);
        let native = evaluate(true);
        assert!(native.value.shared().is_none());
        assert_eq!(actual.obligations, native.obligations);
        assert_eq!(actual.facts, native.facts);
        assert_eq!(actual.value.into_native(), native.value.into_native());
    }
}

#[test]
fn boolean_lowering_preserves_logical_roots_and_exact_c_carriers() {
    let _session = crate::kernel::VerificationSession::enter();
    let condition = ConditionTerm::Variable(Variable(999991));
    let cases = [
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 0,
            },
            true,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 1,
            },
            true,
        ),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(condition),
            },
            true,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 2,
            },
            false,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt32,
                bits: 1,
            },
            false,
        ),
        (MachineTerm::Variable(Variable(999992)), false),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(ConditionTerm::Constant(true)),
            },
            false,
        ),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt32,
                value: Box::new(ConditionTerm::Variable(Variable(999993))),
            },
            false,
        ),
    ];
    for (word, logical) in cases {
        // The C evaluator rejects malformed Bool values before this handoff.
        // Specification payloads must still preserve those exact carriers.
        let valid_c_value = matches!(
            &word,
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 0 | 1
            } | MachineTerm::Variable(_)
                | MachineTerm::BoolCast {
                    to: MachineIntegerType::UInt8,
                    ..
                }
        );
        let value = ProgramValue::Bool(word);
        let mut expressions = vec![SpecExpression::Value(value.clone())];
        if valid_c_value {
            expressions.push(SpecExpression::ProgramExpression(ProgramExpression::Value(
                value.clone(),
            )));
        }
        for expression in expressions {
            let evaluate = |disabled| {
                let mut budget = ExecutionBudget::new();
                let mut evaluation = SpecEvaluation::logical(&mut budget);
                evaluation.machine_result_production_disabled = disabled;
                evaluate_spec_expression_paths_with_bindings_in(
                    &ExecutionState::new(),
                    &expression,
                    &PureFactContext::new(),
                    &BTreeMap::new(),
                    &mut evaluation,
                )
                .unwrap()
                .pop()
                .unwrap()
            };
            let retained = evaluate(false);
            let native = evaluate(true);
            assert_eq!(retained.value.shared().is_some(), logical, "{value:?}");
            if logical {
                let expected = KernelTermImport::default()
                    .argument(&PureFunctionArgument::Value(value.clone()));
                assert_eq!(retained.value.shared(), Some(&expected));
            }
            assert!(native.value.shared().is_none());
            assert_eq!(retained.facts, native.facts);
            assert_eq!(retained.obligations, native.obligations);
            assert_eq!(retained.value.into_native(), value);
            assert_eq!(native.value.into_native(), value);
        }
    }
}

#[test]
fn algebraic_lowering_retains_program_envelopes_and_handoff_roots() {
    let _session = crate::kernel::VerificationSession::enter();
    for native in [
        KernelMatch::test_scrutinee(vec![]),
        AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("T".into()),
            node: AlgebraicTermNode::Variable(Variable(999994)),
        },
    ] {
        let root = KernelTermImport::default().algebraic(&native);
        let program_type = ProgramType::Parameter(TypeParameterName::of(&native.algebraic_type));
        let expected = AlgebraicValue::Program(ProgramValue::Parameter(Box::new(native.clone())));
        let exports = KernelTermExport::algebraic_export_count();
        let field = AlgebraicFieldResult::from_program(SpecValue::Shared(root.clone()));
        assert!(field.has_type(&AlgebraicValueType::Program(program_type)));
        assert!(!field.has_type(&native.algebraic_type.value_type()));
        let envelope = field.clone().into_kernel();
        assert!(
            matches!(envelope.node(), KernelTermNode::ProgramParameter { operand } if operand == &root)
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert_eq!(field.into_native(), expected);
        assert_eq!(
            AlgebraicFieldResult::from_program(SpecValue::Shared(envelope.clone())).into_kernel(),
            envelope
        );
        assert_eq!(
            AlgebraicFieldResult::from_algebraic(AlgebraicResult::Shared(root.clone()))
                .into_kernel(),
            root
        );
        {
            let stored = root;
            let mut state = ExecutionState::new();
            state.locals.set_retained_typed_with_all_qualifiers(
                "value",
                SpecValue::Shared(stored.clone()),
                program_type,
                false,
                false,
                false,
                false,
            );
            let expression =
                SpecExpression::ProgramExpression(ProgramExpression::Variable("value".into()));
            let evaluate = |disabled| {
                let mut budget = ExecutionBudget::new();
                let mut evaluation = SpecEvaluation::logical(&mut budget);
                evaluation.machine_result_production_disabled = disabled;
                evaluate_spec_expression_paths_with_bindings_in(
                    &state,
                    &expression,
                    &PureFactContext::new(),
                    &BTreeMap::new(),
                    &mut evaluation,
                )
                .unwrap()
                .pop()
                .unwrap()
            };
            let exports = KernelTermExport::algebraic_export_count();
            let actual = evaluate(false);
            assert_eq!(actual.value.shared(), Some(&stored));
            assert_eq!(KernelTermExport::algebraic_export_count(), exports);
            let old = evaluate(true);
            assert_eq!(actual.facts, old.facts);
            assert_eq!(actual.obligations, old.obligations);
            assert_eq!(actual.value.into_native(), old.value.into_native());
        }
    }
}

#[test]
fn pointer_lowering_keeps_producers_and_complete_metadata() {
    use std::sync::Arc;
    let _session = crate::kernel::VerificationSession::enter();
    let class = crate::kernel::effective_type::CAccessClass::Scalar(
        crate::kernel::effective_type::CScalarClass::Int,
    );
    let source = PointerValue::new(
        Pointer::symbolic(Variable(999982)),
        ProgramType::VoidPointer,
    )
    .with_address(Pointer::symbolic(Variable(999981)))
    .with_bounds_owner(Some(Arc::new(Pointer::symbolic(Variable(999983)))))
    .with_pointee_volatile(true)
    .with_pointee_constant(true)
    .with_bounds(Some(SubobjectBounds {
        start: Pointer::symbolic(Variable(999984)),
        width: MachineTerm::Variable(Variable(999985)),
    }))
    .with_object_type_evidence(Some(ObjectTypeEvidence::parameter(class, 3, 999986, false)));
    let payload = SharedPointerValue::import(&source);
    let memory = intern_memory(SymbolicMemory::new());
    let address = SharedPointerAddress::import(&SymbolicMemory::global_pointer("pointer-slot"));
    let roots = [
        KernelTerm::shared_pointer_value(payload.clone()),
        KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(source.program_type()),
                "pointer_source".into(),
                vec![],
            ),
            payload.clone(),
        ),
        KernelTerm::shared_pointer_read(payload.clone(), memory.clone(), address.clone()),
    ];
    for root in roots {
        let field = AlgebraicFieldResult::from_program(SpecValue::Shared(root.clone()))
            .without_pointer_constant()
            .into_kernel();
        let expected = SharedPointerValue::import(&source.clone().with_pointee_constant(false));
        assert!(
            field
                .pointer_payload()
                .unwrap()
                .same_source_payload(&expected)
        );
        assert_eq!(
            field.pointer_payload().unwrap().node().address,
            payload.node().address
        );
        assert_eq!(
            field.pointer_payload().unwrap().node().provenance,
            payload.node().provenance
        );
        match (root.node(), field.node()) {
            (KernelTermNode::PointerValue { .. }, KernelTermNode::PointerValue { .. }) => {}
            (
                KernelTermNode::PointerCall { call: a, .. },
                KernelTermNode::PointerCall { call: b, .. },
            ) => assert_eq!(a, b),
            (
                KernelTermNode::PointerRead {
                    memory: a,
                    address: p,
                    ..
                },
                KernelTermNode::PointerRead {
                    memory: b,
                    address: q,
                    ..
                },
            ) => {
                assert_eq!(a, b);
                assert_eq!(p, q);
            }
            _ => panic!("pointer producer changed"),
        }
        assert_eq!(
            AlgebraicFieldResult::from_program(SpecValue::Shared(field.clone()))
                .without_pointer_constant()
                .into_kernel(),
            field
        );
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "p",
            SpecValue::Shared(root.clone()),
            source.program_type(),
            false,
            true,
            false,
            true,
        );
        let expression = SpecExpression::ProgramExpression(ProgramExpression::Variable("p".into()));
        let evaluate = |disabled| {
            let mut budget = ExecutionBudget::new();
            let mut evaluation = SpecEvaluation::logical(&mut budget);
            evaluation.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &state,
                &expression,
                &PureFactContext::new(),
                &BTreeMap::new(),
                &mut evaluation,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let actual = evaluate(false);
        assert_eq!(actual.value.shared(), Some(&root));
        assert!(
            actual
                .value
                .shared()
                .unwrap()
                .pointer_payload()
                .unwrap()
                .same_source_payload(&payload)
        );
        let old = evaluate(true);
        assert_eq!(actual.facts, old.facts);
        assert_eq!(actual.obligations, old.obligations);
        assert_eq!(actual.value.into_native(), old.value.into_native());
    }
}

#[test]
fn explicit_pointer_cast_lowering_keeps_native_bounds_rules() {
    let _session = crate::kernel::VerificationSession::enter();
    for (source, target, keeps_bounds) in [
        (ProgramType::VoidPointer, ProgramType::VoidPointer, false),
        (ProgramType::Int32Pointer, ProgramType::UInt8Pointer, false),
        (ProgramType::Int8Pointer, ProgramType::UInt8Pointer, true),
    ] {
        let pointer = PointerValue::new(Pointer::symbolic(Variable(999940)), source)
            .with_pointee_constant(true)
            .with_bounds(Some(SubobjectBounds {
                start: Pointer::symbolic(Variable(999940)),
                width: MachineTerm::constant(4),
            }));
        let expression = SpecExpression::Cast(
            Box::new(SpecExpression::Value(ProgramValue::Pointer(pointer))),
            target,
        );
        let evaluate = |disabled| {
            let mut execution = ExecutionBudget::new();
            let mut budget = SpecEvaluation::logical(&mut execution);
            budget.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &BTreeMap::new(),
                &mut budget,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let actual = evaluate(false);
        let old = evaluate(true);
        let ProgramValue::Pointer(expected) = old.value.into_native() else {
            panic!()
        };
        assert_eq!(expected.bounds().is_some(), keeps_bounds);
        assert!(
            actual
                .value
                .shared()
                .unwrap()
                .pointer_payload()
                .unwrap()
                .same_source_payload(&SharedPointerValue::import(&expected))
        );
        assert_eq!(actual.facts, old.facts);
        assert_eq!(actual.obligations, old.obligations);
        assert_eq!(actual.value.into_native(), ProgramValue::Pointer(expected));
    }
}

#[test]
fn float_lowering_conversions_preserve_bits_roots_and_path_context() {
    let _session = crate::kernel::VerificationSession::enter();
    let evaluate = |expression: &SpecExpression, disabled| {
        let mut budget = ExecutionBudget::new();
        let mut evaluation = SpecEvaluation::logical(&mut budget);
        evaluation.machine_result_production_disabled = disabled;
        evaluate_spec_expression_paths_with_bindings_in(
            &ExecutionState::new(),
            expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut evaluation,
        )
        .unwrap()
        .pop()
        .unwrap()
    };
    for (format, target, literals) in [
        (
            KernelFloatType::Float32,
            ProgramType::Float64,
            vec![0, 0x8000_0000, 0x7fc0_1234, 0x7f80_0000, 1, 0x3f80_0000],
        ),
        (
            KernelFloatType::Float64,
            ProgramType::Float32,
            vec![
                0,
                0x8000_0000_0000_0000,
                0x7ff8_0000_0000_1234,
                0x7ff0_0000_0000_0000,
                1,
                0x3ff0_0000_0000_0000,
            ],
        ),
    ] {
        let literal = |bits| match format {
            KernelFloatType::Float32 => MachineTerm::constant(bits as u32),
            KernelFloatType::Float64 => MachineTerm::uint64_constant(bits),
        };
        let mut values = literals.into_iter().map(literal).collect::<Vec<_>>();
        values.push(MachineTerm::Variable(Variable(999970)));
        values.push(match format {
            KernelFloatType::Float32 => MachineTerm::Float32Negate(Box::new(literal(0))),
            KernelFloatType::Float64 => MachineTerm::Float64Negate(Box::new(literal(0))),
        });
        values.push(match format {
            KernelFloatType::Float32 => MachineTerm::Float32Binary {
                operator: FloatBinaryOperator::Add,
                left: Box::new(literal(0x3f80_0000)),
                right: Box::new(literal(0x3f80_0000)),
            },
            KernelFloatType::Float64 => MachineTerm::Float64Binary {
                operator: FloatBinaryOperator::Add,
                left: Box::new(literal(0x3ff0_0000_0000_0000)),
                right: Box::new(literal(0x3ff0_0000_0000_0000)),
            },
        });
        for value in values {
            let operand = SpecExpression::Value(format.value(value));
            let source = evaluate(&operand, false);
            let expression = SpecExpression::Cast(Box::new(operand), target);
            let exports = KernelTermExport::float_export_count();
            let actual = evaluate(&expression, false);
            assert_eq!(KernelTermExport::float_export_count(), exports);
            if let KernelTermNode::FloatConvert { operand, .. } =
                actual.value.shared().unwrap().node()
            {
                assert_eq!(Some(operand), source.value.shared());
            }
            let old = evaluate(&expression, true);
            assert_eq!(actual.facts, old.facts);
            assert_eq!(actual.obligations, old.obligations);
            assert_eq!(actual.value.into_native(), old.value.into_native());
        }
    }
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for target in [ProgramType::Float32, ProgramType::Float64] {
            let operand = sum(format);
            let source = evaluate(&operand, false);
            let expression = SpecExpression::Cast(Box::new(operand), target);
            let exports = KernelTermExport::machine_export_count();
            let actual = evaluate(&expression, false);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let KernelTermNode::FloatConvert { operand, .. } =
                actual.value.shared().unwrap().node()
            else {
                panic!("retained numeric conversion")
            };
            assert_eq!(Some(operand), source.value.shared());
            let old = evaluate(&expression, true);
            assert_eq!(actual.facts, old.facts);
            assert_eq!(actual.obligations, old.obligations);
            assert_eq!(actual.value.into_native(), old.value.into_native());
        }
    }
}

#[test]
fn mixed_call_assembly_preserves_typed_roots_without_exports() {
    // Oracle-only normalization of the pre-existing numeric argument carrier
    // difference. Production call assembly keeps its shared numeric handles.
    fn native_call_value(value: SpecValue) -> ProgramValue {
        let value = value.into_native();
        let Some(format) = MachineIntegerType::from_program_type(value.program_type()) else {
            return value;
        };
        let Some(MachineTerm::ClickFunctionApplication { name, arguments }) =
            program_value_bitvector_term(&value)
        else {
            return value;
        };
        let arguments = arguments
            .into_iter()
            .map(|argument| match argument {
                PureFunctionArgument::SharedMachine(value) => {
                    PureFunctionArgument::Value(value.ty().value_from_term(value.value().clone()))
                }
                argument => argument,
            })
            .collect();
        format.value_from_term(MachineTerm::ClickFunctionApplication { name, arguments })
    }
    let _session = crate::kernel::VerificationSession::enter();
    let algebraic_type = AlgebraicType::parameter("T".into());
    let algebraic = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(999960)),
    };
    let pointer = PointerValue::new(
        Pointer::symbolic(Variable(999961)),
        ProgramType::Int32Pointer,
    )
    .with_pointee_constant(true);
    let arguments = vec![
        SpecPureFunctionArgument::Value(sum(MachineIntegerType::UInt32)),
        SpecPureFunctionArgument::Value(SpecExpression::Value(ProgramValue::Float32(
            MachineTerm::Float32Binary {
                operator: FloatBinaryOperator::Add,
                left: Box::new(MachineTerm::Variable(Variable(999962))),
                right: Box::new(MachineTerm::constant(0x3f80_0000)),
            },
        ))),
        SpecPureFunctionArgument::Value(SpecExpression::Value(ProgramValue::Parameter(Box::new(
            algebraic,
        )))),
        SpecPureFunctionArgument::Algebraic(SpecAlgebraicExpression {
            algebraic_type,
            node: SpecAlgebraicExpressionNode::Variable(Variable(999963)),
        }),
        SpecPureFunctionArgument::Integer(SpecIntegerExpression::Term(IntegerTerm::Variable(
            Variable(999964),
        ))),
        SpecPureFunctionArgument::Value(SpecExpression::Value(ProgramValue::Bool(
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 1,
            },
        ))),
        SpecPureFunctionArgument::Value(SpecExpression::Value(ProgramValue::Pointer(
            pointer.clone(),
        ))),
        SpecPureFunctionArgument::Value(SpecExpression::Value(int32(7))),
    ];
    for result_type in [ProgramType::Bool, ProgramType::Int32, ProgramType::UInt64] {
        let expression = SpecExpression::PureFunctionApplication {
            name: "mixed_roots".into(),
            arguments: arguments.clone(),
            result_type,
            pointer_result: None,
            result_object_class: None,
        };
        let evaluate = |disabled| {
            let mut execution = ExecutionBudget::new();
            let mut budget = SpecEvaluation::logical(&mut execution);
            budget.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &BTreeMap::new(),
                &mut budget,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let floats = KernelTermExport::float_export_count();
        let algebraics = KernelTermExport::algebraic_export_count();
        let actual = evaluate(false);
        assert_eq!(KernelTermExport::float_export_count(), floats);
        assert_eq!(KernelTermExport::algebraic_export_count(), algebraics);
        let KernelTermNode::Call { arguments, .. } = actual.value.shared().unwrap().node() else {
            panic!("common call")
        };
        assert_eq!(arguments.len(), 8);
        assert!(matches!(
            arguments[1].node(),
            KernelTermNode::FloatBinary { .. }
        ));
        assert!(matches!(
            arguments[2].node(),
            KernelTermNode::ProgramParameter { .. }
        ));
        assert!(matches!(arguments[3].ty(), KernelType::Algebraic(_)));
        assert_eq!(arguments[4].ty(), &KernelType::Integer);
        assert_eq!(arguments[5].ty(), &KernelType::Bool);
        assert!(
            arguments[6]
                .pointer_payload()
                .unwrap()
                .same_source_payload(&SharedPointerValue::import(&pointer))
        );
        let old = evaluate(true);
        assert_eq!(actual.facts, old.facts);
        assert_eq!(actual.obligations, old.obligations);
        assert_eq!(
            native_call_value(actual.value),
            native_call_value(old.value)
        );
    }
    for value in [
        ProgramValue::Void,
        ProgramValue::Pointer(pointer),
        ProgramValue::Bool(MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        }),
    ] {
        let arguments = vec![SpecCallArgument::Native(PureFunctionArgument::Value(
            value.clone(),
        ))];
        assert!(common_call_arguments(&arguments).is_none());
        assert_eq!(
            call_arguments(arguments),
            vec![PureFunctionArgument::Value(value)]
        );
    }
}
