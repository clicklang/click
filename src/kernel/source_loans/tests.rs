use super::*;
use crate::kernel::eval::{evaluate_c_expression_paths, execute_c_statement_paths};
use crate::languages::rust::schema::{self as r, Expression as E, MirStatement as M, Type};

fn reference_type() -> Type {
    Type::Reference {
        mutable: true,
        pointee: Box::new(Type::I32),
    }
}
fn local(name: &str) -> E {
    E::Local { name: name.into() }
}
fn deref(name: &str) -> E {
    E::Deref {
        reference: Box::new(local(name)),
        value_type: Type::I32,
    }
}
fn assign(target: E, value: E) -> M {
    M::Assign { target, value }
}
fn place(name: &str, value_type: Type) -> r::Place {
    r::Place {
        name: name.into(),
        value_type,
        span: r::Span { line: 1, column: 1 },
    }
}
fn export() -> r::RustExport {
    r::RustExport {
        schema: r::SCHEMA,
        compiler_commit: "test".into(),
        target: r::TARGET.into(),
        edition: "2021".into(),
        overflow_checks: true,
        panic: "abort".into(),
        mir_opt_level: 0,
        logical_source: "borrow.rs".into(),
        records: vec![],
        functions: vec![r::Function {
            name: "test::reuse".into(),
            return_type: Type::Unit,
            parameters: vec![place("parent", reference_type())],
            body: vec![],
            external: false,
            captures: 0,
            span: r::Span { line: 1, column: 1 },
            mir: Some(r::MirBody {
                locals: vec![place("child", reference_type()), place("x", Type::I32)],
                blocks: vec![r::MirBlock {
                    statements: vec![
                        assign(
                            local("child"),
                            E::Borrow {
                                place: Box::new(deref("parent")),
                                value_type: reference_type(),
                            },
                        ),
                        assign(deref("child"), E::Integer { value: 7 }),
                        assign(deref("parent"), E::Integer { value: 8 }),
                    ],
                    terminator: r::MirTerminator::Return,
                }],
            }),
        }],
    }
}
fn body(export: &r::RustExport, identity: &str) -> CStatement {
    let (functions, _) =
        crate::languages::rust::lowering::lower_with_identity(export, Some(identity)).unwrap();
    functions[0].to_kernel_function().body().clone()
}
fn leaves(body: &CStatement) -> Vec<CStatement> {
    let mut leaves = vec![];
    let mut pending = vec![body];
    while let Some(statement) = pending.pop() {
        match statement {
            CStatement::Seq(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            _ => leaves.push(statement.clone()),
        }
    }
    leaves
}
fn initial() -> (CState, ResourceOccurrenceId) {
    let pointer = Pointer {
        block: "source-scalar".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        pointer.clone(),
        0.into(),
        1.into(),
        4,
    ));
    let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
    let support = resources.unique_owned_occurrence_for_fact(&fact).unwrap().0;
    (
        CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 4)
                    .store(pointer.clone(), int32(4)),
            )
            .with_resource_context(resources)
            .with_local(
                "parent",
                CValue::typed_pointer(pointer, CType::Int32Pointer),
            ),
        support,
    )
}
fn execute(state: &CState, statement: &CStatement) -> CStatementOutcome {
    let environment = CExecutionEnvironment::default();
    let mut paths = execute_c_statement_paths(
        state,
        statement,
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}
fn normal(outcome: CStatementOutcome) -> CState {
    match outcome {
        CStatementOutcome::Normal(state) => *state,
        other => panic!("expected normal: {other:?}"),
    }
}
fn read(state: &CState, expression: CExpression) -> CExpressionOutcome {
    let mut paths = evaluate_c_expression_paths(
        state,
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}
fn active(initial: &CState, body: &CStatement) -> (CState, CStatement, CStatement) {
    let mut state = initial.clone();
    let mut birth = None;
    for statement in leaves(body) {
        if matches!(&statement, CStatement::TypedStore { source, .. } if source.lease_plan().is_some())
        {
            return (state, birth.expect("source birth"), statement);
        }
        state = normal(execute(&state, &statement));
        if matches!(&statement, CStatement::Assign { source, .. } if source.lease_plan().is_some())
        {
            birth = Some(statement);
        }
    }
    panic!("source ending missing");
}

#[test]
fn source_scalar_lease_executes_locked_birth_store_end_and_parent_reuse() {
    let program = body(&export(), "locked-source");
    let (initial, support) = initial();
    let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
        panic!("source function return");
    };
    assert_eq!(
        read(&state, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(8))
    );
    assert!(
        state
            .resources()
            .owned_fact_for_occurrence(support)
            .is_some()
    );
    assert!(!state.has_local_scalar_references());
    assert!(matches!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_suspends_raw_parent_and_recovers_exact_owned_occurrence() {
    let program = body(&export(), "locked-source");
    let (initial, support) = initial();
    let (state, _, ending) = active(&initial, &program);
    assert!(
        state
            .resources()
            .owned_fact_for_occurrence(support)
            .is_none()
    );
    assert!(matches!(
        read(&state, c_load(c_variable("parent"))),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    assert!(matches!(
        execute(&state, &c_store(c_variable("parent"), c_int32_literal(9))),
        CStatementOutcome::RuntimeError(_)
    ));
    assert_eq!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(4))
    );
    let recovered = normal(execute(&state, &ending));
    assert_eq!(
        read(&recovered, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(7))
    );
    assert!(
        recovered
            .resources()
            .owned_fact_for_occurrence(support)
            .is_some()
    );
    assert!(matches!(
        execute(&recovered, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_tags_are_semantic_and_observation_labels_cannot_end_loans() {
    let program = body(&export(), "locked-source");
    let (initial, _) = initial();
    let (state, birth, ending) = active(&initial, &program);
    let mut unbound = birth.clone();
    let CStatement::Assign { source, .. } = &mut unbound else {
        panic!();
    };
    *source = CStatementAssignSource::new(source.as_ref().unwrap().clone());
    assert_ne!(birth, unbound);
    let mut unbound = ending.clone();
    let CStatement::TypedStore { source, .. } = &mut unbound else {
        panic!();
    };
    *source = CStatementStoreSource::new(source.as_ref().unwrap().clone());
    assert_ne!(ending, unbound);
    let not_recovered = normal(execute(&state, &unbound));
    assert!(not_recovered.has_local_scalar_references());
    assert!(matches!(
        execute(&not_recovered, &c_return(c_void_value())),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_rejects_transplanted_operands_and_other_locked_plans() {
    let program = body(&export(), "locked-source");
    let (initial, _) = initial();
    let (state, birth, ending) = active(&initial, &program);
    let mut changed = ending;
    let CStatement::TypedStore { value, .. } = &mut changed else {
        panic!();
    };
    *value = c_int32_literal(99);
    assert!(matches!(
        execute(&state, &changed),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    assert_eq!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(4))
    );
    let mut changed = birth;
    let CStatement::Assign { expression, .. } = &mut changed else {
        panic!();
    };
    *expression = c_variable("parent");
    assert!(matches!(
        execute(&state, &changed),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let other = body(&export(), "other-lock");
    let (_, _, other_ending) = active(&initial, &other);
    assert!(matches!(
        execute(&state, &other_ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_requires_actual_birth_and_current_invocation_custody() {
    let program = body(&export(), "locked-source");
    let (initial, _) = initial();
    let (first, _, ending) = active(&initial, &program);
    let (mut second, _, _) = active(&initial, &program);
    let first_child = first.locals.get("child").unwrap().clone();
    assert_ne!(first_child, *second.locals.get("child").unwrap());
    eval::sync_stack_local(&mut second, "child", &first_child);
    second.locals.set("child", first_child);
    assert!(matches!(
        execute(&second, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let parent = initial.locals.get("parent").unwrap().clone();
    let without_birth = initial.with_local("child", parent);
    assert!(matches!(
        execute(&without_birth, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_declared_local_parent_is_suspended_and_updated() {
    let mut initial = normal(execute(&CState::new(), &c_declare("number", CType::Int32)));
    initial = normal(execute(&initial, &c_assign("number", c_int32_literal(4))));
    let pointer = initial.locals.slot("number").unwrap().clone();
    initial = initial.with_local(
        "parent",
        CValue::typed_pointer(pointer, CType::Int32Pointer),
    );
    let program = body(&export(), "locked-source");
    let (state, _, ending) = active(&initial, &program);
    assert!(matches!(
        read(&state, c_variable("number")),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    assert!(matches!(
        execute(&state, &c_assign("number", c_int32_literal(9))),
        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    let recovered = normal(execute(&state, &ending));
    assert_eq!(
        read(&recovered, c_variable("number")),
        CExpressionOutcome::Value(int32(7))
    );
}

#[test]
fn source_scalar_lease_plan_preparation_scales_with_selected_function() {
    let mut measurements = vec![];
    for size in [16, 64, 256, 1024] {
        let mut export = export();
        let statements = &mut export.functions[0].mir.as_mut().unwrap().blocks[0].statements;
        for _ in 0..size {
            statements.insert(0, assign(local("x"), E::Integer { value: 1 }));
        }
        let (program, work) =
            crate::instrumentation::measure_deterministic_work(|| body(&export, "locked-source"));
        assert!(leaves(&program).iter().any(
            |s| matches!(s, CStatement::Assign { source, .. } if source.lease_plan().is_some())
        ));
        measurements.push((size, work));
    }
    eprintln!("source scalar lease preparation: {measurements:?}");
    for pair in measurements.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{measurements:?}");
    }
}

#[test]
fn source_scalar_lease_unsigned_source_widths_preserve_updated_contents() {
    for (kind, value_type, pointer_type, initial_value, final_value) in [
        (
            "u8",
            CType::UInt8,
            CType::UInt8Pointer,
            CValue::UInt8(4.into()),
            CValue::UInt8(8.into()),
        ),
        (
            "u16",
            CType::UInt16,
            CType::UInt16Pointer,
            CValue::UInt16(4.into()),
            CValue::UInt16(8.into()),
        ),
        (
            "u32",
            CType::UInt32,
            CType::UInt32Pointer,
            CValue::UInt32(4.into()),
            CValue::UInt32(8.into()),
        ),
    ] {
        let source = serde_json::to_string(&export())
            .unwrap()
            .replace("\"i32\"", &format!("\"{kind}\""));
        let export = serde_json::from_str(&source).unwrap();
        let program = body(&export, "locked-source");
        let pointer = Pointer {
            block: "unsigned-source-scalar".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer.clone(),
            0.into(),
            value_type.byte_width().into(),
            1,
        ));
        let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        let support = resources.unique_owned_occurrence_for_fact(&fact).unwrap().0;
        let initial = CState::new()
            .with_resource_context(resources)
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), value_type.byte_width())
                    .store(pointer.clone(), initial_value),
            )
            .with_local("parent", CValue::typed_pointer(pointer, pointer_type));
        let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
            panic!("unsigned source return");
        };
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(final_value)
        );
        assert!(
            state
                .resources()
                .owned_fact_for_occurrence(support)
                .is_some()
        );
        assert!(matches!(
            read(&state, c_load(c_variable("child"))),
            CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
}
