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
            implements: None,
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

fn alias_export(count: usize) -> r::RustExport {
    let mut source = export();
    let mir = source.functions[0].mir.as_mut().unwrap();
    let mut statements = vec![mir.blocks[0].statements[0].clone()];
    let mut previous = "child".to_string();
    for index in 0..count {
        let next = format!("alias_{index}");
        mir.locals.push(place(&next, reference_type()));
        statements.push(assign(local(&next), local(&previous)));
        previous = next;
    }
    statements.push(assign(deref(&previous), E::Integer { value: 7 }));
    statements.push(assign(deref("parent"), E::Integer { value: 8 }));
    mir.blocks[0].statements = statements;
    source
}

// Match the production session's analysis of which pointer locals are private.
// Restore thread-local registries even when an assertion panics.
struct AliasLocalScope(BlockRegistriesState);
impl Drop for AliasLocalScope {
    fn drop(&mut self) {
        restore_block_registries(&self.0);
    }
}
fn alias_body(export: &r::RustExport) -> (CStatement, AliasLocalScope) {
    let scope = AliasLocalScope(capture_block_registries());
    let (functions, _) =
        crate::languages::rust::lowering::lower_with_identity(export, Some("locked-source"))
            .unwrap();
    let summary = crate::languages::c::address_taken::summarize_address_taken(functions.iter());
    set_never_address_taken_locals(summary.never_taken());
    (functions[0].to_kernel_function().body().clone(), scope)
}

#[test]
fn source_scalar_lease_alias_chain_shares_custody_and_expires_together() {
    let (program, _scope) = alias_body(&alias_export(3));
    let (initial, support) = initial();
    let (state, _, ending) = active(&initial, &program);
    let child = state.locals.get("child").unwrap();
    for name in ["alias_0", "alias_1", "alias_2"] {
        assert_eq!(state.locals.get(name), Some(child));
        assert_eq!(
            read(&state, c_load(c_variable(name))),
            CExpressionOutcome::Value(int32(4))
        );
    }
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
    let raw_parent = initial.locals.get("parent").unwrap().clone();
    let mut untagged_alias = state.clone();
    eval::sync_stack_local(&mut untagged_alias, "alias_2", &raw_parent);
    untagged_alias.locals.set("alias_2", raw_parent);
    // A still-live original child cannot substitute for missing custody on
    // the actual alias lvalue selected by the ending store.
    assert!(matches!(
        execute(&untagged_alias, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
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
    for name in ["child", "alias_0", "alias_1", "alias_2"] {
        assert!(matches!(
            read(&recovered, c_load(c_variable(name))),
            CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
        assert!(matches!(
            execute(&recovered, &c_store(c_variable(name), c_int32_literal(9))),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
    assert!(matches!(
        execute(&recovered, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
        panic!("alias source function return");
    };
    assert_eq!(
        read(&state, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(8))
    );
}

#[test]
fn source_scalar_lease_alias_survives_replacing_original_child() {
    let mut source = alias_export(1);
    source.functions[0]
        .parameters
        .push(place("other", reference_type()));
    source.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .insert(2, assign(local("child"), local("other")));
    let (program, _scope) = alias_body(&source);
    let (initial, _) = initial();
    let other = Pointer {
        block: "other-scalar".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = initial
        .memory
        .clone()
        .with_block(other.block.clone(), 4)
        .store(other.clone(), int32(2));
    let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        other.clone(),
        0.into(),
        1.into(),
        4,
    ));
    let resources = initial.resources().clone().unchecked_with_fact(fact);
    let initial = initial
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("other", CValue::typed_pointer(other, CType::Int32Pointer));
    let (state, _, ending) = active(&initial, &program);
    assert_ne!(state.locals.get("child"), state.locals.get("alias_0"));
    assert_eq!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(2))
    );
    assert!(matches!(
        read(&state, c_load(c_variable("parent"))),
        CExpressionOutcome::RuntimeError(_)
    ));
    let recovered = normal(execute(&state, &ending));
    assert_eq!(
        read(&recovered, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        read(&recovered, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(2))
    );
    assert!(matches!(
        read(&recovered, c_load(c_variable("alias_0"))),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_alias_later_use_prevents_early_parent_recovery() {
    let mut source = alias_export(1);
    let statements = &mut source.functions[0].mir.as_mut().unwrap().blocks[0].statements;
    statements.push(assign(deref("alias_0"), E::Integer { value: 9 }));
    let (program, _scope) = alias_body(&source);
    // The supplied MIR is deliberately illegal Rust: parent access occurs
    // before the alias's actual last store. The source plan must keep it leased.
    let (initial, _) = initial();
    let endings: Vec<_> = leaves(&program)
        .into_iter()
        .filter_map(|statement| match statement {
            CStatement::TypedStore { value, source, .. } if source.lease_plan().is_some() => {
                Some(value)
            }
            _ => None,
        })
        .collect();
    assert_eq!(endings, [c_int32_literal(9)]);
    assert!(matches!(
        execute(&initial, &program),
        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
}

fn read_export(aliases: usize) -> r::RustExport {
    let mut source = alias_export(aliases);
    let mir = source.functions[0].mir.as_mut().unwrap();
    let reference = if aliases == 0 {
        "child".into()
    } else {
        format!("alias_{}", aliases - 1)
    };
    let last = mir.blocks[0].statements.len() - 2;
    mir.blocks[0].statements[last] = assign(local("x"), deref(&reference));
    source
}
fn before_read(initial: &CState, body: &CStatement) -> (CState, CStatement) {
    let mut state = initial.clone();
    for statement in leaves(body) {
        if matches!(&statement, CStatement::Assign { name, .. } if name == "x") {
            return (state, statement);
        }
        state = normal(execute(&state, &statement));
    }
    panic!("read assignment missing");
}

#[test]
fn source_scalar_lease_read_ending_recovers_after_checked_cached_alias_read() {
    for aliases in [0, 2] {
        let (program, _scope) = alias_body(&read_export(aliases));
        let (initial, support) = initial();
        let (state, ending) = before_read(&initial, &program);
        assert!(state.has_local_scalar_references());
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
        let reference = if aliases == 0 {
            "child".into()
        } else {
            format!("alias_{}", aliases - 1)
        };
        for _ in 0..2 {
            assert_eq!(
                read(&state, c_load(c_variable(&reference))),
                CExpressionOutcome::Value(int32(4))
            );
        }
        let recovered = normal(execute(&state, &ending));
        assert!(!recovered.has_local_scalar_references());
        assert_eq!(
            read(&recovered, c_variable("x")),
            CExpressionOutcome::Value(int32(4))
        );
        assert_eq!(
            read(&recovered, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(4))
        );
        assert!(
            recovered
                .resources()
                .owned_fact_for_occurrence(support)
                .is_some()
        );
        for name in
            std::iter::once("child".to_string()).chain((0..aliases).map(|i| format!("alias_{i}")))
        {
            assert!(matches!(
                read(&recovered, c_load(c_variable(name))),
                CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
            ));
        }
        assert!(matches!(
            execute(&recovered, &ending),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
        let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
            panic!("read-ending function return");
        };
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(8))
        );
        assert_eq!(
            read(&state, c_variable("x")),
            CExpressionOutcome::Value(int32(4))
        );
    }
}

#[test]
fn source_scalar_lease_read_ending_requires_exact_operation_and_actual_custody() {
    let (program, _scope) = alias_body(&read_export(1));
    let (initial, _) = initial();
    let (state, ending) = before_read(&initial, &program);
    assert!(state.has_local_scalar_references());
    let mut altered = ending.clone();
    let CStatement::Assign { expression, .. } = &mut altered else {
        panic!();
    };
    *expression = c_int32_literal(4);
    assert!(matches!(
        execute(&state, &altered),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let CValue::Pointer(parent) = initial.locals.get("parent").unwrap() else {
        panic!();
    };
    let mut missing = initial
        .clone()
        .with_local("alias_0", CValue::Pointer(parent.clone()));
    // Keep an ordinary owner: the load itself can succeed, but no birth or
    // executed lease can be substituted with a matching source observation.
    missing = normal(execute(&missing, &c_declare("x", CType::Int32)));
    assert!(matches!(
        execute(&missing, &ending),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_read_ending_preserves_preceding_child_store() {
    let mut source = read_export(1);
    source.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .insert(2, assign(deref("child"), E::Integer { value: 7 }));
    let (program, _scope) = alias_body(&source);
    let (initial, _) = initial();
    let (state, ending) = before_read(&initial, &program);
    let recovered = normal(execute(&state, &ending));
    assert_eq!(
        read(&recovered, c_variable("x")),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        read(&recovered, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(7))
    );
}

#[test]
fn source_scalar_lease_read_ending_role_and_success_are_semantic() {
    let (program, _scope) = alias_body(&read_export(1));
    let (initial, _) = initial();
    let (state, ending) = before_read(&initial, &program);
    let birth_source = leaves(&program)
        .into_iter()
        .find_map(|s| match s {
            CStatement::Assign { source, .. }
                if source.lease_plan().is_some() && !source.is_lease_read_end() =>
            {
                Some(source)
            }
            _ => None,
        })
        .unwrap();
    let mut wrong_role = ending.clone();
    let CStatement::Assign { source, .. } = &mut wrong_role else {
        panic!();
    };
    *source = birth_source;
    assert_ne!(ending, wrong_role);
    assert!(matches!(
        execute(&state, &wrong_role),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let mut observation_only = ending.clone();
    let CStatement::Assign { source, .. } = &mut observation_only else {
        panic!();
    };
    *source = CStatementAssignSource::default();
    assert_ne!(ending, observation_only);
    let still_active = normal(execute(&state, &observation_only));
    assert!(still_active.has_local_scalar_references());
    assert!(matches!(
        execute(&still_active, &c_return(c_void_value())),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let mut constant_destination = state.clone();
    constant_destination.locals.set_typed_with_all_qualifiers(
        "x",
        int32(0),
        CType::Int32,
        false,
        false,
        true,
        false,
    );
    eval::sync_stack_local(&mut constant_destination, "x", &int32(0));
    assert!(matches!(
        execute(&constant_destination, &ending),
        CStatementOutcome::RuntimeError(_) | CStatementOutcome::UndefinedBehavior(_)
    ));
    assert!(constant_destination.has_local_scalar_references());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/source_loans/tests.rs");
}
