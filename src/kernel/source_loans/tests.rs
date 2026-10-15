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

fn alias_body(export: &r::RustExport) -> (CStatement, AliasLocalScope) {
    let scope = AliasLocalScope(capture_block_registries());
    let (functions, _) =
        crate::languages::rust::lowering::lower_with_identity(export, Some("locked-source"))
            .unwrap();
    let summary = crate::languages::c::address_taken::summarize_address_taken(functions.iter());
    set_never_address_taken_locals(summary.never_taken());
    (functions[0].to_kernel_function().body().clone(), scope)
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

struct AliasLocalScope(BlockRegistriesState);
impl Drop for AliasLocalScope {
    fn drop(&mut self) {
        restore_block_registries(&self.0);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/source_loans/tests.rs");
}

fn boundary(initial: &CState, program: &CStatement) -> (CState, CStatement) {
    let mut state = initial.clone();
    for statement in leaves(program) {
        if matches!(statement, CStatement::EndScalarReference(_)) {
            return (state, statement);
        }
        state = normal(execute(&state, &statement));
    }
    panic!("explicit borrow end missing");
}
fn ends(program: &CStatement) -> Vec<CStatement> {
    leaves(program)
        .into_iter()
        .filter(|s| matches!(s, CStatement::EndScalarReference(_)))
        .collect()
}
fn nested_export(depth: usize) -> r::RustExport {
    assert!(depth > 0);
    let mut source = export();
    let mir = source.functions[0].mir.as_mut().unwrap();
    let mut statements = vec![mir.blocks[0].statements[0].clone()];
    let mut previous = "child".to_string();
    for index in 1..depth {
        let next = format!("nested_{index}");
        mir.locals.push(place(&next, reference_type()));
        statements.push(assign(
            local(&next),
            E::Borrow {
                place: Box::new(deref(&previous)),
                value_type: reference_type(),
            },
        ));
        previous = next;
    }
    statements.push(assign(deref(&previous), E::Integer { value: 7 }));
    statements.push(assign(deref("parent"), E::Integer { value: 8 }));
    mir.blocks[0].statements = statements;
    source
}

#[test]
fn source_scalar_lease_explicit_ends_preserve_store_read_and_alias_behavior() {
    for (source, expected) in [
        (export(), 7),
        (alias_export(3), 7),
        (read_export(0), 4),
        (read_export(2), 4),
    ] {
        let (program, _scope) = alias_body(&source);
        assert_eq!(ends(&program).len(), 1);
        let (initial, support) = initial();
        let (active, end) = boundary(&initial, &program);
        assert!(active.has_local_scalar_references());
        assert!(
            active
                .resources()
                .owned_fact_for_occurrence(support)
                .is_none()
        );
        assert!(matches!(
            read(&active, c_load(c_variable("parent"))),
            CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
        ));
        assert!(matches!(
            execute(&active, &c_store(c_variable("parent"), c_int32_literal(9))),
            CStatementOutcome::RuntimeError(_)
        ));
        for _ in 0..2 {
            assert_eq!(
                read(&active, c_load(c_variable("child"))),
                CExpressionOutcome::Value(int32(expected))
            );
        }
        let recovered = normal(execute(&active, &end));
        assert!(!recovered.has_local_scalar_references());
        assert!(
            recovered
                .resources()
                .owned_fact_for_occurrence(support)
                .is_some()
        );
        assert_eq!(
            read(&recovered, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(expected))
        );
        for slot in &source.functions[0].mir.as_ref().unwrap().locals {
            if matches!(slot.value_type, Type::Reference { .. }) {
                assert!(matches!(
                    read(&recovered, c_load(c_variable(&slot.name))),
                    CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
                ));
                assert!(matches!(
                    execute(
                        &recovered,
                        &c_store(c_variable(&slot.name), c_int32_literal(9))
                    ),
                    CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
                ));
            }
        }
        assert!(matches!(
            execute(&recovered, &end),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
        assert!(recovered.loan_ledger().unwrap().invariant_holds());
        let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
            panic!("source return");
        };
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(8))
        );
    }
}

#[test]
fn source_scalar_lease_explicit_nested_shared_frontiers_end_innermost_first() {
    for depth in [2, 3, 8] {
        let (program, _scope) = alias_body(&nested_export(depth));
        let endings = ends(&program);
        assert_eq!(endings.len(), depth);
        let (initial, support) = initial();
        let (mut state, _) = boundary(&initial, &program);
        assert!(matches!(
            execute(&state, endings.last().unwrap()),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
        for (index, end) in endings.iter().enumerate() {
            state = normal(execute(&state, end));
            assert!(state.loan_ledger().unwrap().invariant_holds());
            assert_eq!(
                state
                    .resources()
                    .owned_fact_for_occurrence(support)
                    .is_some(),
                index + 1 == depth
            );
        }
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(7))
        );
        assert!(!state.has_local_scalar_references());
        let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
            panic!("nested return");
        };
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(8))
        );
    }
}

#[test]
fn source_scalar_lease_explicit_end_uses_live_handle_after_alias_replacement() {
    let mut source = alias_export(1);
    source.functions[0]
        .parameters
        .push(place("other", reference_type()));
    source.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .insert(2, assign(local("child"), local("other")));
    let (program, _scope) = alias_body(&source);
    let (initial, support) = initial();
    let other = Pointer {
        block: "other-scalar".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = initial
        .resources()
        .clone()
        .unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(other.clone(), 0.into(), 1.into(), 4),
        ));
    let memory = initial
        .memory
        .clone()
        .with_block(other.block.clone(), 4)
        .store(other.clone(), int32(2));
    let initial = initial
        .with_resource_context(resources)
        .with_memory(memory)
        .with_local("other", CValue::typed_pointer(other, CType::Int32Pointer));
    let (state, end) = boundary(&initial, &program);
    assert_eq!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(2))
    );
    let state = normal(execute(&state, &end));
    assert!(
        state
            .resources()
            .owned_fact_for_occurrence(support)
            .is_some()
    );
    assert_eq!(
        read(&state, c_load(c_variable("parent"))),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        read(&state, c_load(c_variable("child"))),
        CExpressionOutcome::Value(int32(2))
    );
    assert!(matches!(
        read(&state, c_load(c_variable("alias_0"))),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_explicit_end_refuses_missing_foreign_and_duplicate_handles() {
    let (program, _scope) = alias_body(&export());
    let (initial, _) = initial();
    let (state, end) = boundary(&initial, &program);
    assert!(matches!(
        execute(&initial, &end),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let other = body(&export(), "different-locked-import");
    assert_ne!(end, ends(&other)[0]);
    assert!(matches!(
        execute(&state, &ends(&other)[0]),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let holder = state.loan_ledger().unwrap().fresh_participant().unwrap();
    let wrong = state.clone().with_loan_participant(Some(holder));
    assert!(matches!(
        execute(&wrong, &end),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let recovered = normal(execute(&state, &end));
    assert!(matches!(
        execute(&recovered, &end),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_explicit_operations_are_semantic_and_observations_are_inert() {
    let (program, _scope) = alias_body(&export());
    let (initial, _) = initial();
    let statements = leaves(&program);
    let mut without_ends = c_skip();
    let mut without_birth = c_skip();
    for statement in statements {
        if !matches!(statement, CStatement::EndScalarReference(_)) {
            without_ends = c_seq(without_ends, statement.clone());
        }
        let mut bare = statement;
        if let CStatement::Assign { source, .. } = &mut bare
            && let Some(observer) = source.as_ref()
        {
            *source = CStatementAssignSource::new(observer.clone());
        }
        without_birth = c_seq(without_birth, bare);
    }
    assert_ne!(program, without_ends);
    assert_ne!(program, without_birth);
    assert!(matches!(
        execute(&initial, &without_ends),
        CStatementOutcome::RuntimeError(_)
    ));
    assert!(matches!(
        execute(&initial, &without_birth),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let birth = leaves(&program)
        .into_iter()
        .find(|s| matches!(s,CStatement::Assign{source,..} if source.lease_plan().is_some()))
        .unwrap();
    let mut altered = birth;
    let CStatement::Assign { expression, .. } = &mut altered else {
        panic!()
    };
    *expression = c_variable("parent");
    assert!(matches!(
        execute(&initial, &altered),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn source_scalar_lease_explicit_end_is_not_executed_after_failed_read_assignment() {
    let (program, _scope) = alias_body(&read_export(1));
    let (initial, _) = initial();
    let mut state = initial;
    let statements = leaves(&program);
    let point = statements
        .iter()
        .position(|s| matches!(s,CStatement::Assign{name,..} if name=="x"))
        .unwrap();
    for statement in &statements[..point] {
        state = normal(execute(&state, statement));
    }
    state.locals.set_typed_with_all_qualifiers(
        "x",
        int32(0),
        CType::Int32,
        false,
        false,
        true,
        false,
    );
    eval::sync_stack_local(&mut state, "x", &int32(0));
    let tail = statements[point..].iter().cloned().fold(c_skip(), c_seq);
    assert!(matches!(
        execute(&state, &tail),
        CStatementOutcome::RuntimeError(_) | CStatementOutcome::UndefinedBehavior(_)
    ));
    assert!(state.has_local_scalar_references());
}

#[test]
fn source_scalar_lease_explicit_ending_follows_late_alias_use() {
    let mut source = alias_export(1);
    source.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .push(assign(deref("alias_0"), E::Integer { value: 9 }));
    let (program, _scope) = alias_body(&source);
    let (initial, _) = initial();
    assert!(matches!(
        execute(&initial, &program),
        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
}

#[test]
fn source_scalar_lease_explicit_declared_local_and_current_child_writes_survive_recovery() {
    let mut initial = normal(execute(&CState::new(), &c_declare("number", CType::Int32)));
    initial = normal(execute(&initial, &c_assign("number", c_int32_literal(4))));
    let pointer = initial.locals.slot("number").unwrap().clone();
    let initial = initial.with_local(
        "parent",
        CValue::typed_pointer(pointer, CType::Int32Pointer),
    );
    let mut source = read_export(1);
    source.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .insert(2, assign(deref("child"), E::Integer { value: 7 }));
    let (program, _scope) = alias_body(&source);
    let (state, end) = boundary(&initial, &program);
    assert!(matches!(
        read(&state, c_variable("number")),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    let recovered = normal(execute(&state, &end));
    assert_eq!(
        read(&recovered, c_variable("number")),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        read(&recovered, c_variable("x")),
        CExpressionOutcome::Value(int32(7))
    );
}

#[test]
fn source_scalar_lease_explicit_unsigned_widths_preserve_current_values() {
    for (kind, value_type, pointer_type, start, finish) in [
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
        for source in [alias_export(1), read_export(1)] {
            let json = serde_json::to_string(&source)
                .unwrap()
                .replace("\"i32\"", &format!("\"{kind}\""));
            let source = serde_json::from_str(&json).unwrap();
            let (program, _scope) = alias_body(&source);
            let pointer = Pointer {
                block: "unsigned-scalar".into(),
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
                .with_memory(
                    CMemory::new()
                        .with_block(pointer.block.clone(), value_type.byte_width())
                        .store(pointer.clone(), start.clone()),
                )
                .with_resource_context(resources)
                .with_local("parent", CValue::typed_pointer(pointer, pointer_type));
            let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
                panic!("unsigned return")
            };
            assert_eq!(
                read(&state, c_load(c_variable("parent"))),
                CExpressionOutcome::Value(finish.clone())
            );
            assert!(
                state
                    .resources()
                    .owned_fact_for_occurrence(support)
                    .is_some()
            );
            assert!(matches!(
                read(&state, c_load(c_variable("alias_0"))),
                CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
            ));
        }
    }
}

#[test]
fn source_scalar_lease_explicit_end_handles_scalar_expressions_and_unused_children() {
    let mut expression = read_export(1);
    expression.functions[0].mir.as_mut().unwrap().blocks[0].statements[2] = assign(
        local("x"),
        E::Binary {
            operator: "add".into(),
            left_type: Type::I32,
            right_type: Type::I32,
            left: Box::new(deref("alias_0")),
            right: Box::new(E::Integer { value: 1 }),
        },
    );
    let mut unused = alias_export(1);
    unused.functions[0].mir.as_mut().unwrap().blocks[0]
        .statements
        .remove(2);
    for source in [expression, unused] {
        let (program, _scope) = alias_body(&source);
        let (initial, _) = initial();
        assert_eq!(ends(&program).len(), 1);
        let CStatementOutcome::Return { state, .. } = execute(&initial, &program) else {
            panic!("source return")
        };
        assert_eq!(
            read(&state, c_load(c_variable("parent"))),
            CExpressionOutcome::Value(int32(8))
        );
        assert!(!state.has_local_scalar_references());
    }
}
