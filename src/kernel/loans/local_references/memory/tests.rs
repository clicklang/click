use super::*;
use crate::kernel::eval::{evaluate_c_expression_paths, execute_c_statement_paths};
use crate::kernel::*;

fn pointer(index: usize) -> Pointer {
    Pointer {
        block: format!("scalar-lease-{index}").into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn owned(index: usize) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        pointer(index),
        0.into(),
        1.into(),
        4,
    ))
}
fn fixture(size: usize) -> (CState, CPointerValue, ResourceOccurrenceId) {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let mut memory = CMemory::new();
    let mut resources = ResourceContext::new();
    for index in 0..size {
        memory = memory
            .with_block(pointer(index).block, 4)
            .store(pointer(index), int32(index as u32));
        resources = resources.unchecked_with_fact(owned(index));
    }
    let support = resources
        .unique_owned_occurrence_for_fact(&owned(0))
        .unwrap()
        .0;
    (
        CState::new()
            .with_memory(memory)
            .with_resource_context(resources)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(holder)),
        CPointerValue::new(pointer(0), CType::Int32Pointer),
        support,
    )
}
fn begin(
    state: &CState,
    parent: &CPointerValue,
    support: Option<ResourceOccurrenceId>,
) -> (CState, CPointerValue) {
    state
        .begin_local_scalar_reference(parent, support, CType::Int32, &PureFactContext::new())
        .unwrap()
}
fn read(state: &CState, pointer: &CPointerValue) -> CExpressionOutcome {
    read_assuming(
        state,
        c_load(CExpression::Value(CValue::Pointer(pointer.clone()))),
        &PureFactContext::new(),
    )
}
fn read_assuming(
    state: &CState,
    expression: CExpression,
    assumptions: &PureFactContext,
) -> CExpressionOutcome {
    let mut paths =
        evaluate_c_expression_paths(state, &expression, assumptions, &mut ExecutionBudget::new())
            .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}
fn statement(state: &CState, statement: CStatement) -> CStatementOutcome {
    let environment = CExecutionEnvironment::default();
    let mut paths = execute_c_statement_paths(
        state,
        &statement,
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}
fn store(state: &CState, pointer: &CPointerValue, value: u32) -> CStatementOutcome {
    statement(
        state,
        c_store(
            CExpression::Value(CValue::Pointer(pointer.clone())),
            c_int32_literal(value),
        ),
    )
}
fn normal(outcome: CStatementOutcome) -> CState {
    match outcome {
        CStatementOutcome::Normal(state) => *state,
        other => panic!("expected normal: {other:?}"),
    }
}

#[test]
fn scalar_lease_memory_execution_suspends_parent_and_preserves_child_writes() {
    let (state, parent, support) = fixture(2);
    let (active, child) = begin(&state, &parent, Some(support));
    assert!(
        active
            .resources()
            .owned_fact_for_occurrence(support)
            .is_none()
    );
    assert!(matches!(
        read(&active, &parent),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    assert!(matches!(
        store(&active, &parent, 99),
        CStatementOutcome::RuntimeError(_)
    ));
    assert_eq!(read(&active, &child), CExpressionOutcome::Value(int32(0)));
    let updated = normal(store(&active, &child, 7));
    assert!(
        updated
            .resources()
            .unique_owned_occurrence_for_fact(&owned(0))
            .is_none()
    );
    assert_eq!(read(&updated, &child), CExpressionOutcome::Value(int32(7)));
    let neighbor = CPointerValue::new(pointer(1), CType::Int32Pointer);
    let updated = normal(store(&updated, &neighbor, 42));
    let recovered = updated
        .end_local_scalar_reference(&child, &PureFactContext::new())
        .unwrap();
    assert_eq!(
        read(&recovered, &parent),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        read(&recovered, &neighbor),
        CExpressionOutcome::Value(int32(42))
    );
    assert!(
        recovered
            .resources()
            .unique_owned_occurrence_for_fact(&owned(0))
            .is_some()
    );
    assert!(!recovered.has_local_scalar_references());
    assert_eq!(
        recovered
            .end_local_scalar_reference(&child, &PureFactContext::new())
            .unwrap_err(),
        LoanRefusal::AlreadyRecovered
    );
    assert!(recovered.loan_ledger().unwrap().invariant_holds());
}

#[test]
fn scalar_lease_local_copies_and_identity_casts_remain_expired_after_recovery() {
    let (state, parent, support) = fixture(1);
    let (active, child) = begin(&state, &parent, Some(support));
    let active = active
        .with_local("child", CValue::Pointer(child.clone()))
        .with_local("copy", CValue::Pointer(parent.clone()));
    assert!(matches!(
        statement(&active, c_assign("copy", c_variable("child"))),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let registries = crate::kernel::capture_block_registries();
    crate::kernel::set_never_address_taken_locals(BTreeSet::from([
        "child".to_owned(),
        "copy".to_owned(),
    ]));
    let copied = normal(statement(&active, c_assign("copy", c_variable("child"))));
    let CValue::Pointer(copy) = copied.locals.get("copy").unwrap() else {
        panic!("pointer copy");
    };
    assert_eq!(child, *copy);
    assert_ne!(child, parent); // Same address, different memory custody.
    let recovered = copied
        .end_local_scalar_reference(&child, &PureFactContext::new())
        .unwrap();
    assert!(matches!(
        read_assuming(
            &recovered,
            c_load(c_variable("copy")),
            &PureFactContext::new()
        ),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    for pointer in [
        copy.clone(),
        copy.clone()
            .with_type(CType::VoidPointer)
            .with_type(CType::Int32Pointer),
    ] {
        assert!(matches!(
            read(&recovered, &pointer),
            CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
        assert!(matches!(
            store(&recovered, &pointer, 9),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
    assert_eq!(
        read(&recovered, &parent),
        CExpressionOutcome::Value(int32(0))
    );
    crate::kernel::restore_block_registries(&registries);
}

#[test]
fn scalar_lease_nested_execution_requires_inner_ending_before_parent_reuse() {
    let (state, parent, support) = fixture(1);
    let (outer_state, outer) = begin(&state, &parent, Some(support));
    let (inner_state, inner) = begin(&outer_state, &outer, None);
    assert!(matches!(
        read(&inner_state, &outer),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    assert_eq!(
        inner_state
            .end_local_scalar_reference(&outer, &PureFactContext::new())
            .unwrap_err(),
        LoanRefusal::ActiveDependency
    );
    let updated = normal(store(&inner_state, &inner, 11));
    let outer_state = updated
        .end_local_scalar_reference(&inner, &PureFactContext::new())
        .unwrap();
    assert!(
        outer_state
            .resources()
            .unique_owned_occurrence_for_fact(&owned(0))
            .is_none()
    );
    assert_eq!(
        read(&outer_state, &outer),
        CExpressionOutcome::Value(int32(11))
    );
    assert!(matches!(
        read(&outer_state, &inner),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let recovered = outer_state
        .end_local_scalar_reference(&outer, &PureFactContext::new())
        .unwrap();
    assert_eq!(
        read(&recovered, &parent),
        CExpressionOutcome::Value(int32(11))
    );
}

#[test]
fn scalar_lease_rejects_wrong_holder_branch_address_and_type() {
    let (state, parent, support) = fixture(2);
    let (left, child) = begin(&state, &parent, Some(support));
    let (right, _) = begin(&state, &parent, Some(support));
    assert!(matches!(
        read(&right, &child),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let wrong_holder = left.clone().with_loan_participant(Some(
        left.loan_ledger().unwrap().fresh_participant().unwrap(),
    ));
    assert!(matches!(
        read(&wrong_holder, &child),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let wrong_address = child.clone().with_address(pointer(1));
    assert!(matches!(
        read(&left, &wrong_address),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let wrong_type = child.with_type(CType::UInt8Pointer);
    assert!(matches!(
        read(&left, &wrong_type),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn scalar_lease_address_of_dereference_preserves_custody_and_integer_escape_is_refused() {
    let (state, parent, support) = fixture(1);
    let (active, child) = begin(&state, &parent, Some(support));
    let expression = CExpression::AddressOf(Box::new(c_load(CExpression::Value(CValue::Pointer(
        child.clone(),
    )))));
    assert_eq!(
        read_assuming(&active, expression, &PureFactContext::new()),
        CExpressionOutcome::Value(CValue::Pointer(child.clone()))
    );
    assert_eq!(
        read_assuming(
            &active,
            c_equal(
                CExpression::Value(CValue::Pointer(parent)),
                CExpression::Value(CValue::Pointer(child.clone()))
            ),
            &PureFactContext::new()
        ),
        CExpressionOutcome::Value(int32(1))
    );
    let displaced = read_assuming(
        &active,
        c_pointer_offset_bytes(CExpression::Value(CValue::Pointer(child.clone())), 4),
        &PureFactContext::new(),
    );
    let CExpressionOutcome::Value(CValue::Pointer(displaced)) = displaced else {
        panic!("one-past pointer");
    };
    assert_eq!(
        displaced.local_reference().unwrap().id(),
        child.local_reference().unwrap().id()
    );
    assert!(matches!(
        read(&active, &displaced),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let converted = crate::kernel::eval::cast_c_value_to_type(
        CValue::Pointer(child),
        CType::UInt64,
        crate::kernel::prelude::IntegerConversion::Checked,
        &mut Vec::new(),
        &PureFactContext::new(),
    );
    assert!(matches!(converted, Err(CRuntimeError::LoanRefusal(_))));
}

#[test]
fn scalar_lease_contract_load_bypass_and_view_only_parent_do_not_restore_authority() {
    let (state, parent, support) = fixture(1);
    let state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(
            CResourceFact::view_memory(owned(0).memory_own_range().unwrap().clone()),
        ));
    let (active, _) = begin(&state, &parent, Some(support));
    let expression = c_load(CExpression::Value(CValue::Pointer(parent)));
    assert!(matches!(
        read_assuming(
            &active,
            expression,
            &PureFactContext::new().allow_symbolic_contract_loads()
        ),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
}

#[test]
fn scalar_lease_unsupported_boundaries_refuse_before_custody_can_escape() {
    let (state, parent, support) = fixture(1);
    let (active, child) = begin(&state, &parent, Some(support));
    for operation in [
        c_call("unmodeled", Vec::new()),
        c_while(c_int32_literal(0), Vec::new(), CStatement::Skip),
        CStatement::HeapFree {
            pointer: CExpression::Value(CValue::Pointer(child.clone())),
        },
    ] {
        assert!(matches!(
            statement(&active, operation),
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
    assert!(matches!(
        statement(&active, CStatement::Return(c_int32_literal(0))),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    assert_eq!(read(&active, &child), CExpressionOutcome::Value(int32(0)));
    assert!(
        active
            .resources()
            .unique_owned_occurrence_for_fact(&owned(0))
            .is_none()
    );
}

#[test]
fn scalar_lease_independent_roots_keep_untagged_reads_guarded_until_both_recover() {
    let (state, first, support) = fixture(2);
    let (active, first_child) = begin(&state, &first, Some(support));
    let second = CPointerValue::new(pointer(1), CType::Int32Pointer);
    let support = active
        .resources()
        .unique_owned_occurrence_for_fact(&owned(1))
        .unwrap()
        .0;
    let (active, second_child) = begin(&active, &second, Some(support));
    let recovered = active
        .end_local_scalar_reference(&first_child, &PureFactContext::new())
        .unwrap();
    assert!(recovered.has_local_scalar_references());
    assert!(matches!(
        read(&recovered, &second),
        CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
    ));
    assert_eq!(
        read(&recovered, &first),
        CExpressionOutcome::Value(int32(0))
    );
    let recovered = recovered
        .end_local_scalar_reference(&second_child, &PureFactContext::new())
        .unwrap();
    assert!(!recovered.has_local_scalar_references());
    assert!(recovered.loan_ledger().unwrap().invariant_holds());
}

#[test]
fn scalar_lease_fresh_borrow_never_revives_an_old_child() {
    let (state, parent, support) = fixture(1);
    let (active, old_child) = begin(&state, &parent, Some(support));
    let recovered = active
        .end_local_scalar_reference(&old_child, &PureFactContext::new())
        .unwrap();
    let support = recovered
        .resources()
        .unique_owned_occurrence_for_fact(&owned(0))
        .unwrap()
        .0;
    let (active, new_child) = begin(&recovered, &parent, Some(support));
    assert_ne!(old_child, new_child);
    assert!(matches!(
        read(&active, &old_child),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    assert_eq!(
        read(&active, &new_child),
        CExpressionOutcome::Value(int32(0))
    );
    let recovered = active
        .end_local_scalar_reference(&new_child, &PureFactContext::new())
        .unwrap();
    assert!(matches!(
        store(&recovered, &old_child, 9),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
}

#[test]
fn scalar_lease_refuses_pointer_storage_and_duplicate_owner_recovery() {
    let (state, parent, support) = fixture(2);
    let (active, child) = begin(&state, &parent, Some(support));
    let operation = CStatement::TypedStore {
        access_class: None,
        pointer: CExpression::Value(CValue::typed_pointer(
            pointer(1),
            CType::Int32PointerPointer,
        )),
        value: CExpression::Value(CValue::Pointer(child.clone())),
        value_type: CType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    assert!(matches!(
        statement(&active, operation),
        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    let forged = active
        .clone()
        .with_resource_context(active.resources().clone().unchecked_with_fact(owned(0)));
    assert_eq!(
        forged
            .end_local_scalar_reference(&child, &PureFactContext::new())
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    assert!(matches!(
        read(&forged, &child),
        CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
    ));
    assert_eq!(read(&active, &child), CExpressionOutcome::Value(int32(0)));
}

#[test]
fn scalar_lease_supported_unsigned_widths_execute_and_recover_current_contents() {
    for (value_type, pointer_type, initial, replacement) in [
        (
            CType::UInt8,
            CType::UInt8Pointer,
            CValue::UInt8(1.into()),
            CValue::UInt8(7.into()),
        ),
        (
            CType::UInt16,
            CType::UInt16Pointer,
            CValue::UInt16(1.into()),
            CValue::UInt16(7.into()),
        ),
        (
            CType::UInt32,
            CType::UInt32Pointer,
            CValue::UInt32(1.into()),
            CValue::UInt32(7.into()),
        ),
    ] {
        let ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer(0),
            0.into(),
            1.into(),
            value_type.byte_width(),
        ));
        let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        let support = resources.unique_owned_occurrence_for_fact(&fact).unwrap().0;
        let state = CState::new()
            .with_resource_context(resources)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(holder))
            .with_memory(
                CMemory::new()
                    .with_block(pointer(0).block, value_type.byte_width())
                    .store(pointer(0), initial),
            );
        let parent = CPointerValue::new(pointer(0), pointer_type);
        let (active, child) = state
            .begin_local_scalar_reference(
                &parent,
                Some(support),
                value_type,
                &PureFactContext::new(),
            )
            .unwrap();
        let updated = normal(statement(
            &active,
            CStatement::TypedStore {
                access_class: None,
                pointer: CExpression::Value(CValue::Pointer(child.clone())),
                value: CExpression::Value(replacement.clone()),
                value_type,
                volatile: false,
                pointee_constant: false,
                source: Default::default(),
            },
        ));
        assert_eq!(
            read(&updated, &child),
            CExpressionOutcome::Value(replacement.clone())
        );
        let recovered = updated
            .end_local_scalar_reference(&child, &PureFactContext::new())
            .unwrap();
        assert_eq!(
            read(&recovered, &parent),
            CExpressionOutcome::Value(replacement)
        );
        assert!(matches!(
            read(&recovered, &child),
            CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/loans/local_references/memory/tests.rs");
}
