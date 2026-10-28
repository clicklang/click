use super::*;

fn free_once(state: &CState, name: &str, facts: &PureFactContext) -> CStatementOutcome {
    let mut paths = execute_c_statement_paths(
        state,
        &c_heap_free(c_variable(name)),
        facts,
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}

fn owned_base(base: &Pointer) -> ResourceContext {
    ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(base.clone(), 4))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            0.into(),
            1.into(),
        )))
}

#[test]
fn free_uses_the_owned_base_and_retires_every_proven_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(973_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(973_001));
    let facts = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(
            CPointerValue::new(alias.clone(), CType::Int32Pointer),
            CPointerValue::new(base.clone(), CType::Int32Pointer),
        ),
        true,
    ));
    for registered in [false, true] {
        let mut memory = CMemory::new().store(alias.clone(), int32(7));
        if registered {
            memory = memory.with_heap_allocation_claim(base.clone(), 4).unwrap();
        }
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(owned_base(&base))
            .with_local("q", CValue::pointer(alias.clone()))
            .with_local("p", CValue::pointer(base.clone()));
        let CStatementOutcome::Normal(after) = free_once(&state, "q", &facts) else {
            panic!("a proven base alias must free (registered={registered})");
        };
        assert!(after.resources().facts().is_empty());
        assert!(after.memory().live_heap_block_size(&base).is_none());
        assert!(after.memory().is_deallocated_heap_address(&base, &facts));
        assert!(after.memory().is_deallocated_heap_address(&alias, &facts));
        assert_eq!(
            after.memory().load(&alias),
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        );
        for name in ["p", "q"] {
            assert!(matches!(
                free_once(&after, name, &facts),
                CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                    CInvalidFree::DoubleFree
                ))
            ));
        }
    }
}

#[test]
fn free_does_not_treat_an_unproved_or_interior_alias_as_a_base() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(973_010),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(973_011));
    let state = CState::new()
        .with_resource_context(owned_base(&base))
        .with_local("q", CValue::pointer(alias.clone()));
    let none = PureFactContext::new();
    let interior = none.clone().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), base.offset_by_bytes(2)),
        true,
    ));
    let numeric_only = none.clone().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias, base),
        true,
    ));
    for facts in [&none, &interior, &numeric_only] {
        assert!(matches!(
            free_once(&state, "q", facts),
            CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(_))
        ));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/tests/heap_tests/free_base_alias_tests.rs");
}

#[test]
fn free_alias_cannot_bypass_an_unresolved_reallocation() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(973_020),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(973_021));
    let pending = Pointer::symbolic(Variable(973_022));
    let facts = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(
            CPointerValue::new(alias.clone(), CType::Int32Pointer),
            CPointerValue::new(base.clone(), CType::Int32Pointer),
        ),
        true,
    ));
    let memory = CMemory::new()
        .with_heap_allocation_claim(base.clone(), 4)
        .unwrap()
        .with_pending_heap_reallocation(pending, base.clone(), 4.into(), None, vec![], vec![]);
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(owned_base(&base))
        .with_local("q", CValue::pointer(alias));
    assert!(matches!(
        free_once(&state, "q", &facts),
        CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
    ));
}
