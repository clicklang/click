use super::*;

fn free_once(state: &ExecutionState, name: &str, facts: &PureFactContext) -> StatementOutcome {
    let mut paths = execute_execution_statement_paths(
        state,
        &program_heap_free(crate::kernel::program_expression::variable(name)),
        facts,
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap().outcome
}

fn owned_base(base: &Pointer) -> ResourceContext {
    ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(base.clone(), 4))
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
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
            PointerValue::new(alias.clone(), ProgramType::Int32Pointer),
            PointerValue::new(base.clone(), ProgramType::Int32Pointer),
        ),
        true,
    ));
    for registered in [false, true] {
        let mut memory = Memory::new().store(alias.clone(), int32(7));
        if registered {
            memory = memory
                .with_heap_allocation_claim(base.clone(), HeapExtent::int32(4))
                .unwrap();
        }
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(owned_base(&base))
            .with_local("q", ProgramValue::pointer(alias.clone()))
            .with_local("p", ProgramValue::pointer(base.clone()));
        let StatementOutcome::Normal(after) = free_once(&state, "q", &facts) else {
            panic!("a proven base alias must free (registered={registered})");
        };
        assert!(after.resources().facts().is_empty());
        assert!(after.memory().live_heap_block_extent(&base).is_none());
        assert!(after.memory().is_deallocated_heap_address(&base, &facts));
        assert!(after.memory().is_deallocated_heap_address(&alias, &facts));
        assert_eq!(
            after.memory().load(&alias),
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        );
        for name in ["p", "q"] {
            assert!(matches!(
                free_once(&after, name, &facts),
                StatementOutcome::RuntimeError(RuntimeError::InvalidFree(InvalidFree::DoubleFree))
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
    let state = ExecutionState::new()
        .with_resource_context(owned_base(&base))
        .with_local("q", ProgramValue::pointer(alias.clone()));
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
            StatementOutcome::RuntimeError(RuntimeError::InvalidFree(_))
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
            PointerValue::new(alias.clone(), ProgramType::Int32Pointer),
            PointerValue::new(base.clone(), ProgramType::Int32Pointer),
        ),
        true,
    ));
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(4))
        .unwrap()
        .with_pending_heap_reallocation(
            pending,
            base.clone(),
            HeapExtent::int32(4),
            None,
            vec![],
            vec![],
        );
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(owned_base(&base))
        .with_local("q", ProgramValue::pointer(alias));
    assert!(matches!(
        free_once(&state, "q", &facts),
        StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome)
    ));
}
