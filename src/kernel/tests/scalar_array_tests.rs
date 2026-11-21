//! Compact scalar arrays keep checked authority independent of logical length.
use super::*;

fn pointer(block: &str, offset: i64) -> Address {
    Address {
        base: block.into(),
        offset: AddressOffset::Constant(offset),
    }
}
fn fresh(count: u32) -> SymbolicMemory {
    SymbolicMemory::new()
        .with_block("local:array-source", count * 4)
        .with_block("local:array-target", count * 4)
}
fn seeded(count: u32) -> SymbolicMemory {
    fresh(count)
        .initialize_scalar_array(
            &pointer("local:array-source", 0),
            ProgramType::UInt32,
            count,
            ProgramValue::UInt32(MachineTerm::Variable(Variable(912_345))),
            false,
        )
        .unwrap()
}

#[test]
fn scalar_array_copy_after_partial_call_keeps_known_lanes_and_rejects_bad_storage() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    let range = MemoryRange::new_with_element_width(source.clone(), 4u32.into(), 12u32.into(), 1);
    let after_call = seeded(4).with_call_memory_havoc(
        Variable(912_348),
        std::slice::from_ref(&range),
        &PureFactContext::new(),
        None,
    );
    let copied = after_call
        .clone()
        .initialize_scalar_array(
            &target,
            ProgramType::UInt32,
            4,
            ProgramValue::pointer(source.clone()),
            true,
        )
        .unwrap();
    assert_eq!(
        copied.load(&target),
        ExpressionOutcome::Value(ProgramValue::UInt32(MachineTerm::Variable(Variable(
            912_345
        )),))
    );
    assert_ne!(
        copied.load(&pointer("local:array-target", 4)),
        copied.load(&target)
    );
    for invalid in [
        fresh(4)
            .store(source.clone(), ProgramValue::UInt32(7u32.into()))
            .with_call_memory_havoc(Variable(912_349), &[range], &PureFactContext::new(), None),
        after_call
            .clone()
            .store(source.clone(), ProgramValue::Int32(7u32.into())),
        after_call.store(pointer("local:array-source", 1), crate::kernel::uint8(7u32)),
    ] {
        assert!(
            invalid
                .initialize_scalar_array(
                    &target,
                    ProgramType::UInt32,
                    4,
                    ProgramValue::pointer(source.clone()),
                    true,
                )
                .is_err()
        );
    }
}

#[test]
fn compact_scalar_arrays_reject_uninitialized_and_partial_storage() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    assert!(
        fresh(4)
            .initialize_scalar_array(
                &target,
                ProgramType::UInt32,
                4,
                ProgramValue::pointer(source.clone()),
                true,
            )
            .is_err()
    );
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                ProgramType::UInt32,
                3,
                ProgramValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                ProgramType::Int32,
                4,
                ProgramValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    let initialized = seeded(4)
        .initialize_scalar_array(
            &target,
            ProgramType::UInt32,
            4,
            ProgramValue::pointer(source),
            true,
        )
        .unwrap();
    assert!(
        initialized
            .initialize_scalar_array(
                &target,
                ProgramType::UInt32,
                4,
                ProgramValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
    assert!(
        fresh(4)
            .initialize_scalar_array(
                &pointer("local:array-target", 4),
                ProgramType::UInt32,
                3,
                ProgramValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
}

#[test]
fn compact_scalar_array_operations_require_complete_read_and_write_authority() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    for copy in [false, true] {
        for complete in [false, true] {
            let mut resources = vec![own_memory_fact(
                target.clone(),
                0,
                if complete { 4 } else { 3 },
            )];
            if copy {
                resources.push(view_memory_fact(source.clone(), 0, 4));
            }
            let state = ExecutionState::new()
                .with_memory(if copy { seeded(4) } else { fresh(4) })
                .with_resource_context(ResourceContext::new().unchecked_with_facts(resources));
            let statement = program_initialize_scalar_array(
                crate::kernel::program_expression::pointer_value(target.clone()),
                if copy {
                    crate::kernel::program_expression::pointer_value(source.clone())
                } else {
                    crate::kernel::program_expression::uint32_literal(7)
                },
                ProgramType::UInt32,
                4,
                copy,
            );
            let theorem = prove_execution_statement_execution(state, statement).unwrap();
            let Proposition::ProgramStatementVerifies { outcome, .. } = theorem.proposition()
            else {
                panic!()
            };
            if complete {
                assert!(
                    matches!(outcome, StatementOutcome::Normal(_)),
                    "{outcome:?}"
                );
            } else {
                assert!(
                    matches!(
                        outcome,
                        StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. })
                    ),
                    "{outcome:?}"
                );
            }
        }
    }
    let state = ExecutionState::new()
        .with_memory(seeded(4))
        .with_resource_context(ResourceContext::new().unchecked_with_facts(vec![
            own_memory_fact(target.clone(), 0, 4),
            view_memory_fact(source.clone(), 0, 3),
        ]));
    let theorem = prove_execution_statement_execution(
        state,
        program_initialize_scalar_array(
            crate::kernel::program_expression::pointer_value(target),
            crate::kernel::program_expression::pointer_value(source),
            ProgramType::UInt32,
            4,
            true,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. }),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_zero_length_needs_no_byte_authority() {
    let state = ExecutionState::new().with_memory(fresh(0));
    let statement = program_seq(
        program_initialize_scalar_array(
            crate::kernel::program_expression::pointer_value(pointer("local:array-source", 0)),
            crate::kernel::program_expression::uint32_literal(7),
            ProgramType::UInt32,
            0,
            false,
        ),
        program_initialize_scalar_array(
            crate::kernel::program_expression::pointer_value(pointer("local:array-target", 0)),
            crate::kernel::program_expression::pointer_value(pointer("local:array-source", 0)),
            ProgramType::UInt32,
            0,
            true,
        ),
    );
    let theorem = prove_execution_statement_execution(state, statement).unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Normal(_),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_rejects_readonly_storage_and_pointer_qualifiers() {
    let target = pointer("local:array-target", 0);
    for readonly_block in [false, true] {
        let memory =
            SymbolicMemory::new().with_block_or_read_only(target.base.clone(), 16, readonly_block);
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(own_memory_context(target.clone(), 0, 4));
        let pointer = Pointer::new(target.clone(), ProgramType::UInt32Pointer)
            .with_pointee_constant(!readonly_block);
        let theorem = prove_execution_statement_execution(
            state,
            program_initialize_scalar_array(
                ProgramExpression::Value(ProgramValue::Pointer(pointer)),
                crate::kernel::program_expression::uint32_literal(7),
                ProgramType::UInt32,
                4,
                false,
            ),
        )
        .unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                ..
            }
        ));
    }
    let theorem = prove_execution_statement_execution(
        ExecutionState::new().with_memory(fresh(0)),
        program_initialize_scalar_array(
            crate::kernel::program_expression::pointer_value(target),
            program_void_value(),
            ProgramType::Void,
            0,
            false,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_cannot_bypass_an_active_view_borrow() {
    let target = pointer("local:array-target", 0);
    let viewed = view_memory_fact(target.clone(), 0, 4);
    let resources = ResourceContext::new()
        .unchecked_with_facts([own_memory_fact(target.clone(), 0, 4), viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::borrows::BorrowLedger::new();
    let participant = ledger.fresh_participant().unwrap();
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let bindings = crate::kernel::borrows::BorrowBindings::default().with_inserted(
        support,
        crate::kernel::borrows::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = ExecutionState::new()
        .with_memory(fresh(4))
        .with_resource_context(resources)
        .with_borrow_ledger(Some(ledger))
        .with_borrow_participant(Some(participant))
        .with_borrow_bindings(bindings);
    let statement = program_initialize_scalar_array(
        crate::kernel::program_expression::pointer_value(target),
        crate::kernel::program_expression::uint32_literal(7),
        ProgramType::UInt32,
        4,
        false,
    );
    let theorem = prove_execution_statement_execution(state, statement).unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::RuntimeError(RuntimeError::BorrowRefusal(_)),
            ..
        }
    ));
}

fn scalar_array_region_state() -> ExecutionState {
    ExecutionState::new()
        .with_memory(seeded(4))
        .with_resource_context(ResourceContext::new().unchecked_with_facts([
            own_memory_fact(pointer("local:array-source", 0), 0, 4),
            own_memory_fact(pointer("local:array-target", 0), 0, 4),
        ]))
}

fn execute_test_scalar_array_write(
    state: &ExecutionState,
    count: u32,
    copy: bool,
    assumptions: &PureFactContext,
) -> StatementExecutionPath {
    let value = if copy {
        crate::kernel::program_expression::pointer_value(pointer("local:array-source", 0))
    } else {
        crate::kernel::program_expression::uint32_literal(7)
    };
    let [path]: [StatementExecutionPath; 1] = execute_execution_statement_paths(
        state,
        &program_write_scalar_array_region(
            ProgramExpression::Value(ProgramValue::typed_pointer(
                pointer("local:array-target", 0),
                ProgramType::UInt32Pointer,
            )),
            value,
            ProgramType::UInt32,
            count,
            copy,
        ),
        assumptions,
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .try_into()
    .expect("one compact write path");
    path
}

#[test]
fn scalar_array_region_writes_require_separation_for_the_entire_destination() {
    use crate::kernel::borrows::BorrowLedger;

    let state = scalar_array_region_state();
    let assumptions = PureFactContext::new();
    for (block, separate) in [("local:array-target", false), ("local:array-source", true)] {
        // The borrow covers only the last element of the block.
        let range = MemoryRange::new(pointer(block, 12), 0u32.into(), 1u32.into());
        let backing = ResourceFact::own_memory(range.clone());
        let occurrence = ResourceContext::new()
            .unchecked_with_fact(backing.clone())
            .unique_owned_occurrence_for_fact(&backing)
            .unwrap()
            .0;
        let ledger = BorrowLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(lender, reader, occurrence, backing).unwrap();
        let state = state
            .clone()
            .with_borrow_ledger(Some(ledger.apply(&opening.transition).unwrap()));

        let borrowed = Resource::Memory(range);
        for copy in [true, false] {
            let write = execute_test_scalar_array_write(&state, 4, copy, &assumptions);
            let [obligation] = write.obligations.as_slice() else {
                panic!("expected one separation obligation for the entire write");
            };
            let Proposition::ResourceSeparate { left, right } = obligation.proposition() else {
                panic!("expected a borrow separation obligation");
            };
            let expected = MemoryRange::from_pointer_value(
                &Pointer::new(pointer("local:array-target", 0), ProgramType::UInt32Pointer),
                0u32.into(),
                4u32.into(),
                4,
            );
            assert_eq!(left.as_ref(), &Resource::Memory(expected));
            assert_eq!(right.as_ref(), &borrowed);
            assert_eq!(assumptions.proves_resource_separate(left, right), separate);
            let StatementOutcome::Normal(after) = write.outcome else {
                panic!("expected a write path conditional on separation");
            };
            let expected_value = if copy {
                state.memory().load(&pointer("local:array-source", 12))
            } else {
                ExpressionOutcome::Value(crate::kernel::uint32(7u32))
            };
            assert_eq!(
                after.memory().load(&pointer("local:array-target", 12)),
                expected_value,
            );

            let empty = execute_test_scalar_array_write(&state, 0, copy, &assumptions);
            assert!(empty.obligations.is_empty());
            let StatementOutcome::Normal(after_empty) = empty.outcome else {
                panic!("an empty region has no destination write");
            };
            assert_eq!(after_empty.memory(), state.memory());
        }
    }
}

#[test]
fn compact_array_regions_check_source_type_size_alignment_and_initialization() {
    let context = PureFactContext::new();
    let source = pointer("local:source", 4);
    let target = pointer("local:target", 4);
    let memory = SymbolicMemory::new()
        .with_block(source.base.clone(), 24)
        .with_block(target.base.clone(), 24)
        .write_scalar_array_region(
            &source,
            ProgramType::UInt32,
            4,
            ProgramValue::UInt32(7u32.into()),
            false,
            false,
            &context,
        )
        .unwrap();
    for (at, element, count) in [
        (target.clone(), ProgramType::Int32, 4),
        (pointer("local:target", 5), ProgramType::UInt32, 4),
        (
            pointer("local:target", i64::MAX - 3),
            ProgramType::UInt32,
            4,
        ),
        (target.clone(), ProgramType::UInt32, 6),
    ] {
        assert!(
            memory
                .clone()
                .write_scalar_array_region(
                    &at,
                    element,
                    count,
                    ProgramValue::pointer(source.clone()),
                    true,
                    false,
                    &context
                )
                .is_err()
        );
    }
    let changed = memory
        .clone()
        .store(source.clone(), ProgramValue::UInt32(9u32.into()));
    let copied = changed
        .write_scalar_array_region(
            &target,
            ProgramType::UInt32,
            4,
            ProgramValue::pointer(source.clone()),
            true,
            false,
            &context,
        )
        .unwrap();
    assert_eq!(
        copied.load(&target),
        ExpressionOutcome::Value(ProgramValue::UInt32(9u32.into()))
    );
    let fresh = SymbolicMemory::new()
        .with_block(source.base.clone(), 24)
        .with_block(target.base.clone(), 24);
    assert!(
        fresh
            .write_scalar_array_region(
                &target,
                ProgramType::UInt32,
                4,
                ProgramValue::pointer(source.clone()),
                true,
                false,
                &context
            )
            .is_err()
    );
    // Reading the old uniform value first makes overlapping/self copies states.
    let copied = memory
        .write_scalar_array_region(
            &pointer("local:source", 8),
            ProgramType::UInt32,
            3,
            ProgramValue::pointer(source),
            true,
            false,
            &context,
        )
        .unwrap();
    assert_eq!(
        copied.load(&pointer("local:source", 16)),
        ExpressionOutcome::Value(ProgramValue::UInt32(7u32.into()))
    );
}

#[test]
fn compact_array_region_execution_requires_full_authority_and_mutable_storage() {
    for (writable, complete, readonly) in [
        (true, true, false),
        (true, false, false),
        (false, true, false),
        (true, true, true),
    ] {
        let target = pointer("local:region", 4);
        let resource = if writable {
            own_memory_fact(target.clone(), 0, if complete { 4 } else { 3 })
        } else {
            view_memory_fact(target.clone(), 0, 4)
        };
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block_or_read_only(
                target.base.clone(),
                24,
                readonly,
            ))
            .with_resource_context(ResourceContext::new().unchecked_with_facts(vec![resource]));
        let statement = program_write_scalar_array_region(
            crate::kernel::program_expression::pointer_value(target),
            crate::kernel::program_expression::uint32_literal(7),
            ProgramType::UInt32,
            4,
            false,
        );
        let theorem = prove_execution_statement_execution(state, statement).unwrap();
        let Proposition::ProgramStatementVerifies { outcome, .. } = theorem.proposition() else {
            panic!()
        };
        assert_eq!(
            matches!(outcome, StatementOutcome::Normal(_)),
            writable && complete && !readonly
        );
    }
}

#[test]
fn compact_array_region_write_refreshes_an_addressed_scalar_local() {
    let declaration = prove_execution_statement_execution(
        ExecutionState::new(),
        program_seq(
            program_declare("value", ProgramType::UInt32),
            program_assign(
                "value",
                crate::kernel::program_expression::uint32_literal(42),
            ),
        ),
    )
    .unwrap();
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Normal(state),
        ..
    } = declaration.proposition()
    else {
        panic!("scalar declaration must execute");
    };
    let target = state.locals().slot("value").unwrap().clone();
    let state = state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_facts([own_memory_fact(target, 0, 1)]),
    );
    let theorem = prove_execution_statement_execution(
        state,
        program_write_scalar_array_region(
            crate::kernel::program_expression::addr_of("value"),
            crate::kernel::program_expression::uint32_literal(7),
            ProgramType::UInt32,
            1,
            false,
        ),
    )
    .unwrap();
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Normal(state),
        ..
    } = theorem.proposition()
    else {
        panic!("authorized region write must execute");
    };
    assert_eq!(
        state.locals().get_native("value").as_deref(),
        Some(&crate::kernel::uint32(7u32))
    );
}

#[test]
fn scalar_array_states_check_explicit_coverage_types_and_overlap() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    let mut memory = fresh(4);
    for index in 0..4 {
        memory = memory.store(
            pointer("local:array-source", index * 4),
            ProgramValue::UInt32((index as u32 + 1).into()),
        );
    }
    let copied = memory
        .clone()
        .initialize_scalar_array(
            &target,
            ProgramType::UInt32,
            4,
            ProgramValue::pointer(source.clone()),
            true,
        )
        .unwrap();
    for index in 0..4 {
        assert_eq!(
            copied.load(&pointer("local:array-target", index * 4)),
            ExpressionOutcome::Value(ProgramValue::UInt32((index as u32 + 1).into()))
        );
    }
    let overlap = memory
        .clone()
        .write_scalar_array_region(
            &pointer("local:array-source", 4),
            ProgramType::UInt32,
            3,
            ProgramValue::pointer(source.clone()),
            true,
            false,
            &PureFactContext::new(),
        )
        .unwrap();
    for index in 1..4 {
        assert_eq!(
            overlap.load(&pointer("local:array-source", index * 4)),
            ExpressionOutcome::Value(ProgramValue::UInt32((index as u32).into()))
        );
    }
    let wrong_type = memory.clone().store(
        pointer("local:array-source", 4),
        ProgramValue::Int32(2.into()),
    );
    let missing = fresh(4).store(source.clone(), ProgramValue::UInt32(1u32.into()));
    let misaligned = memory.store(pointer("local:array-source", 1), crate::kernel::uint8(3u32));
    for invalid in [wrong_type, missing, misaligned] {
        assert!(
            invalid
                .initialize_scalar_array(
                    &target,
                    ProgramType::UInt32,
                    4,
                    ProgramValue::pointer(source.clone()),
                    true
                )
                .is_err()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/scalar_array_tests.rs");
}
