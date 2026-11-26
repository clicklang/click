#[test]
fn aggregate_step_results_cost_their_fields_instead_of_unrelated_state() {
    for unrelated in [false, true] {
        let mut work_by_size = Vec::new();
        for size in [1, 16, 256] {
            let _session = VerificationSession::enter();
            let fields = if unrelated { 1 } else { size };
            let (mut state, source, layout) = fixture(fields);
            if unrelated {
                for i in 0..size {
                    let pointer = SymbolicMemory::local_pointer(format!("other{i}"));
                    state.set_memory(
                        state
                            .memory
                            .clone()
                            .with_block(pointer.base.clone(), 4)
                            .store(pointer, int32(i)),
                    );
                }
            }
            let mut budget = ExecutionBudget::for_new_execution();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let result = materialize(&state, &source, &layout, &mut budget);
                end_aggregate_step_lifetimes(&result, &[0]).unwrap();
            });
            work_by_size.push((size as usize, work));
        }
        if unrelated {
            assert!(
                work_by_size
                    .iter()
                    .all(|(_, work)| *work <= work_by_size[0].1 + 64),
                "{work_by_size:?}"
            );
        } else {
            let base = work_by_size[0].1;
            assert!(
                work_by_size
                    .iter()
                    .all(|(size, work)| *work <= base * size * 2),
                "{work_by_size:?}"
            );
        }
    }
}

#[test]
fn opaque_exception_creation_ignores_unrelated_memory_and_types() {
    let mut costs = Vec::new();
    for size in [1, 32, 1024] {
        let _session = VerificationSession::enter();
        let mut state = ExecutionState::new();
        for index in 0..size {
            TypeParameterName::intern(&format!("Unrelated{index}"));
            let pointer = SymbolicMemory::local_pointer(format!("other{index}"));
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.base.clone(), 4)
                    .store(pointer, int32(index)),
            );
        }
        let payload = TypeParameterName::intern("struct ParseError");
        let statement = ProgramStatement::ThrowOpaque(payload);
        let environment = ExecutionEnvironment::new();
        let assumptions = PureFactContext::default();
        let mut budget = ExecutionBudget::for_new_execution();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &assumptions,
                ExecutionContext::verify_loops(&environment),
                &mut budget,
            )
            .unwrap()
        });
        let StatementOutcome::Throw {
            value,
            state: thrown,
        } = &paths[0].outcome
        else {
            panic!("expected opaque throw");
        };
        assert_eq!(value.program_type(), ProgramType::Parameter(payload));
        assert_eq!(thrown.memory, state.memory);
        let next = execute_execution_statement_paths(
            &state,
            &statement,
            &assumptions,
            ExecutionContext::verify_loops(&environment),
            &mut budget,
        )
        .unwrap();
        let StatementOutcome::Throw { value: other, .. } = &next[0].outcome else {
            panic!("expected second throw");
        };
        assert_ne!(value, other, "each construction introduces a fresh value");
        costs.push(work);
    }
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

use crate::kernel::borrows::BorrowLedger;

#[test]
fn aggregate_copy_builds_one_borrow_obligation_without_visiting_aliases_or_borrows() {
    let _session = VerificationSession::enter();
    let (state, source, layout) = fixture(2);
    let target = SymbolicMemory::local_pointer("destination");
    let state = state.clone().with_memory(
        state
            .memory
            .clone()
            .with_block(target.base.clone(), layout.size_bytes()),
    );
    let target_expression = ProgramExpression::Value(ProgramValue::typed_pointer(
        target.clone(),
        ProgramType::UInt8Pointer,
    ));
    for grow_aliases in [true, false] {
        let mut work = Vec::new();
        for size in [4_u64, 16, 64] {
            let mut ledger = BorrowLedger::new();
            let lender = ledger.fresh_participant().unwrap();
            let borrower = ledger.fresh_participant().unwrap();
            let mut assumptions = PureFactContext::new();
            if grow_aliases {
                for i in 0..size {
                    assumptions = assumptions.assume_condition(
                        OldConditionTerm::address_equal(
                            target.clone(),
                            Address::symbolic(Variable(9_831_000 + i)),
                        ),
                        true,
                    );
                }
            }
            let mut last = None;
            for i in 0..if grow_aliases { 1 } else { size } {
                let owner = ResourceFact::own_memory(MemoryRange::new(
                    Address::symbolic(Variable(9_832_000 + i)),
                    0u32.into(),
                    1u32.into(),
                ));
                let support = ResourceContext::new()
                    .unchecked_with_fact(owner.clone())
                    .unique_owned_occurrence_for_fact(&owner)
                    .unwrap()
                    .0;
                let opening = ledger.lend(lender, borrower, support, owner).unwrap();
                ledger = ledger.apply(&opening.transition).unwrap();
                last = Some(opening);
            }
            let copy = |ledger: &BorrowLedger| {
                let state = state.clone().with_borrow_ledger(Some(ledger.clone()));
                let mut paths = execute_program_aggregate_copy_paths(
                    &state,
                    &target_expression,
                    &source,
                    &layout,
                    AggregateCopyDestination::Assignment,
                    &assumptions,
                    &mut ExecutionBudget::for_new_execution(),
                )
                .unwrap();
                assert_eq!(paths.len(), 1);
                paths.pop().unwrap()
            };
            let (path, units) =
                crate::instrumentation::measure_deterministic_work(|| copy(&ledger));
            assert!(
                matches!(path.outcome, StatementOutcome::Normal(_)),
                "{:?}",
                path.outcome
            );
            let [obligation] = path.obligations.as_slice() else {
                panic!("expected one separation obligation");
            };
            let Proposition::ResourceSeparate { left, .. } = obligation.proposition() else {
                panic!("expected a separation obligation");
            };
            let expected = Resource::Memory(MemoryRange::from_pointer_value(
                &OldPointer::new(target.clone(), ProgramType::UInt8Pointer),
                0u32.into(),
                layout.size_bytes().into(),
                1,
            ));
            assert_eq!(left.as_ref(), &expected);
            work.push(units);

            if grow_aliases {
                let opening = last.unwrap();
                let returned = ledger
                    .transfer(opening.root_share, borrower, lender)
                    .unwrap();
                let ledger = ledger.apply(&returned).unwrap();
                let ended = ledger.end(opening.scope, lender).unwrap();
                let ledger = ledger.apply(&ended).unwrap();
                let path = copy(&ledger);
                assert!(matches!(path.outcome, StatementOutcome::Normal(_)));
                assert!(path.obligations.is_empty());
            }
        }
        assert!(
            work.iter().all(|units| *units <= work[0] + 32),
            "{grow_aliases}: {work:?}"
        );
    }
}
