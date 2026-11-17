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
                    let pointer = Memory::local_pointer(format!("other{i}"));
                    state.set_memory(
                        state
                            .memory
                            .clone()
                            .with_block(pointer.block.clone(), 4)
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
            let pointer = Memory::local_pointer(format!("other{index}"));
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), 4)
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
