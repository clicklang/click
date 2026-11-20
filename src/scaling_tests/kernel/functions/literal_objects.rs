#[test]
fn string_literal_reference_work_ignores_other_literals_and_selected_byte_length() {
    for grow_bytes in [false, true] {
        let mut work_by_size = Vec::new();
        for size in [1, 16, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let count = if grow_bytes { 1 } else { size };
            let bytes = if grow_bytes { size } else { 1 };
            let literals = (0..count)
                .map(|i| {
                    let mut content = vec![b'x'; bytes];
                    content.push(0);
                    StringLiteral::new(StringLiteralId::new("literal_work", i as u32), content)
                })
                .collect();
            let function = program_function(
                ProgramType::Void,
                "literal_work",
                vec![],
                ProgramStatement::Skip,
            )
            .with_string_literals(literals);
            let state = initialize_program_function_globals(&ExecutionState::new(), &function);
            let expression =
                ProgramExpression::StringLiteral(StringLiteralId::new("literal_work", 0));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::evaluate_expression_value_paths(
                    &state,
                    &expression,
                    &PureFactContext::default(),
                    &mut ExecutionBudget::for_new_execution(),
                )
                .unwrap()
            });
            work_by_size.push(work);
        }
        assert!(
            work_by_size
                .iter()
                .all(|work| *work <= work_by_size[0] + 64),
            "{work_by_size:?}"
        );
    }
}

#[test]
fn statement_completion_ignores_unrelated_blocks_and_string_literals() {
    for with_literals in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let _session = crate::kernel::VerificationSession::enter();
            let mut memory = SymbolicMemory::new();
            for i in 0..size {
                let block = if with_literals {
                    let identity = StringLiteralId::new("statement_completion", i);
                    SymbolicMemory::string_literal_pointer(&identity, b"ok\0").base
                } else {
                    AddressBase::Heap(u64::from(i))
                };
                memory = if with_literals {
                    memory.with_read_only_block(block, 3)
                } else {
                    memory.with_block(block, 3)
                };
            }
            let state = ExecutionState::new().with_memory(memory);
            let (execution, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::prove_symbolic_execution_statement_verification_paths_with_environment(
                    state,
                    ProgramStatement::Skip,
                    PureFactContext::new(),
                    ExecutionEnvironment::new(),
                    ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                )
            });
            let [path] = execution.paths() else {
                panic!("expected a checked statement");
            };
            assert!(path.obligations().is_empty());
            assert!(path.facts().is_empty());
            work
        });
        eprintln!("statement work with 4/16/64 blocks, literals={with_literals}: {samples:?}");
        assert_eq!(samples, [samples[0]; 3]);
    }
}
