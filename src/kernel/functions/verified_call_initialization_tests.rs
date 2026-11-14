use super::*;

fn local_pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete("local:caller:x".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn owned_cell_spec() -> ResourceSpec {
    ResourceSpec::owned_memory(MemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(1),
    ))
}

fn uninitialized_cell_spec() -> ResourceSpec {
    ResourceSpec::owned_memory(
        MemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1))
            .with_uninitialized(true),
    )
}

fn caller_state(pointer: &Pointer) -> ExecutionState {
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own(
        Resource::Memory(MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
    ));
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(pointer.block.clone(), 4))
        .with_resource_context(resources)
}

fn apply(
    function: ProgramFunction,
    state: &ExecutionState,
    pointer: &Pointer,
) -> Vec<FunctionPath> {
    let environment =
        ExecutionEnvironment::new().with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    execute_c_function_call_paths(
        state,
        &function,
        &[c_pointer_value(pointer.clone())],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("verified call should execute")
}

#[test]
fn an_owning_call_requires_the_caller_to_initialize_the_range() {
    let pointer = local_pointer();
    let function = c_function(
        ProgramType::Int32,
        "read_owned",
        vec![c_parameter("p", ProgramType::Int32Pointer)],
        c_return(c_index(c_variable("p"), c_int32_literal(0))),
    )
    .with_resource_summary(vec![owned_cell_spec()], Vec::new());
    let paths = apply(function, &caller_state(&pointer), &pointer);
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
            ..
        }] if message.contains("holds its range as initialized")
    ));
}

#[test]
fn owned_write_keeps_an_uninitialized_output_writable() {
    let pointer = local_pointer();
    let function = c_function(
        ProgramType::Void,
        "write_owned",
        vec![c_parameter("p", ProgramType::Int32Pointer)],
        c_store(
            c_index(c_variable("p"), c_int32_literal(0)),
            c_int32_literal(7),
        ),
    )
    .with_resource_summary(vec![uninitialized_cell_spec()], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        )],
        Vec::new(),
        true,
    );
    let paths = apply(function, &caller_state(&pointer), &pointer);
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
}
