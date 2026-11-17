use super::*;

fn local_pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete("local:caller:x".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn owned_cell_spec() -> ResourceSpec {
    ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ))
}

fn uninitialized_cell_spec() -> ResourceSpec {
    ResourceSpec::owned_memory(
        MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )
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
        .with_memory(SymbolicMemory::new().with_block(pointer.block.clone(), 4))
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
            descent_completion: None,
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    execute_program_function_call_paths(
        state,
        &function,
        &[crate::kernel::program_expression::pointer_value(
            pointer.clone(),
        )],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("verified call should execute")
}

#[test]
fn an_owning_call_requires_the_caller_to_initialize_the_range() {
    let pointer = local_pointer();
    let function = program_function(
        ProgramType::Int32,
        "read_owned",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
        )),
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
    let function = program_function(
        ProgramType::Void,
        "write_owned",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_store(
            crate::kernel::program_expression::index(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            crate::kernel::program_expression::int32_literal(7),
        ),
    )
    .with_resource_summary(vec![uninitialized_cell_spec()], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
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

fn aliased_byte_output_fixture(
    size: u32,
    initialized_output: bool,
) -> (ExecutionState, ProgramFunction, PureFactContext, Pointer) {
    let word = SymbolicMemory::local_pointer("output-word");
    let alias = Pointer::symbolic(Variable(987_000));
    let mut memory = SymbolicMemory::new().with_declared_scalar_block(
        word.block.clone(),
        4,
        ProgramType::UInt32,
    );
    let mut assumptions = PureFactContext::new();
    let mut previous = alias.clone();
    for i in 0..size {
        let next = Pointer::symbolic(Variable(987_001 + u64::from(i)));
        assumptions = assumptions
            .assume_condition(ConditionTerm::pointer_equal(previous, next.clone()), true);
        previous = next;
        memory = memory.with_block(format!("unrelated-output-{i}"), 4);
    }
    assumptions =
        assumptions.assume_condition(ConditionTerm::pointer_equal(previous, word.clone()), true);
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    )
    .with_element_width(1);
    let function = program_function(
        ProgramType::Void,
        "fill_alias",
        vec![program_parameter("p", ProgramType::UInt8Pointer)],
        ProgramStatement::Skip,
    )
    .with_resource_summary(
        vec![
            ResourceSpec::owned_memory(segment.clone().with_uninitialized(true))
                .with_role(ResourceTransferRole::Consume),
        ],
        vec![
            ResourceSpec::owned_memory(segment.with_uninitialized(!initialized_output))
                .with_role(ResourceTransferRole::Produce),
        ],
    );
    let state = ExecutionState::new().with_memory(memory).with_local(
        "p",
        ProgramValue::typed_pointer(alias, ProgramType::UInt8Pointer),
    );
    (state, function, assumptions, word)
}

#[test]
fn byte_output_initializes_the_concrete_storage_held_through_an_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    for initialized in [false, true] {
        let (state, function, assumptions, word) = aliased_byte_output_fixture(8, initialized);
        // This producer receives post-havoc memory. It records initialization
        // only for initialized outputs; call-level stale-word controls exercise
        // the earlier invalidation of the caller's previous contents.
        let mut facts = ExecutionFacts::new();
        let mut budget = ExecutionBudget::new();
        budget.install_program_byte_order(ByteOrder::Little);
        let memory = produced_memory_initialization(
            &state,
            &state,
            function.contract_interface(),
            state.memory().clone(),
            &assumptions,
            &mut facts,
            &mut budget,
        )
        .unwrap()
        .unwrap();
        assert_eq!(memory.has_initialized_bytes_at(&word, 4), initialized);
        assert_eq!(facts.len(), usize::from(initialized));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/verified_call_initialization_tests.rs");
}
