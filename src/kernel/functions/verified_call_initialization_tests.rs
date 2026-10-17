use super::*;

fn local_pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete("local:caller:x".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn owned_cell_spec() -> CResourceSpec {
    CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(1),
    ))
}

fn caller_state(pointer: &Pointer) -> CState {
    let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
        CResource::Memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
    ));
    CState::new()
        .with_population_creation_tracking()
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 4))
        .with_resource_context(resources)
}

fn apply(function: CFunction, state: &CState, pointer: &Pointer) -> Vec<CFunctionPath> {
    let environment =
        CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            loop_semantics: CLoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    execute_c_function_call_paths(
        state,
        &function,
        &[c_pointer_value(pointer.clone())],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("verified call should execute")
}

#[test]
fn owned_read_does_not_treat_ownership_as_initialization() {
    let pointer = local_pointer();
    let function = c_function(
        CType::Int32,
        "read_owned",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_index(c_variable("p"), c_int32_literal(0))),
    )
    .with_resource_summary(vec![owned_cell_spec()], Vec::new());
    let paths = apply(function, &caller_state(&pointer), &pointer);
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            ..
        }]
    ));
}

#[test]
fn owned_write_keeps_an_uninitialized_output_writable() {
    let pointer = local_pointer();
    let function = c_function(
        CType::Void,
        "write_owned",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_store(
            c_index(c_variable("p"), c_int32_literal(0)),
            c_int32_literal(7),
        ),
    )
    .with_resource_summary(vec![owned_cell_spec()], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
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
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
}
