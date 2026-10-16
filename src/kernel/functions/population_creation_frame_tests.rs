use super::*;

#[test]
fn authority_refuses_calls_that_reach_a_population() {
    let authority = CState::new().with_population_creation_tracking();
    let call = |helper: &CFunction| {
        execute_c_function_call_paths(
            &authority,
            helper,
            &[],
            &PureFactContext::new(),
            CExecutionContext::apply_verified_rules(&CExecutionEnvironment::new()),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
    };
    let refused = |paths: &[CFunctionPath]| {
        matches!(
            paths,
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)),
                ..
            }] if message.contains("assumed contract changes a population or mutex resource")
        )
    };

    // A helper whose contract moves no resource reaches no population.
    let ordinary = c_function(CType::Void, "helper", vec![], CStatement::Skip);
    assert!(!contract_reaches_population(ordinary.contract_interface()));
    assert!(!refused(&call(&ordinary)));

    // An abstract token may be an authorized member, so an unadmitted
    // contract producing one is refused.
    let minting = c_function(CType::Void, "mint", vec![], CStatement::Skip).with_resource_summary(
        vec![],
        vec![CResourceSpec::token(
            CResourceAccessMode::Own,
            "ticket".into(),
            vec![],
            vec![],
        )],
    );
    assert!(contract_reaches_population(minting.contract_interface()));
    assert!(refused(&call(&minting)));
}

#[test]
fn unused_creation_ledgers_compare_equal_and_used_ones_do_not() {
    let left = CState::new().with_population_creation_tracking();
    let right = CState::new().with_population_creation_tracking();
    assert_ne!(left, right, "fresh ledgers have distinct identities");
    assert!(left.equal_up_to_unused_creation_ledgers(&right));
    assert!(!left.equal_up_to_unused_creation_ledgers(&CState::new()));

    let mut base = CState::new().with_local("frame:holder", int32(0));
    let block = base.locals.slot("frame:holder").unwrap().block.clone();
    base.set_memory(CMemory::new().with_block(block.clone(), 4));
    let unused = base.clone().with_population_creation_tracking();
    let mut used = base.with_population_creation_tracking();
    assert!(used.equal_up_to_unused_creation_ledgers(&unused));
    used.record_population_storage_creation(block);
    assert!(!used.equal_up_to_unused_creation_ledgers(&unused));
    assert!(!unused.equal_up_to_unused_creation_ledgers(&used));
}

#[test]
fn ended_automatic_storage_retires_creation_evidence() {
    let function = c_function(CType::Int32, "scope", vec![], c_return(c_int32_literal(0)));
    for name in ["frame:holder", "lifetime:holder"] {
        let mut state = CState::new()
            .with_local(name, int32(0))
            .with_population_creation_tracking();
        let block = state.locals.slot(name).unwrap().block.clone();
        state.set_memory(CMemory::new().with_block(block.clone(), 4));
        state.record_population_storage_creation(block.clone());
        assert!(
            state
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .created_here(&block)
        );
        for memory in [
            end_inline_frame_automatic_lifetimes(&state).unwrap(),
            end_function_body_automatic_lifetimes(&state, &function, &CMemory::new(), None)
                .unwrap(),
        ] {
            let retired = retired_automatic_creation_blocks(&state, &memory);
            assert_eq!(retired, vec![block.clone()]);
            let mut after = state.clone().with_memory(memory);
            for block in retired {
                after.retire_population_storage(&block).unwrap();
            }
            assert!(
                !after
                    .population_effects
                    .creation
                    .as_ref()
                    .unwrap()
                    .created_here(&block)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/population_creation_frame_tests.rs");
}
