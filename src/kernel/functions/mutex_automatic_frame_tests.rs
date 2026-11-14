use super::*;

#[test]
fn mutex_automatic_frame_retirement_requires_destruction() {
    let function = program_function(
        ProgramType::Int32,
        "scope",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    for name in ["holder", "frame:holder", "lifetime:holder"] {
        let state = ExecutionState::new().with_local(name, int32(0));
        let address = state.locals.slot(name).unwrap().clone();
        let memory = Memory::new().with_block(address.block.clone(), 40);
        let initialized =
            crate::kernel::mutexes::MutexContext::new(state.with_memory(memory.clone()))
                .initialize_empty(address.clone(), 40)
                .unwrap();
        assert!(matches!(
            end_function_body_automatic_lifetimes(
                initialized.state(),
                &function,
                &Memory::new(),
                None
            ),
            Err(RuntimeError::MutexStorageScopeEnd { .. })
        ));
        // The caller's object remains live across a callee return.
        assert_eq!(
            end_function_body_automatic_lifetimes(initialized.state(), &function, &memory, None),
            Ok(memory.clone())
        );
        if name != "holder" {
            assert!(matches!(
                end_inline_frame_automatic_lifetimes(initialized.state()),
                Err(RuntimeError::MutexStorageScopeEnd { .. })
            ));
        }
        let destroyed = initialized
            .destroy(&address, &PureFactContext::new())
            .unwrap();
        assert!(
            !end_function_body_automatic_lifetimes(
                destroyed.state(),
                &function,
                &Memory::new(),
                None
            )
            .unwrap()
            .has_block(&address.block)
        );
        if name != "holder" {
            assert!(
                !end_inline_frame_automatic_lifetimes(destroyed.state())
                    .unwrap()
                    .has_block(&address.block)
            );
        }
    }
}
