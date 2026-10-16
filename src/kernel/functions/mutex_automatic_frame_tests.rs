use super::*;

#[test]
fn mutex_automatic_frame_retirement_requires_destruction() {
    let function = c_function(CType::Int32, "scope", vec![], c_return(c_int32_literal(0)));
    for name in ["holder", "frame:holder", "lifetime:holder"] {
        let state = CState::new().with_local(name, int32(0));
        let address = state.locals.slot(name).unwrap().clone();
        let memory = CMemory::new().with_block(address.block.clone(), 40);
        let initialized =
            crate::kernel::mutexes::MutexContext::new(state.with_memory(memory.clone()))
                .initialize_empty(address.clone(), 40)
                .unwrap();
        assert!(matches!(
            end_function_body_automatic_lifetimes(
                initialized.state(),
                &function,
                &CMemory::new(),
                None
            ),
            Err(CRuntimeError::MutexStorageScopeEnd { .. })
        ));
        // The caller's object remains live across a callee return.
        assert_eq!(
            end_function_body_automatic_lifetimes(initialized.state(), &function, &memory, None),
            Ok(memory.clone())
        );
        if name != "holder" {
            assert!(matches!(
                end_inline_frame_automatic_lifetimes(initialized.state()),
                Err(CRuntimeError::MutexStorageScopeEnd { .. })
            ));
        }
        let destroyed = initialized
            .destroy(&address, &PureFactContext::new())
            .unwrap();
        assert!(
            !end_function_body_automatic_lifetimes(
                destroyed.state(),
                &function,
                &CMemory::new(),
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
