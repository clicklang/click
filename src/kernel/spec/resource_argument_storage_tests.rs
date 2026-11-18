use super::*;

#[test]
fn resource_argument_evaluation_keeps_the_existing_program_producer() {
    let _session = crate::kernel::VerificationSession::enter();
    let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993601));
    let root = KernelTerm::machine_binary_shared(
        MachineIntegerType::UInt32,
        MachineBinaryOp::Add,
        [atom.clone(), atom],
    );
    let state =
        ExecutionState::new().with_retained_local("word", ExecutionValue::Shared(root.clone()));
    let resource = SpecResource::Composite {
        name: "SharedArgument".into(),
        arguments: vec![SpecExpression::ProgramExpression(
            ProgramExpression::Variable("word".into()),
        )],
    };
    let mut execution = ExecutionBudget::default();
    let exports = KernelTermExport::machine_export_count();
    let paths = evaluate_spec_resource_at_state_in(
        SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
        &resource,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut execution),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let Resource::Composite { arguments, .. } = &paths[0].0 else {
        panic!("composite")
    };
    assert_eq!(arguments.program_value(0).unwrap().shared(), Some(&root));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(!root.has_cached_native_argument());
}

#[test]
fn resource_argument_arrays_keep_native_identity_order_hash_and_debug() {
    use std::hash::{Hash, Hasher};
    let _session = crate::kernel::VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(10993602));
    let call = |argument| {
        AlgebraicValue::Program(ProgramValue::UInt32(
            MachineTerm::ClickFunctionApplication {
                name: "argument_input".into(),
                arguments: vec![argument],
            },
        ))
    };
    let inputs = vec![
        call(PureFunctionArgument::Value(ProgramValue::UInt32(
            word.clone(),
        ))),
        call(PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
        )),
        AlgebraicValue::Program(ProgramValue::Bool(MachineTerm::constant(2))),
        AlgebraicValue::Program(ProgramValue::Float32(MachineTerm::uint32_constant(
            0x7fc00123,
        ))),
        AlgebraicValue::Program(ProgramValue::Float64(MachineTerm::uint64_constant(
            0x8000000000000000,
        ))),
        AlgebraicValue::Integer(IntegerTerm::Variable(Variable(10993603))),
        AlgebraicValue::Program(
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(10993604)),
                ProgramType::Int32Pointer,
            )
            .with_pointer_pointee_constant(true),
        ),
    ];
    fn hash(value: &impl Hash) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }
    for value in &inputs {
        let native: NativeResourceArguments = vec![value.clone()].into();
        let stored = ResourceArguments::from(native.clone());
        assert_eq!(hash(&stored), hash(&native));
        assert_eq!(format!("{stored:?}"), format!("{native:?}"));
        for other in &inputs {
            let other_native: NativeResourceArguments = vec![other.clone()].into();
            let other_stored = ResourceArguments::from(other_native.clone());
            assert_eq!(stored == other_stored, native == other_native);
            assert_eq!(stored.cmp(&other_stored), native.cmp(&other_native));
        }
    }
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/spec/resource_argument_storage_tests.rs");
}
