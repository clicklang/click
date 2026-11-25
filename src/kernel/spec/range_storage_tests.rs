use super::*;
#[test]
fn evaluated_memory_range_keeps_existing_common_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let atom = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(10993611));
        let root =
            KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [atom.clone(), atom]);
        let state = ExecutionState::new().with_retained_local("bound", root.clone().into());
        let bound = SpecExpression::ProgramExpression(ProgramExpression::Variable("bound".into()));
        let resource = SpecResource::Memory {
            base: SpecExpression::Value(ProgramValue::pointer(OldAddress::symbolic(Variable(
                10993612,
            )))),
            start: bound.clone(),
            end: bound,
            element_width: 4,
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
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let Resource::Memory(range) = &paths[0].0 else {
            panic!("memory");
        };
        assert_eq!(range.retained_bounds().0.root(), Some(&root));
        assert_eq!(range.retained_bounds().1.root(), Some(&root));
        assert_eq!(range.spatial_key().retained_bounds().0.root(), Some(&root));
    }
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/spec/range_storage_tests.rs");
}
