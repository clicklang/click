use super::*;

#[test]
fn evaluated_iterated_guard_retains_the_existing_common_producer() {
    let _session = crate::kernel::VerificationSession::enter();
    let atom = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993621));
    let root = KernelTerm::machine_binary_shared(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        [atom.clone(), atom],
    );
    let state = ExecutionState::new().with_retained_local("guard", root.clone().into());
    let value =
        |bits| ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(bits)));
    let pointer =
        |id| ProgramExpression::Value(ProgramValue::pointer(Address::symbolic(Variable(id))));
    let spec = crate::kernel::IteratedSpec {
        owner: "CommonGuard".into(),
        element: MemorySegment::new(pointer(10993622), value(0), value(0)),
        stride: 1,
        start_offset: 0,
        end_offset: 1,
        guard_base: pointer(10993623),
        guard_cell_type: ProgramType::Int32,
        guard_cell_width: 4,
        holds_when_equal: true,
        guard_value: ProgramExpression::Variable("guard".into()),
    };
    let exports = KernelTermExport::machine_export_count();
    let fact = evaluate_iterated_resource_spec(
        &state,
        &spec,
        false,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let Resource::Iterated(value) = fact.resource() else {
        panic!("iterated");
    };
    assert_eq!(value.guard.value.root(), Some(&root));
    assert!(!root.has_cached_native_argument());
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/functions/iterated_operand_storage_tests.rs");
}

#[test]
fn evaluated_resource_quantity_retains_the_existing_common_producer() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993651));
    let state = ExecutionState::new().with_retained_local("quantity", root.clone().into());
    let exports = KernelTermExport::machine_export_count();
    let quantity = evaluate_declared_quantity(
        &state,
        &ProgramExpression::Variable("quantity".into()),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .unwrap();
    let fact = ResourceFact::own_quantity_stored(Resource::Emp, quantity);
    let ResourceFact::Own(_, quantity) = fact else {
        panic!("owned");
    };
    assert_eq!(quantity.root(), Some(&root));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(!root.has_cached_native_argument());
}
