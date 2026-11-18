#[test]
fn iterated_descriptor_handoffs_and_holes_preserve_growing_shared_operands() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993624));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let operand = StoredMachineTerm::from_value(root.clone().into()).unwrap();
            let guard = IteratedGuard::new_stored(
                Address::symbolic(Variable(10993625)),
                ProgramType::Int32,
                4,
                true,
                operand.clone(),
            );
            let fact = IteratedMemory::new_stored(
                "CommonGuard",
                Address::symbolic(Variable(10993626)),
                4,
                1,
                0,
                1,
                operand.clone(),
                operand.clone(),
                guard,
            )
            .unwrap();
            for _ in 0..32 {
                let with_hole = fact.clone().with_stored_hole(operand.clone());
                assert_eq!(with_hole.lower.root(), Some(&root));
                assert_eq!(with_hole.upper.root(), Some(&root));
                assert_eq!(with_hole.guard.value.root(), Some(&root));
                assert_eq!(with_hole.holes()[0].root(), Some(&root));
                let closed = with_hole.without_hole_at(0);
                assert!(closed.holes().is_empty());
                assert_eq!(closed.lower.root(), Some(&root));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}

#[test]
fn owned_resource_quantity_handoffs_share_growing_machine_dags() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993652));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let state = ExecutionState::new().with_retained_local("quantity", root.clone().into());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let quantity = evaluate_declared_quantity(
                &state,
                &ProgramExpression::Variable("quantity".into()),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
            .unwrap();
            let deferred = crate::kernel::threads::DeferredMemberExchange {
                block: AddressBase::ExternalArgument,
                description: ResourceDescription::new(
                    "quantity".into(),
                    vec![].into(),
                    ResourceFieldSchema::new(vec![]).unwrap(),
                ),
                produce: true,
                quantity: quantity.clone(),
                exclusive: false,
            };
            let fact = ResourceFact::own_quantity_stored(Resource::Emp, quantity);
            for _ in 0..32 {
                let copy = deferred.clone();
                assert_eq!(copy.quantity.root(), Some(&root));
                assert_eq!(copy.block, deferred.block);
                assert_eq!(copy.produce, deferred.produce);
                let ResourceFact::Own(_, value) = fact.clone() else {
                    panic!("owned");
                };
                assert_eq!(value.root(), Some(&root));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
