use super::*;

#[test]
fn match_payload_construction_reads_arms_without_walking_shared_bodies() {
    for size in [8, 32, 128] {
        let mut body = KernelTerm::variable(KernelType::Integer, Variable(991001));
        for _ in 0..size {
            body =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
        }
        let scrutinee = KernelTermImport::default()
            .argument(&PureFunctionArgument::Algebraic(tests::scrutinee()));
        let arms = (0..size)
            .map(|n| {
                (
                    KernelMatchArm {
                        variant: format!("arm{n}"),
                        bindings: vec![],
                        binding_names: Default::default(),
                    },
                    body.clone(),
                )
            })
            .collect();
        let before = KernelTermExport::machine_export_count();
        let (payload, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelMatch::new(KernelType::Integer, scrutinee, arms).unwrap()
        });
        assert_eq!(payload.arms.len(), size);
        assert!(payload.arguments[1..].iter().all(|child| *child == body));
        assert_eq!(work, size + 1);
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }
}

#[test]
fn numeric_match_observation_walks_shared_bodies_once() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut body = KernelTerm::variable(KernelType::C(format.c_type()), Variable(991982));
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [body.clone(), body],
            );
        }
        let root = KernelMatch::new(
            KernelType::C(format.c_type()),
            KernelTermImport::default()
                .argument(&PureFunctionArgument::Algebraic(tests::scrutinee())),
            vec![(
                KernelMatchArm {
                    variant: "Box".into(),
                    bindings: vec![],
                    binding_names: Default::default(),
                },
                body,
            )],
        )
        .unwrap()
        .into_term();
        let exports = KernelTermExport::machine_export_count();
        let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
            SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap()
        });
        assert!(observed.shared_operand().is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 40 * size + 200, "size={size}, work={work}");
    }
}

#[test]
fn numeric_match_opaque_scrutinee_identity_keeps_exact_roots_and_shared_bodies() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut body = KernelTerm::variable(KernelType::C(format.c_type()), Variable(991983));
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [body.clone(), body],
            );
        }
        let mut scrutinee = tests::scrutinee();
        scrutinee.node = AlgebraicTermNode::PureFunctionApplication {
            name: "opaque_model".into(),
            arguments: vec![],
        };
        let make = || {
            KernelMatch::new(
                KernelType::C(format.c_type()),
                KernelTermImport::default()
                    .argument(&PureFunctionArgument::Algebraic(scrutinee.clone())),
                vec![(
                    KernelMatchArm {
                        variant: "Box".into(),
                        bindings: vec![],
                        binding_names: Default::default(),
                    },
                    body.clone(),
                )],
            )
            .unwrap()
            .into_term()
        };
        let a = make();
        let b = make();
        assert_ne!(a, b, "opaque producer identities remain exact");
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(crate::kernel::shared_machine_syntax_equal(&a, &b));
            assert_eq!(
                crate::kernel::ExecutionValue::Shared(a.clone()),
                crate::kernel::ExecutionValue::Shared(b.clone())
            );
            assert_eq!(
                SharedMachineIntegerTerm::observe_shared(format, a).unwrap(),
                SharedMachineIntegerTerm::observe_shared(format, b).unwrap()
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 1000, "size={size}, work={work}");
    }
}
