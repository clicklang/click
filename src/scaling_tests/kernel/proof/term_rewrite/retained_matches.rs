use super::*;

#[test]
fn common_match_rewrite_shares_arm_bodies_without_machine_exports() {
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut body = KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(991920));
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [body.clone(), body],
            );
        }
        let scrutinee = KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(
            KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(ProgramType::Int32)]),
        ));
        let arms = (0..size)
            .map(|_| {
                (
                    KernelMatchArm {
                        variant: "Arm".into(),
                        binding_names: Default::default(),
                        bindings: vec![KernelTerm::variable(
                            KernelType::C(ProgramType::Int32),
                            Variable(991921),
                        )],
                    },
                    body.clone(),
                )
            })
            .collect();
        let matched = KernelMatch::new(KernelType::C(ProgramType::Int32), scrutinee, arms).unwrap();
        let from = MachineTerm::Variable(Variable(991922));
        let to = MachineTerm::Variable(Variable(991923));
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite.retained_match(&matched));
        assert_eq!(result.unwrap(), matched);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 150 * size + 300, "size={size}, work={work}");
    }
}

#[test]
fn common_match_reduction_retains_shared_machine_body() {
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut scrutinee =
            KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(ProgramType::Int32)]);
        scrutinee.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::C(ProgramValue::Int32(
                MachineTerm::Variable(Variable(991924)),
            ))],
        };
        let mut body = KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(991921));
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [body.clone(), body],
            );
        }
        let matched = KernelMatch::new(
            KernelType::C(ProgramType::Int32),
            KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(scrutinee)),
            vec![(
                KernelMatchArm {
                    variant: "Arm".into(),
                    binding_names: Default::default(),
                    bindings: vec![KernelTerm::variable(
                        KernelType::C(ProgramType::Int32),
                        Variable(991921),
                    )],
                },
                body,
            )],
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::empty().reduce_retained_match(&matched)
        });
        let mut result = result.unwrap().unwrap();
        for _ in 0..size {
            let KernelTermNode::MachineBinary { arguments, .. } = result.node() else {
                panic!("retained arithmetic")
            };
            assert_eq!(arguments[0].id(), arguments[1].id());
            result = arguments[0].clone();
        }
        assert!(matches!(
            result.node(),
            KernelTermNode::Variable(variable) if *variable == Variable(991924)
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 150 * size + 300, "size={size}, work={work}");
    }
}

#[test]
fn retained_algebraic_match_rewrite_keeps_shared_nested_bodies() {
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut native = KernelMatch::test_scrutinee(vec![]);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Arm".into(),
                fields: vec![],
            },
            AlgebraicVariantType {
                name: "Other".into(),
                fields: vec![],
            },
        ]
        .into();
        native.algebraic_type.variants = variants.clone();
        native.algebraic_type.schemas = std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from(
            [(native.algebraic_type.value_type(), variants)],
        )));
        let ty = KernelType::Algebraic(native.algebraic_type.clone());
        let leaf = KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(native));
        let mut root = leaf.clone();
        for _ in 0..size {
            let arm = KernelMatchArm {
                variant: "Arm".into(),
                bindings: vec![],
                binding_names: Default::default(),
            };
            let mut other = arm.clone();
            other.variant = "Other".into();
            root = KernelMatch::new(
                ty.clone(),
                leaf.clone(),
                vec![(arm, root.clone()), (other, root)],
            )
            .unwrap()
            .into_term();
        }
        let KernelTermNode::Match(matched) = root.node() else {
            unreachable!()
        };
        let from = MachineTerm::Variable(Variable(991995));
        let to = MachineTerm::constant(7);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let exports = KernelTermExport::algebraic_export_count();
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite.retained_match(matched));
        assert_eq!(result.unwrap().into_term(), root);
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert!(work < 100 * size + 100, "size={size}, work={work}");
    }
}
