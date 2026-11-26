#[test]
fn common_algebraic_equality_visits_shared_constructor_pairs_once() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let key = AlgebraicValueType::Algebraic {
            name: "EqualityTree".into(),
            arguments: vec![],
        };
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Leaf".into(),
                fields: vec![AlgebraicValueType::Program(ProgramType::Int32Pointer)],
            },
            AlgebraicVariantType {
                name: "Branch".into(),
                fields: vec![key.clone(), key.clone()],
            },
        ]
        .into();
        let ty = AlgebraicType {
            rigid: false,
            name: "EqualityTree".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from(
                [(key, variants)],
            ))),
        };
        let pointer = OldPointer::new(
            Address::symbolic(Variable(999674)),
            ProgramType::Int32Pointer,
        );
        let mut roots = [pointer.clone(), pointer].map(|pointer| {
            KernelTermImport::default().algebraic(&AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Leaf".into(),
                    fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(pointer))],
                },
            })
        });
        for _ in 0..size {
            roots = roots.map(|root| {
                KernelConstructor {
                    algebraic_type: ty.clone(),
                    variant: "Branch".into(),
                    fields: vec![root.clone(), root],
                }
                .into_term()
            });
        }
        assert_ne!(roots[0], roots[1]);
        let exports = (
            KernelTermExport::algebraic_export_count(),
            KernelTermExport::machine_export_count(),
        );
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            roots[0].algebraic_syntax_equal(&roots[1])
        });
        assert!(equal);
        assert!(work <= 5 * size + 20, "size={size} work={work}");
        assert_eq!(
            exports,
            (
                KernelTermExport::algebraic_export_count(),
                KernelTermExport::machine_export_count()
            )
        );
    }
}
