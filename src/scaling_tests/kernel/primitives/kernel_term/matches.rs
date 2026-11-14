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
