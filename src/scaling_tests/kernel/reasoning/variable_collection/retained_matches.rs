use super::*;
use crate::kernel::{KernelIntegerOperator, KernelMatchArm, KernelTerm, KernelTermImport};

#[test]
fn match_scope_readers_share_growing_arm_bodies() {
    for size in [8, 32, 128] {
        let mut body = KernelTerm::variable(KernelType::Integer, Variable(991910));
        for _ in 0..size {
            body =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
        }
        let scrutinee = KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(
            KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]),
        ));
        let arms = (0..size)
            .map(|_| {
                (
                    KernelMatchArm {
                        variant: "Arm".into(),
                        binding_names: Default::default(),
                        bindings: vec![KernelTerm::variable(KernelType::Integer, Variable(991911))],
                    },
                    body.clone(),
                )
            })
            .collect();
        let matched = KernelMatch::new(KernelType::Integer, scrutinee, arms).unwrap();
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_match_variables(&matched, FoldVariableRead::IntegerFree, &mut variables);
            variables
        });
        assert_eq!(variables, BTreeSet::from([Variable(991910)]));
        assert!(work <= 30 * size + 100, "size={size}, work={work}");
    }
}

#[test]
fn match_scope_readers_merge_only_changed_binding_paths() {
    for size in [8, 32, 128] {
        let mut body = KernelTerm::variable(KernelType::Integer, Variable(992000));
        for n in 1..size {
            body = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![
                    body,
                    KernelTerm::variable(KernelType::Integer, Variable(992000 + n as u64)),
                ],
            )
            .unwrap();
        }
        let mut scrutinee = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        let variants: std::sync::Arc<[crate::kernel::AlgebraicVariantType]> = (0..size)
            .map(|n| crate::kernel::AlgebraicVariantType {
                name: format!("Case{n}"),
                fields: vec![AlgebraicValueType::Integer],
            })
            .collect::<Vec<_>>()
            .into();
        let key = scrutinee.algebraic_type.value_type();
        scrutinee.algebraic_type.variants = variants.clone();
        scrutinee.algebraic_type.schemas =
            std::sync::Arc::new(crate::kernel::AlgebraicSchemas::new(
                std::collections::BTreeMap::from([(key, variants)]),
            ));
        let scrutinee =
            KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(scrutinee));
        let arms = (0..size)
            .map(|n| {
                (
                    KernelMatchArm {
                        variant: format!("Case{n}"),
                        binding_names: Default::default(),
                        bindings: vec![KernelTerm::variable(
                            KernelType::Integer,
                            Variable(992000 + n as u64),
                        )],
                    },
                    body.clone(),
                )
            })
            .collect();
        let matched = KernelMatch::new(KernelType::Integer, scrutinee, arms).unwrap();
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_match_variables(&matched, FoldVariableRead::IntegerFree, &mut variables);
            variables
        });
        assert_eq!(
            variables,
            (0..size).map(|n| Variable(992000 + n as u64)).collect()
        );
        assert!(work <= 30 * size + 100, "size={size}, work={work}");
    }
}
