use super::*;

#[test]
fn identity_match_check_scales_with_its_constructor_fields() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let value = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer; size]);
        let bindings = (0..size)
            .map(|i| AlgebraicValue::Integer(IntegerTerm::var(Variable(992_000 + i as u64))))
            .collect::<Vec<_>>();
        let mut matched = value.clone();
        matched.node = AlgebraicTermNode::Match {
            scrutinee: Box::new(value.clone()),
            arms: vec![AlgebraicResultMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                body: AlgebraicTerm {
                    algebraic_type: value.algebraic_type.clone(),
                    node: AlgebraicTermNode::Constructor {
                        variant: "Arm".into(),
                        fields: bindings.clone(),
                    },
                },
                bindings,
            }],
        };
        let goal = Proposition::Equal(
            Term::Algebraic(value.into()),
            Term::Algebraic(matched.into()),
        );
        let (holds, work) =
            crate::instrumentation::measure_deterministic_work(|| solve_builtin_prop(&goal));
        assert!(holds);
        assert!(
            (size..=4 * size + 32).contains(&work),
            "size={size} work={work}"
        );
    }
}
