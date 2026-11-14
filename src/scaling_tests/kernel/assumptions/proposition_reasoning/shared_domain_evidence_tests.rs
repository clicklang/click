use super::*;

#[test]
fn domain_source_selection_ignores_unrelated_prefix_and_preserves_branches() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable =
            |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
        let root = KernelTerm::machine_binary_shared(
            ty,
            Op::Multiply,
            [variable(979001), variable(979002)],
        );
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let value = operand.operand_view().observe(ty).unwrap();
        let premise = Proposition::ConditionIs(
            ConditionTerm::integer_greater_than(
                IntegerTerm::constant((i32::MAX).into()),
                value.clone(),
            ),
            true,
        );
        let [upper, lower] = ordinary_bounds(
            ty,
            Operation::Add.exact(value, IntegerTerm::constant((1).into())),
        );
        let goal = Proposition::And(Box::new(upper), Box::new(lower));
        let query = crate::kernel::machine_integer::definedness::range_domain_query(&goal).unwrap();
        let mut base = PureFactContext::new();
        for i in 0..size {
            base = base.assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(980000 + i)),
                    MachineTerm::constant(i as u32),
                ),
                true,
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let held = base.clone().assume_proposition(premise.clone());
            assert_eq!(
                held.selected_for_test()
                    .select_domain_rule_premises(&query, DomainRule::Increment),
                Some(vec![premise])
            );
            assert!(
                base.selected_for_test()
                    .select_domain_rule_premises(&query, DomainRule::Increment)
                    .is_none()
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "{samples:?}"
    );
}
