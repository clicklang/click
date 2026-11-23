#[test]
fn shared_contract_scope_walk_visits_dag_nodes_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(1017141);
        let mut root = KernelTerm::variable(
            crate::kernel::KernelType::Program(crate::kernel::ProgramType::Int32),
            variable,
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Multiply,
                [root.clone(), root],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_shallow_operand_variables(Operand::Shared(&root), &mut variables);
            variables
        });
        assert_eq!(variables, BTreeSet::from([variable]));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn symbolic_ternary_lowering_ignores_unrelated_facts_and_retains_its_guard() {
    let requirement = super::prepared_entry_cases_tests::ternary_requirement();
    let mut results = Vec::new();
    for (size, flag_is_zero) in [(0, None), (16, Some(true)), (256, Some(false))] {
        let _session = crate::kernel::VerificationSession::enter();
        let flag = MachineTerm::Variable(Variable(1017210));
        let y = MachineTerm::Variable(Variable(1017211));
        let state = ExecutionState::new()
            .with_local("flag", crate::kernel::int32(flag.clone()))
            .with_local("y", crate::kernel::int32(y));
        let mut facts = (0..size).fold(PureFactContext::new(), |facts, index| {
            facts.assume_proposition(Proposition::condition_is(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(1017300 + index)),
                    MachineTerm::constant(1),
                ),
                true,
            ))
        });
        if let Some(flag_is_zero) = flag_is_zero {
            facts = facts.assume_proposition(Proposition::condition_is(
                ConditionTerm::equal(flag, MachineTerm::constant(0)),
                flag_is_zero,
            ));
        }
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            program_lower_spec_proposition_at_state(&state, &requirement, None, &facts)
        });
        results.push((lowered.unwrap().0, work));
    }
    for (proposition, work) in &results[1..] {
        assert_eq!(proposition, &results[0].0);
        assert!(*work <= results[0].1 + 32, "{results:?}");
    }
}
