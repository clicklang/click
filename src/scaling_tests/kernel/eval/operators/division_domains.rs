use super::*;

#[test]
fn division_domain_checks_do_not_scan_unrelated_assumptions() {
    for established in [false, true] {
        let mut costs = Vec::new();
        for size in [0, 128, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let left = Bitvector32Term::Variable(Variable(970_001 + size * 4));
            let right = Bitvector32Term::Variable(Variable(970_002 + size * 4));
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(971_000 + index)),
                        Bitvector32Term::Constant(index as u32),
                    ),
                    true,
                );
            }
            if established {
                facts = facts.assume_proposition(Proposition::signed_division_exclusion(
                    MachineIntegerType::Int32,
                    &left,
                    &right,
                ));
            }
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                apply_nonzero(
                    MachineIntegerType::Int32,
                    left,
                    right,
                    ExecutionFacts::new(),
                    vec![],
                    &facts,
                    result,
                )
            });
            assert_eq!(paths.len(), if established { 1 } else { 2 });
            costs.push(work);
        }
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "established={established}: {costs:?}"
        );
    }
}
