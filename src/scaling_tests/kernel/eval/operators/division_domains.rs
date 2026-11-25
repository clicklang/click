use super::*;

#[test]
fn division_domain_checks_do_not_scan_unrelated_assumptions() {
    for established in [false, true] {
        let mut costs = Vec::new();
        for size in [0, 128, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let left = OldMachineTerm::Variable(Variable(970_001 + size * 4));
            let right = OldMachineTerm::Variable(Variable(970_002 + size * 4));
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        OldMachineTerm::Variable(Variable(971_000 + index)),
                        OldMachineTerm::constant(index as u32),
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

#[test]
fn literal_or_zero_check_ignores_related_and_unrelated_bounds() {
    let format = MachineIntegerType::Int32;
    let word = OldMachineTerm::Variable(Variable(972_001));
    let divisor = OldMachineTerm::machine_binary(
        format,
        MachineBinaryOp::BitwiseOr,
        word.clone(),
        OldMachineTerm::constant(1),
    );
    let zero = ConditionTerm::equal(divisor.clone(), OldMachineTerm::constant(0));
    for related in [false, true] {
        let samples = [4u32, 16, 64, 256].map(|size| {
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                let value = if related {
                    word.clone()
                } else {
                    OldMachineTerm::Variable(Variable(972_100 + u64::from(index)))
                };
                facts.assume_condition(
                    ConditionTerm::signed_greater_equal(value, OldMachineTerm::constant(!index)),
                    true,
                )
            });
            let (decision, work) = crate::instrumentation::measure_deterministic_work(|| {
                decide_zero(&divisor, &zero, &facts, &ExecutionFacts::new())
            });
            assert_eq!(decision, Some(false));
            work
        });
        assert_eq!(samples, [samples[0]; 4], "{related}: {samples:?}");
    }
}

#[test]
fn computed_divisor_queries_use_indexed_operand_facts() {
    let format = MachineIntegerType::Int32;
    let word = OldMachineTerm::var(Variable(973_001));
    let literal = OldMachineTerm::constant(1);
    let positive = OldMachineTerm::var(Variable(973_002));
    let xor = OldMachineTerm::machine_binary(
        format,
        MachineBinaryOp::BitwiseXor,
        word.clone(),
        literal.clone(),
    );
    let or = OldMachineTerm::machine_binary(
        format,
        MachineBinaryOp::BitwiseOr,
        word.clone(),
        positive.clone(),
    );
    let zero = ConditionTerm::equal(xor.clone(), OldMachineTerm::constant(0));
    let or_zero = ConditionTerm::equal(or.clone(), OldMachineTerm::constant(0));
    let path = ExecutionFacts::new();
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut facts = PureFactContext::new()
                .assume_condition(ConditionTerm::equal(word.clone(), literal.clone()), false)
                .assume_condition(
                    ConditionTerm::signed_greater_than(
                        positive.clone(),
                        OldMachineTerm::constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_equal(word.clone(), OldMachineTerm::constant(0)),
                    true,
                );
            for index in 0..size {
                let value = if related {
                    word.clone()
                } else {
                    OldMachineTerm::var(Variable(973_100 + u64::from(index)))
                };
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(value, OldMachineTerm::constant(100 + index)),
                    true,
                );
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    decide_zero(&xor, &zero, &facts, &path),
                    decide_zero(&or, &or_zero, &facts, &path),
                    bitwise_excludes(format, &or, true, &facts, &path),
                    bitwise_excludes(format, &xor, true, &facts, &path),
                )
            });
            assert_eq!(result, (Some(false), Some(false), true, true));
            work
        });
        let minimum = samples.iter().copied().min().unwrap();
        assert!(
            samples.iter().all(|&work| work <= minimum + 4),
            "{related}: {samples:?}"
        );
    }
}
