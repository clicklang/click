use super::*;

#[test]
fn signed_shift_headroom_uses_indexed_operand_extrema() {
    let count = OldMachineTerm::var(Variable(974_001));
    let left = OldMachineTerm::var(Variable(974_002));
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut facts = PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::signed_less_equal(left.clone(), OldMachineTerm::constant(3)),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_than(count.clone(), OldMachineTerm::constant(16)),
                    true,
                );
            for index in 0..size {
                let value = if related {
                    count.clone()
                } else {
                    OldMachineTerm::var(Variable(974_100 + u64::from(index)))
                };
                facts = facts.assume_condition(
                    OldConditionTerm::signed_less_equal(
                        value,
                        OldMachineTerm::constant(100 + index),
                    ),
                    true,
                );
            }
            let (fits, work) = crate::instrumentation::measure_deterministic_work(|| {
                signed_shift_fits_from_bounds(
                    MachineIntegerType::Int32,
                    &left,
                    &count,
                    false,
                    &facts,
                    &ExecutionFacts::new(),
                )
            });
            assert!(fits);
            work
        });
        // Key lookups can take slightly different work across index shapes.
        let minimum = samples.iter().copied().min().unwrap();
        assert!(
            samples.iter().all(|&work| work <= minimum + 4),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn signed_shift_headroom_uses_indexed_expression_guards() {
    let count = OldMachineTerm::var(Variable(975_001));
    let assumptions = PureFactContext::new();
    let one = OldMachineTerm::constant(1);
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut guards = ExecutionFacts::new();
            guards.ensure_indexed();
            guards.push(ExecutionPureFact::new(Proposition::condition_is(
                OldConditionTerm::signed_less_than(count.clone(), OldMachineTerm::constant(16)),
                true,
            )));
            for index in 0..size {
                let value = if related {
                    count.clone()
                } else {
                    OldMachineTerm::var(Variable(975_100 + u64::from(index)))
                };
                guards.push(ExecutionPureFact::new(Proposition::condition_is(
                    OldConditionTerm::signed_less_equal(
                        value,
                        OldMachineTerm::constant(100 + index),
                    ),
                    true,
                )));
            }
            let (fits, work) = crate::instrumentation::measure_deterministic_work(|| {
                signed_shift_fits_from_bounds(
                    MachineIntegerType::Int32,
                    &one,
                    &count,
                    false,
                    &assumptions,
                    &guards,
                )
            });
            assert!(fits);
            work
        });
        let minimum = samples.iter().copied().min().unwrap();
        assert!(
            samples.iter().all(|&work| work <= minimum + 4),
            "{related}: {samples:?}"
        );
    }
}
