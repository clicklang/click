// Deterministic scaling tests for condition matching in memory resolution.

#[test]
fn exact_memory_condition_matches_ignore_other_facts() {
    let var = |id| Bitvector32Term::Variable(Variable(id));
    let condition = |kind, left, right| match kind {
        0 => ConditionTerm::IntegerEqual(
            crate::kernel::IntegerTerm::var(Variable(left)).into(),
            crate::kernel::IntegerTerm::var(Variable(right)).into(),
        ),
        1 => ConditionTerm::pointer_equal(
            Pointer::symbolic(Variable(left)),
            Pointer::symbolic(Variable(right)),
        ),
        2 => ConditionTerm::uint64_less_than(var(left), var(right)),
        3 => ConditionTerm::signed_less_than(
            Bitvector32Term::add(var(left), 1u32.into()),
            var(right),
        ),
        _ => unreachable!(),
    };
    for kind in 0..4 {
        for related in [false, true] {
            let mut samples = Vec::new();
            for size in [8u64, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let mut context = PureFactContext::new();
                for index in 0..size {
                    let left = if related { 950_000 } else { index };
                    context = context.assume_condition(condition(kind, left, index + 10_000), true);
                }
                let goal = condition(kind, 950_000, 950_001);
                // Compound misses still use the general fallback; only
                // their exact hits are claimed to have constant work here.
                let missing_work = if kind != 3 {
                    let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                        context.has_matching_condition_fact_for_memory_resolution(&goal, true)
                    });
                    assert!(!found, "exact-only conditions need the stated fact");
                    work
                } else {
                    0
                };
                context = context.assume_condition(goal.clone(), true);
                let (found, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.has_matching_condition_fact_for_memory_resolution(&goal, true)
                });
                assert!(found);
                samples.push((missing_work, hit_work));
            }
            eprintln!("exact condition kind={kind}, related={related}: {samples:?}");
            assert!(
                samples.iter().all(|sample| *sample == samples[0]),
                "condition matching scans facts: kind={kind}, related={related}, {samples:?}"
            );
        }
    }
}
