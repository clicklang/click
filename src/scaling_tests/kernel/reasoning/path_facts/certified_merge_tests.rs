fn certified_fact_merge_work(
    prefix_size: usize,
    additions: usize,
    related: bool,
) -> (usize, usize) {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let prefix: ExecutionFacts = (0..prefix_size)
        .map(|i| {
            ExecutionPureFact::new(Proposition::condition_is(
                OldConditionTerm::signed_less_equal(
                    OldMachineTerm::Variable(Variable(if related {
                        1025100
                    } else {
                        1024100 + i as u64
                    })),
                    OldMachineTerm::constant(i as u32 + 8),
                ),
                true,
            ))
        })
        .collect::<Vec<_>>()
        .into();
    let produced: ExecutionFacts = (0..additions)
        .map(|i| {
            ExecutionPureFact::certified(Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(1025100 + i as u64)),
                    OldMachineTerm::constant(7),
                ),
                true,
            ))
        })
        .collect::<Vec<_>>()
        .into();
    // A cold prefix and a sibling fork: neither merge may inspect old facts
    // or replace their producer records in order to retain this checked delta.
    // Stream iteration has its own counter, separate from general work.
    // Count it explicitly so restoring either old prefix scan fails this test.
    crate::kernel::execution_facts::take_fact_reads();
    let ((left, right), work) = crate::instrumentation::measure_deterministic_work(|| {
        (
            merge_facts_with_changes(&prefix, &produced, &context).unwrap(),
            merge_facts_with_changes(&prefix, &produced, &context).unwrap(),
        )
    });
    let reads = crate::kernel::execution_facts::take_fact_reads();
    for (facts, mut changed) in [left, right] {
        changed.sort_unstable();
        changed.dedup();
        assert_eq!(facts.len(), prefix_size + additions);
        assert_eq!(
            changed,
            (prefix_size..prefix_size + additions).collect::<Vec<_>>()
        );
        assert_eq!(facts.suffix_since(&prefix).unwrap(), produced);
    }
    assert_eq!(prefix.len(), prefix_size);
    (work, reads)
}

#[test]
fn certified_fact_merge_ignores_cold_unrelated_and_related_prefixes() {
    for related in [false, true] {
        let samples = [4, 64, 512].map(|size| certified_fact_merge_work(size, 1, related));
        eprintln!("certified merge work, related={related}: {samples:?}");
        assert!(samples[0].0 > 0 && samples[0].1 > 0, "unmeasured merge");
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn certified_fact_merge_is_linear_in_the_supplied_delta() {
    let one = certified_fact_merge_work(64, 1, false);
    for additions in [4, 16, 64] {
        let work = certified_fact_merge_work(64, additions, false);
        assert!(
            work.0 <= one.0 * additions && work.1 <= one.1 * additions,
            "{additions} facts cost {work:?}; one costs {one:?}"
        );
    }
}
