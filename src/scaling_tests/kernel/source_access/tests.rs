// Scaling tests of `src/kernel/source_access.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn source_reference_selected_observation_merge_does_not_scan_ambient_facts() {
    for size in [16, 64, 256, 1024] {
        let mut prefix = ExecutionFacts::new();
        for index in 0..size {
            prefix.push(ExecutionPureFact::condition(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(Variable(index))),
                    Box::new(Bitvector32Term::Constant(7)),
                ),
                true,
            ));
        }
        let mut suffix = ExecutionFacts::new();
        suffix.push(read_fact());
        let (merged, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::path_facts::merge_facts(
                &prefix,
                &suffix,
                &PureFactContext::new(),
            )
            .unwrap()
        });
        assert_eq!(merged.len(), size as usize + 1);
        assert!(
            merged
                .iter()
                .last()
                .unwrap()
                .reference_observation
                .is_some()
        );
        assert!(
            work <= 64,
            "selected source delta scanned {size} old facts: {work}"
        );
        let mut births = ExecutionFacts::new();
        births.push(borrow_fact());
        let (merged, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::path_facts::merge_facts(
                &prefix,
                &births,
                &PureFactContext::new(),
            )
            .unwrap()
        });
        assert_eq!(merged.len(), size as usize + 1);
        assert!(
            merged
                .iter()
                .last()
                .unwrap()
                .reference_observation
                .is_borrow()
        );
        assert!(work <= 64, "birth delta scanned {size} old facts: {work}");
    }
}
