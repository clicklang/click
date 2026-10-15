// Scaling tests of `src/kernel/memory_provenance.rs` (module `borrow_partition_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 3.1s in the parallel gate"]
fn borrow_partition_query_does_not_scan_unrelated_resources_or_history() {
    let mut samples = Vec::new();
    let mut admission_samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let (_, mut source, write, read) = resources();
        let mut context = PureFactContext::new()
            .assume_proposition(Proposition::CResourceComposition(source.clone()));
        let (_, admission) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                source = source
                    .clone()
                    .unchecked_with_fact(CResourceFact::own_memory(range(910_000 + index)));
                context = context
                    .clone()
                    .assume_proposition(Proposition::CResourceComposition(source.clone()));
            }
        });
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert!(
                    typed_store_separated_ranges_evidence(
                        write.base(),
                        4,
                        read.base(),
                        4,
                        &context
                    )
                    .is_some()
                );
            }
        });
        eprintln!("borrow partition size={size}, admission={admission}, queries={work}");
        samples.push(work);
        admission_samples.push(admission);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated history changed lookup work: {samples:?}"
    );
    assert!(
        admission_samples
            .windows(2)
            .all(|pair| pair[1] <= 5 * pair[0]),
        "superlinear admission: {admission_samples:?}"
    );
}
