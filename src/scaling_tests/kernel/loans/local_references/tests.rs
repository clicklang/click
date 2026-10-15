// Scaling tests of `src/kernel/loans/local_references/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn local_reference_selected_lifecycle_is_indexed_among_unrelated_roots() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (mut ledger, holder, mut resources, root) = fixture();
        for index in 0..size {
            let fact = scalar(&format!("local:ambient:{index}"));
            resources = resources.unchecked_with_fact(fact.clone());
            (_, ledger) = register(&ledger, holder, &resources, &fact);
        }
        assert!(ledger.invariant_holds());
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            let (child, open) = ledger
                .borrow_local_reference(&root, holder, &resources)
                .unwrap();
            let active = ledger.apply(&open).unwrap();
            assert_eq!(access(&active, &child, holder, &resources), Ok(()));
            let ended = active
                .apply(
                    &active
                        .recover_local_reference(&child, holder, &resources)
                        .unwrap(),
                )
                .unwrap();
            assert_eq!(access(&ended, &root, holder, &resources), Ok(()));
        });
        measurements.push((size, work));
    }
    eprintln!("local-reference selected lifecycle work: {measurements:?}");
    assert!(measurements.iter().all(|(_, work)| *work < 2048));
    assert!(measurements[3].1 < measurements[0].1 * 4);
}
