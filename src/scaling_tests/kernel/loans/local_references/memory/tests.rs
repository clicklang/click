// Scaling tests of `src/kernel/loans/local_references/memory/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn scalar_lease_selected_adapter_work_is_indexed_across_unrelated_owners() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (state, parent, support) = fixture(size);
        let ((), work) = crate::persistent::measure_persistent_work(|| {
            let (active, child) = begin(&state, &parent, Some(support));
            let (resources, _) = active
                .local_scalar_access_resources(
                    child.local_reference().unwrap(),
                    child.pointer(),
                    CType::Int32,
                    &PureFactContext::new(),
                )
                .unwrap();
            assert!(
                resources
                    .memory_write_range(child.pointer(), 4, &PureFactContext::new())
                    .is_some()
            );
            let recovered = active
                .end_local_scalar_reference(&child, &PureFactContext::new())
                .unwrap();
            assert!(!recovered.has_local_scalar_references());
        });
        measurements.push((size, work));
    }
    eprintln!("scalar lease adapter work: {measurements:?}");
    assert!(
        measurements[3].1 < measurements[0].1 * 4,
        "{measurements:?}"
    );
}
