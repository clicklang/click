// Scaling tests of `src/kernel/termination.rs` (module `checked_callee_certification_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn checked_callee_claim_reuse_shares_the_dependency_set() {
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let calls = Arc::new(
            (0..size)
                .map(|n| format!("callee_{n}"))
                .collect::<BTreeSet<_>>(),
        );
        let (merged, work) = crate::instrumentation::measure_deterministic_work(|| {
            merge_checked_callees(std::iter::repeat_n(Some(&calls), size)).unwrap()
        });
        eprintln!("claim reuse size={size}, dependency work={work}");
        assert!(Arc::ptr_eq(&calls, &merged));
        assert_eq!(merged.len(), size);
        if let Some(before) = previous {
            assert!(
                work <= 5 * before,
                "superlinear claim reuse: {before} -> {work}"
            );
        }
        previous = Some(work);
    }
    let empty = Arc::new(BTreeSet::new());
    assert!(merge_checked_callees([Some(&empty), None]).is_none());
    assert!(merge_checked_callees([]).is_none());
    assert!(merge_checked_callees([Some(&empty)]).unwrap().is_empty());
    let left = Arc::new(BTreeSet::from(["left".into()]));
    let right = Arc::new(BTreeSet::from(["right".into()]));
    assert_eq!(
        *merge_checked_callees([Some(&left), Some(&right)]).unwrap(),
        BTreeSet::from(["left".into(), "right".into()])
    );
}
