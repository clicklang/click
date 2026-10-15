// Scaling tests of `src/kernel/primitives/memory_equality_index/symbolic.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn symbolic_footprint_selection_does_not_scan_same_base_ranges() {
    let base = Pointer::symbolic(Variable(920_000));
    let alias = Pointer::symbolic(Variable(920_001));
    let n = Bitvector32Term::Variable(Variable(920_002));
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let held = CResourceFact::view_memory(range(&base, 0u32.into(), n.clone()));
        let mut resources =
            ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held.clone());
        for i in 0..size {
            let end = Bitvector32Term::Variable(Variable(921_000 + i));
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(range(
                &base,
                0u32.into(),
                end,
            )));
        }
        // Apply the explicit equality delta before measuring steady queries.
        resources.synchronize_memory_equalities(&facts);
        let required = range(&alias, 0u32.into(), n.clone());
        let supplier = resources.occurrences_for_fact(&held)[0];
        let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    resources.symbolic_range_read_supported(&required, &facts, None),
                    Some(true)
                );
                let uncertain = range(
                    &alias,
                    0u32.into(),
                    Bitvector32Term::Variable(Variable(950_000)),
                );
                assert_eq!(
                    resources.symbolic_range_read_supported(&uncertain, &facts, None),
                    None
                );
                assert_eq!(
                    resources.symbolic_range_read_supported(&required, &facts, Some(supplier)),
                    Some(true)
                );
            })
        });
        samples.push((size, work, persistent));
    }
    assert!(
        samples
            .iter()
            .all(|(_, work, _)| *work <= samples[0].1 * 2 + 64),
        "supplier search: {samples:?}"
    );
    assert!(
        samples
            .iter()
            .all(|(_, _, work)| *work <= samples[0].2 * 4 + 512),
        "deep/linear index lookup: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn symbolic_byte_read_consumer_refuses_ambiguous_suppliers_without_search() {
    let base = Pointer::symbolic(Variable(960_000));
    let alias = Pointer::symbolic(Variable(960_001));
    let n = Bitvector32Term::Variable(Variable(960_002));
    let m = Bitvector32Term::Variable(Variable(960_003));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), m.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(m.clone(), n.clone()), true);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let held = CResourceFact::view_memory(range(&base, 0u32.into(), n.clone()));
        let mut resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held);
        for i in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(range(
                &base,
                0u32.into(),
                Bitvector32Term::Variable(Variable(961_000 + i)),
            )));
        }
        resources.synchronize_memory_equalities(&facts);
        let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(crate::kernel::resource_context_has_symbolic_range_read(
                    &resources, &alias, &n, &facts,
                ));
                // m <= n can validate a selected supplier, but cannot choose
                // one by testing every range in an ambiguous start bucket.
                assert!(!crate::kernel::resource_context_has_symbolic_range_read(
                    &resources, &alias, &m, &facts,
                ));
            })
        });
        samples.push((size, work, persistent));
    }
    assert!(
        samples
            .iter()
            .all(|(_, work, _)| *work <= samples[0].1 * 2 + 64),
        "symbolic byte consumer searched suppliers: {samples:?}"
    );
    assert!(
        samples
            .iter()
            .all(|(_, _, work)| *work <= samples[0].2 * 4 + 512),
        "symbolic byte consumer scanned persistent inputs: {samples:?}"
    );
}
