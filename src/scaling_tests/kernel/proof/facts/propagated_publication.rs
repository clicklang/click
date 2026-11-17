#[test]
fn propagated_fact_publication_visits_only_the_new_consequences() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut input = (0..size)
            .map(|i| atom(&format!("unrelated{i}")))
            .collect::<Vec<_>>();
        input.push(rule());
        let root = ProofFacts::from_ordered(&input);
        let ((child, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| root.with_fact(atom("trigger")))
        });
        assert!(child.contains(&atom("result")));
        assert!(!root.contains(&atom("result")));
        assert_eq!(
            child.store().introduced_since(root.store()).unwrap().len(),
            2
        );
        samples.push((size, work, persistent));
    }
    eprintln!("propagated publication: {samples:?}");
    assert!(samples.iter().all(|s| s.1 <= samples[0].1 + 8));
    assert!(samples.iter().all(|s| s.2 <= samples[0].2 * 5));
}
