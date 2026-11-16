#[test]
fn exact_propagation_queries_and_updates_ignore_unrelated_rules() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut root = PureFactContext::new();
        for i in 0..size {
            root = root.assume_proposition(implies(atom(&format!("u{i}")), atom(&format!("v{i}"))));
        }
        root = root.assume_proposition(implies(atom("trigger"), atom("result")));
        let ((child, update), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| root.clone().assume_proposition(atom("trigger")))
        });
        let (_, query) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..8 {
                assert!(child.contains_known(&atom("result")));
                assert!(!root.contains_known(&atom("result")));
                assert!(!child.contains_known(&atom("absent")));
            }
        });
        samples.push((size, update, persistent, query));
    }
    eprintln!("exact propagation unrelated rules: {samples:?}");
    assert!(samples.iter().all(|s| s.1 == samples[0].1 && s.3 == samples[0].3));
    assert!(samples.iter().all(|s| s.2 <= samples[0].2 * 5));
}

#[test]
fn exact_propagation_chain_and_fanout_work_follows_produced_facts() {
    for fanout in [false, true] {
        let mut samples = Vec::new();
        for size in [4, 16, 64, 256] {
            let mut root = PureFactContext::new();
            for i in 0..size {
                root = root.assume_proposition(implies(atom(&format!("p{}", if fanout {0} else {i})), atom(&format!("p{}", i+1))));
            }
            let ((child, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| root.clone().assume_proposition(atom("p0")))
            });
            assert!(child.contains_known(&atom(&format!("p{size}"))));
            assert!(!root.contains_known(&atom(&format!("p{size}"))));
            samples.push((size, work, persistent));
        }
        eprintln!("exact propagation fanout={fanout}: {samples:?}");
        assert!(samples.iter().all(|s| s.1 <= samples[0].1 * s.0 / 4 * 2));
        assert!(samples.iter().all(|s| s.2 <= samples[0].2 * s.0 / 4 * 5));
    }
}

#[test]
fn exact_propagation_blocked_clauses_consume_each_occurrence_once() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut root = PureFactContext::new();
        for i in 0..size {
            root = root.assume_proposition(implies(and(atom("trigger"), atom(&format!("guard{i}"))), atom(&format!("result{i}"))));
        }
        let (child, work) = crate::instrumentation::measure_deterministic_work(|| root.assume_proposition(atom("trigger")));
        assert!(!child.contains_known(&atom("result0")));
        let (_, repeat) = crate::instrumentation::measure_deterministic_work(|| child.clone().assume_proposition(atom("trigger")));
        samples.push((size, work, repeat));
    }
    eprintln!("exact propagation blocked clauses: {samples:?}");
    assert!(samples.iter().all(|s| s.1 <= samples[0].1 * s.0 / 4 * 2));
    assert!(samples.iter().all(|s| s.2 == samples[0].2));
}
