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
            crate::instrumentation::measure_deterministic_work(|| {
                root.clone().assume_proposition(atom("trigger"))
            })
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
    assert!(
        samples
            .iter()
            .all(|s| s.1 == samples[0].1 && s.3 == samples[0].3)
    );
    assert!(samples.iter().all(|s| s.2 <= samples[0].2 * 5));
}

#[test]
fn exact_propagation_chain_and_fanout_work_follows_produced_facts() {
    for fanout in [false, true] {
        let mut samples = Vec::new();
        for size in [4, 16, 64, 256] {
            let mut root = PureFactContext::new();
            for i in 0..size {
                root = root.assume_proposition(implies(
                    atom(&format!("p{}", if fanout { 0 } else { i })),
                    atom(&format!("p{}", i + 1)),
                ));
            }
            let ((child, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    root.clone().assume_proposition(atom("p0"))
                })
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
            root = root.assume_proposition(implies(
                and(atom("trigger"), atom(&format!("guard{i}"))),
                atom(&format!("result{i}")),
            ));
        }
        let (child, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.assume_proposition(atom("trigger"))
        });
        assert!(!child.contains_known(&atom("result0")));
        let (_, repeat) = crate::instrumentation::measure_deterministic_work(|| {
            child.clone().assume_proposition(atom("trigger"))
        });
        samples.push((size, work, repeat));
    }
    eprintln!("exact propagation blocked clauses: {samples:?}");
    assert!(samples.iter().all(|s| s.1 <= samples[0].1 * s.0 / 4 * 2));
    assert!(samples.iter().all(|s| s.2 == samples[0].2));
}

#[test]
fn exact_falsehood_from_literal_integer_comparisons_ignores_other_facts() {
    use crate::instrumentation::measure_deterministic_work;
    use crate::kernel::{IntegerTerm, SharedIntegerTerm};

    let _session = crate::kernel::VerificationSession::enter();
    let one: SharedIntegerTerm = IntegerTerm::constant_i64(1).into();
    let zero: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
    let comparisons = [
        (
            OldConditionTerm::IntegerEqual(one.clone(), zero.clone()),
            true,
        ),
        (
            OldConditionTerm::IntegerLessEqual(one.clone(), zero.clone()),
            true,
        ),
        (OldConditionTerm::IntegerGreaterThan(one, zero), false),
    ];
    let mut baseline = [None; 3];
    for size in [4, 16, 64, 256] {
        let root = context(
            (0..size)
                .map(|i| implies(atom(&format!("u{i}")), atom(&format!("v{i}"))))
                .collect(),
        );
        for ((comparison, impossible_polarity), baseline) in comparisons.iter().zip(&mut baseline) {
            let (child, work) = measure_deterministic_work(|| {
                root.clone()
                    .assume_condition(comparison.clone(), *impossible_polarity)
            });
            assert!(child.contains_assumed_exact(&falsehood()));
            assert_eq!(work, *baseline.get_or_insert(work), "fact count {size}");
            let consistent = root
                .clone()
                .assume_condition(comparison.clone(), !*impossible_polarity);
            assert!(!consistent.contains_assumed_exact(&falsehood()));
        }
        assert!(!root.contains_assumed_exact(&falsehood()));
    }
}
