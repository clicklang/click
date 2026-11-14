use super::*;

#[test]
fn retained_closing_work_tracks_outcomes_and_clauses_without_walking_ambient_facts() {
    for clauses in [1, 2, 4, 8] {
        let mut samples = Vec::new();
        for unrelated in [0, 64, 256] {
            let (function, entry, path, outcome) = fixture(clauses, unrelated);
            for paths in [1, 4, 16, 64] {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..paths {
                        let prepared = prepare_closing_path(
                            &function,
                            &path,
                            &entry.closing_entry,
                            &outcome,
                            vec![],
                            false,
                            false,
                            None,
                            ResourceContext::new(),
                            false,
                            None,
                        )
                        .unwrap();
                        assert!(Arc::ptr_eq(
                            &prepared.checked_required_resources,
                            &entry.closing_entry.checked
                        ));
                    }
                });
                assert!(
                    work <= 512 * paths * (clauses + 1),
                    "{paths} paths, {clauses} clauses, {unrelated} unrelated facts: {work}"
                );
                samples.push((paths, unrelated, work));
            }
        }
        for paths in [1, 4, 16, 64] {
            let costs = samples
                .iter()
                .filter(|(count, _, _)| *count == paths)
                .map(|(_, _, work)| *work)
                .collect::<Vec<_>>();
            assert!(
                costs.windows(2).all(|pair| pair[0] == pair[1]),
                "{clauses} clauses, {paths} paths: {costs:?}"
            );
        }
    }
}
