#[test]
fn loop_control_destinations_ignore_unrelated_bodies_tails_and_parent_frames() {
    for continuing in [false, true] {
        for with_update in [false, true] {
            let mut measurements = Vec::new();
            for size in [4, 16, 64, 256] {
                let mut fixture =
                    nested_loop(continuing, false, with_update, size, size, size, false);
                let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                    transfer(&mut fixture, continuing)
                });
                assert_destination(&fixture, continuing, size);
                measurements.push(work);
            }
            assert!(
                measurements.iter().all(|work| *work <= measurements[0] + 8),
                "{continuing}/{with_update}: {measurements:?}"
            );
        }
    }
}

#[test]
fn loop_control_work_tracks_only_exited_scopes() {
    for continuing in [false, true] {
        let mut baseline = None;
        for scopes in [0, 4, 16, 64, 256] {
            let mut fixture = nested_loop(continuing, false, true, 2, 2, 2, false);
            for _ in 0..scopes {
                fixture
                    .core
                    .frontier
                    .continuations
                    .push(ProofExecutionContinuation {
                        loop_control: None,
                        remaining: Some(fixture.after_function.clone()),
                        next_statement_index: 99,
                        exceptional: None,
                    });
            }
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                transfer(&mut fixture, continuing)
            });
            assert_destination(&fixture, continuing, 2);
            let base = *baseline.get_or_insert(work);
            assert!(work >= base + scopes, "each exited scope is charged");
            assert!(
                work <= base + 4 * scopes + 8,
                "{scopes}: {work}, base {base}"
            );
        }
    }
}
