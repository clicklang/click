// Scaling tests of `src/languages/cpp/lifetime.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn lifetime_planning_and_exit_validation_scale_with_events_and_emitted_edges() {
    let record = record();
    for size in [8usize, 32, 128, 512, 1024] {
        let mut body = (0..size)
            .map(|i| declaration(&format!("guard_{i}")))
            .collect::<Vec<_>>();
        body.push(returned(
            (0..size)
                .rev()
                .map(|i| cleanup(&format!("guard_{i}")))
                .collect(),
        ));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let plan = LifetimePlan::new(&body, |id| (id == "Guard").then_some(&record))?;
            plan.validate(&body, "caller")
        });
        result.unwrap();
        assert!(work >= size && work <= 4 * size + 4, "size {size}: {work}");
        for mutation in 0..3 {
            let mut forged = body.clone();
            let CppStatement::Return { cleanups, .. } = forged.last_mut().unwrap() else {
                unreachable!()
            };
            match mutation {
                0 => cleanups.swap(0, 1),
                1 => {
                    cleanups.pop();
                }
                _ => {
                    cleanups[0] = cleanups[1].clone();
                }
            }
            let plan = LifetimePlan::new(&forged, |id| (id == "Guard").then_some(&record)).unwrap();
            assert!(
                plan.validate(&forged, "caller")
                    .unwrap_err()
                    .contains("exactly once in reverse construction order")
            );
        }
    }
}

#[test]
fn lowering_without_destructors_does_not_rescan_function_bodies() {
    let mut record = record();
    record.destructor = None;
    let records =
        super::super::super::schema::RecordIndex::new(BTreeMap::from([("Guard".into(), &record)]));
    for size in [8usize, 32, 128, 512] {
        let mut body = (0..size)
            .map(|i| declaration(&format!("trivial_{i}")))
            .collect::<Vec<_>>();
        body.push(returned(Vec::new()));
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            LifetimePlan::for_lowering(&body, &records)
        });
        let plan = plan.unwrap();
        assert_eq!(
            work, 0,
            "size {size}: a trivial import needs no cleanup inventory walk"
        );
        plan.validate(&body, "caller").unwrap();
    }
}
