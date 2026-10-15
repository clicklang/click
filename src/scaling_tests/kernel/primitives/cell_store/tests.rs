// Scaling tests of `src/kernel/primitives/cell_store.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn retained_run_reads_refresh_load_origins_without_scanning_the_run() {
    let mut samples = Vec::new();
    for count in [16, 64, 65, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = source(99);
        let base = constant(&PointerBlock::from("cell-store-source-99"), 0);
        let run = run(base.clone(), 4, count, &source);
        let first = run.value(0);
        let CValue::Int32(crate::kernel::Bitvector32Term::Variable(variable)) = first else {
            panic!("a seeded scalar names its source load");
        };
        assert!(crate::kernel::eval::registered_load_origin_for_variable(&variable).is_some());
        crate::kernel::eval::begin_load_origin_epoch();
        assert!(crate::kernel::eval::registered_load_origin_for_variable(&variable).is_none());
        assert_eq!(run.value(0), first);
        assert_eq!(
            crate::kernel::eval::registered_load_origin_for_variable(&variable),
            Some((source, base)),
            "a retained {count}-cell run must observe the load in this epoch"
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert_eq!(run.value(0), first);
            }
        });
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "repeated seeded reads must use the epoch cache without scanning the run: {samples:?}"
    );
}
