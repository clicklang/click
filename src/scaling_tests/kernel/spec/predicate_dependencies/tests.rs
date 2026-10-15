// Scaling tests of `src/kernel/spec/predicate_dependencies.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn predicate_dependency_scan_has_linear_deterministic_work() {
    let samples = [16, 64, 256].map(|size| {
        let mut body = SpecProposition::Defined(literal());
        for _ in 1..size {
            body = SpecProposition::And(
                Box::new(SpecProposition::Defined(literal())),
                Box::new(body),
            );
        }
        let (dependent, work) =
            crate::instrumentation::measure_deterministic_work(|| observes_resource_state(&body));
        assert!(!dependent);
        (size, work)
    });
    for (size, work) in samples {
        assert_eq!(
            work,
            3 * size - 1,
            "each proposition and expression is visited once"
        );
    }
}
