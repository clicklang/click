// Scaling tests of `src/languages/rust/charon/slice_into_iteration_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn charon_slice_into_iter_work_does_not_depend_on_slice_extent() {
    let export = decode(ARTIFACT, "iteration.rs", SOURCE).unwrap();
    let prepared = super::super::super::import::prepared_for_test(export).unwrap();
    let mut previous = None;
    for length in [8, 128, 1024] {
        let sidecar = format!(
            "verifying \"iteration.rs\"; fn first_byte(bytes: &[u8]) -> u8 {{ requires bytes.len() == {length}u64; views bytes[0..{length}]; ensures result == old(bytes[0]); }} by {{ execute(); simp(); }}"
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(&sidecar, &prepared)
        });
        result.unwrap();
        if let Some(previous) = previous {
            assert!(
                work <= previous + 1000,
                "extent {length}: {work}, previous {previous}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn charon_slice_into_iter_many_slice_parameters_lower_with_linear_charged_work() {
    for count in [8, 128, 1024] {
        let mut export = decode(ARTIFACT, "iteration.rs", SOURCE).unwrap();
        export.functions.retain(|f| f.name == "first_signed");
        let function = &mut export.functions[0];
        let parameter = function.parameters[0].clone();
        for index in 0..count {
            let mut parameter = parameter.clone();
            parameter.name = format!("extra_{index}");
            function.parameters.push(parameter);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::super::lowering::lower(&export)
        });
        let (functions, _) = result.unwrap();
        assert_eq!(functions[0].parameters().len(), 2 * (count + 1));
        assert!(work <= 4 * count + 1000, "{count} slice parameters: {work}");
    }
}
