// Scaling tests of `src/languages/rust/charon/split_slices_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn charon_split_at_checked_byte_reads_do_not_enumerate_slice_extent() {
    let export = decode(ARTIFACT, "split.rs", SOURCE).unwrap();
    let prepared = super::super::super::import::prepared_for_test(export).unwrap();
    let mut previous = None;
    for length in [8, 128, 1024] {
        let sidecar = CLAIM.replace(
            "views bytes[0..bytes.len()];",
            &format!("requires bytes.len() == {length}u64; views bytes[0..bytes.len()];"),
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
