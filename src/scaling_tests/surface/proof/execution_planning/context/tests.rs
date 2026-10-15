// Scaling tests of `src/surface/proof/execution_planning/context.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 6.5s in the parallel gate"]
fn path_certificate_merge_work_is_bounded_by_its_input_steps() {
    let mut samples = Vec::new();
    for leaves in [4usize, 64, 1024] {
        let paths = balanced_path_certificates(leaves, 128);
        let expected = paths.clone();
        let input = paths
            .iter()
            .map(|path| path.case_path.len() + path.certificate.steps().len())
            .sum::<usize>();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            merge_path_aligned_certificates("balanced", paths)
        });
        let certificate = result.expect("a complete balanced case tree must merge");
        let tactics = certificate.to_proof_tactics();
        assert!(
            matches!(tactics.first(), Some(ProofTactic::Mark(name)) if name == &format!("prefix-0-{leaves}"))
        );
        assert!(matches!(tactics.get(1), Some(ProofTactic::If(_))));
        for path in &expected {
            let (selected, offsets) =
                certificate_leaf_for_case_path("balanced", &tactics, &path.case_path)
                    .expect("every original branch must survive merging");
            assert_eq!(selected, path.certificate);
            assert_eq!(offsets, path.case_offsets);
        }
        samples.push((leaves, input, work));
        assert!(
            work > 0 && work <= input * 10,
            "merge must charge its work once per input step: {samples:?}"
        );
    }
    eprintln!("(leaves, input steps/cases, merge work): {samples:?}");
}
