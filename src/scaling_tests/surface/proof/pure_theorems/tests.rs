// Scaling tests for scalar induction script preparation and checked prefixes.

#[test]
#[ignore = "nightly: 0.67s focused scalar-induction prefixes at four sizes"]
fn scalar_induction_prefix_work_scales_with_explicit_helpers() {
    let template = "theorem prefix(n: int32) { requires n >= 0; ensures n >= 0 by { have n == n; let ih = induct(n); known(); } }";
    let samples = [8, 16, 32, 64].map(|size| {
        let source = template.replace("have n == n;", &"have n == n by known();\n".repeat(size));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::verify_c_sources(&source, &[])
        });
        result.unwrap();
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "induction prefix work must scale with the written script: {samples:?}"
        );
    }
}
