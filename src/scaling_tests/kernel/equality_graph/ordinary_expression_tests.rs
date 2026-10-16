use super::*;

#[test]
fn ordinary_expression_queries_ignore_unrelated_classes() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_int32_equality(&word(950_000 + 2 * i), &word(950_001 + 2 * i));
        }
        graph.add_int32_equality(&word(940_061), &word(940_062));
        let build = |x| {
            U::UInt64From32.build_raw(
                B::BitwiseAnd.build_raw(B::Multiply.build_raw(x, word(940_063)), word(940_064)),
            )
        };
        let a = build(word(940_061));
        let b = build(word(940_062));
        let (known, work) =
            crate::instrumentation::measure_deterministic_work(|| graph.are_uint64_equal(&a, &b));
        assert!(known);
        if let Some(previous) = previous {
            assert_eq!(work, previous, "ambient size {size}");
        }
        previous = Some(work);
    }
}
#[test]
fn nested_ordinary_expression_registration_and_late_merges_scale_linearly() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let build = |mut x| {
            for _ in 0..size {
                x = B::BitwiseAnd.build_raw(x, word(940_073));
            }
            x
        };
        let a = build(word(940_071));
        let b = build(word(940_072));
        let ((before, after), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            let before = graph.are_int32_equal(&a, &b);
            graph.add_int32_equality(&word(940_071), &word(940_072));
            (before, graph.are_int32_equal(&a, &b))
        });
        assert!(!before);
        assert!(after);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= 5 * p[0]),
        "superlinear work: {samples:?}"
    );
}
