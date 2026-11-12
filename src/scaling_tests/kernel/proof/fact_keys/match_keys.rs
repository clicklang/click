use super::*;

#[test]
fn match_alpha_identity_work_scales_with_selected_arms() {
    let samples = [16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let left = selected_match(100, size);
        let right = selected_match(200, size);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(key(&left), key(&right));
        });
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else { unreachable!() };
        assert!(*sw > 0);
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
