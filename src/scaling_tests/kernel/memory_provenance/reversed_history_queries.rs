use super::*;

#[test]
fn reversed_negative_history_queries_do_not_walk_again() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let (before, after, pointer) = changed_history(size);
        let assumptions = PureFactContext::new();
        let (first, cold) = crate::instrumentation::measure_deterministic_work(|| {
            recorded_load_history(&before, &after, &pointer, LoadKind::Bits32, &assumptions)
        });
        assert!(matches!(first, LoadHistory::DifferentVersions));
        let (reversed, warm) = crate::instrumentation::measure_deterministic_work(|| {
            recorded_load_history(&after, &before, &pointer, LoadKind::Bits32, &assumptions)
        });
        assert!(matches!(reversed, LoadHistory::DifferentVersions));
        assert!(cold > 0);
        samples.push((size, cold, warm));
    }
    eprintln!("reversed negative histories: {samples:?}");
    assert!(
        samples.iter().all(|(_, _, warm)| *warm <= 4),
        "reversed queries repeated their walks: {samples:?}"
    );
}
