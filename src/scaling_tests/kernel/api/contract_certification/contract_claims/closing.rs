#[test]
fn private_output_footprint_lookup_ignores_memory_and_alias_history() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let (caller, effects, assumptions) = aliased_write_fixture(true, size);
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            check_empty_footprint(&caller, &effects, &assumptions).is_ok()
        });
        assert!(accepted);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}
