use super::*;

#[test]
fn range_access_work_is_flat_across_recorded_order_chains() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let (context, base, indices, end) = ordered_range(size);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for position in [0, size / 2, size] {
                assert!(covered(&context, &base, &indices[position], &end));
            }
        });
        samples.push((size, work));
    }
    eprintln!("ordered range access: {samples:?}");
    assert!(samples[0].1 > 0);
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "range accesses walked the chain at each index: {samples:?}"
    );
}
