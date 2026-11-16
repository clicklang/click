use super::*;

fn work(selected: usize, unrelated: u32) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let mut state = entry_state();
    for index in 0..unrelated {
        state = state.with_local(format!("other_{index}"), crate::kernel::int32(index));
    }
    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
        for _ in 0..selected {
            assert!(lower_name(&state, "input", true).is_ok());
        }
    });
    work
}

#[test]
fn old_aggregate_lookup_scales_with_reads_not_unrelated_locals() {
    let unrelated = [0, 16, 64, 256].map(|n| work(8, n));
    assert!(
        unrelated.iter().all(|w| *w <= unrelated[0] + 32),
        "{unrelated:?}"
    );
    let selected = [8, 16, 32, 64].map(|n| work(n, 64));
    assert!(selected[0] > 0);
    assert!(
        selected.windows(2).all(|p| p[1] <= 2 * p[0] + 32),
        "{selected:?}"
    );
}

#[test]
fn recorded_aggregate_place_lookup_ignores_unrelated_locals() {
    let costs = [0, 16, 64, 256].map(|count| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = entry_state();
        for index in 0..count {
            state = state.with_local(format!("unrelated_{index}"), crate::kernel::int32(index));
        }
        lower_recorded_input(&state).1
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 32),
        "{costs:?}"
    );
}
