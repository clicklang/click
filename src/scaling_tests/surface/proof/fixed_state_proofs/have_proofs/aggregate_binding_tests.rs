use super::*;

fn selection_work(selected: u32, unrelated: u32) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let (mut state, mut values) = aggregate_entry(selected);
    let names = values.keys().cloned().collect();
    for index in 0..unrelated {
        let name = format!("unrelated_{index}");
        let value = crate::kernel::int32(index);
        state = state.with_local(name.clone(), value.clone());
        values.insert(name, value);
    }
    let (lowering, work) = crate::instrumentation::measure_deterministic_work(|| {
        FixedStateLowering::for_names(
            names,
            ContractEnvironment::new(&values, &ClickArrayRefs::new()),
            &state,
            &state,
            None,
            false,
        )
    });
    assert!(
        lowering
            .lowering_state
            .locals()
            .aggregate_layout("input_0")
            .is_some()
    );
    work
}

#[test]
fn aggregate_binding_selection_ignores_unrelated_names() {
    let samples = [0, 16, 64, 256].map(|size| selection_work(4, size));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn aggregate_binding_selection_scales_with_selected_names() {
    let samples = [8, 16, 32, 64].map(|size| selection_work(size, 64));
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "{samples:?}"
    );
}
