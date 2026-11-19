use super::*;

#[test]
fn aliased_byte_output_lookup_ignores_unrelated_memory_and_alias_history() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, function, assumptions, word) = aliased_byte_output_fixture(size, true);
        let mut facts = ExecutionFacts::new();
        let mut budget = ExecutionBudget::new();
        budget.install_program_byte_order(ByteOrder::Little);
        let mut post_state = state.clone();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_produced_memory(
                &state,
                &state,
                function.contract_interface(),
                &mut post_state,
                &assumptions,
                &mut facts,
                &mut budget,
            )
        });
        result.unwrap().unwrap();
        assert!(post_state.memory().has_initialized_bytes_at(&word, 4));
        assert_eq!(facts.len(), 1);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}
