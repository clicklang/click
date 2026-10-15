// Scaling tests of `src/kernel/mutexes/helper_contracts.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn helper_transfers_ignore_unrelated_resources_protocols_and_history() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let function = function(&format!("helper_scaling_{size}"), HelperEffect::Acquire);
        let mut state = input(&function, false);
        let source = state
            .resources
            .mutex_use_candidate_at(&mutex())
            .unwrap()
            .clone();
        let holder = state.loan_participant.unwrap();
        for index in 0..size {
            let marker = CResourceFact::own(CResource::Token {
                name: format!("unrelated_helper_frame_{index}"),
                arguments: vec![].into(),
            });
            state.resources = state.resources.unchecked_with_fact(marker.clone());
            let support = state
                .resources
                .unique_owned_occurrence_for_fact(&marker)
                .unwrap()
                .0;
            let (ledger, other) = state
                .loan_ledger
                .as_ref()
                .unwrap()
                .borrowed_mutex_use_input(holder, support, Pointer::symbolic(Variable(900 + index)))
                .unwrap();
            state.resources = state
                .resources
                .unchecked_with_fact(ledger.mutex_use_resource(other.usage, holder).unwrap());
            state.loan_ledger = Some(ledger);
            let (held, _, _) = apply_call_effect(
                &state,
                &source,
                &source,
                HelperEffect::Acquire,
                None,
                None,
                None,
                &[],
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let guard = exported_guard(&held).unwrap();
            state = apply_call_effect(
                &held,
                &source,
                &source,
                HelperEffect::Release,
                Some(&guard),
                None,
                None,
                &[],
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap()
            .0;
        }
        let ((released, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (held, _, _) = apply_call_effect(
                    &state,
                    &source,
                    &source,
                    HelperEffect::Acquire,
                    None,
                    None,
                    None,
                    &[],
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                assert!(permits_return(&held));
                let guard = exported_guard(&held).unwrap();
                let (released, _, _) = apply_call_effect(
                    &held,
                    &source,
                    &source,
                    HelperEffect::Release,
                    Some(&guard),
                    None,
                    None,
                    &[],
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                released
            })
        });
        assert_eq!(
            released.resources.facts().len(),
            state.resources.facts().len()
        );
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "mutex helper transition scans unrelated frame or history: {samples:?}"
        );
    }
}
