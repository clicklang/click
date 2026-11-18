use super::*;

#[test]
fn constructed_state_observation_does_not_revisit_ambient_owners_or_aliases() {
    for axis in ["related", "owners", "aliases"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Address::symbolic(Variable(8_919_000));
            let mut aliases = Vec::new();
            let mut resources = ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer.clone(),
                    0u32.into(),
                    4u32.into(),
                    1,
                )),
            );
            for index in 0..count {
                if axis == "aliases" {
                    aliases.push(Proposition::condition_is(
                        ConditionTerm::address_equal(
                            pointer.clone(),
                            Address::symbolic(Variable(8_919_100 + u64::from(index))),
                        ),
                        true,
                    ));
                } else {
                    let (base, start) = if axis == "related" {
                        (pointer.clone(), (index + 1) * 8)
                    } else {
                        (Address::symbolic(Variable(8_919_200 + u64::from(index))), 0)
                    };
                    resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            base,
                            start.into(),
                            (start + 4).into(),
                            1,
                        ),
                    ));
                }
            }
            let store = PureFactStore::from_ordered(&aliases);
            resources.synchronize_memory_equalities(store.assumptions());
            let state = ExecutionState::new().with_resource_context(resources);
            let mut facts = ProofResourcePureFacts::new(store);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                append_state_resource_context_observable_facts_with_store(&state, &mut facts);
            });
            samples.push(work);
        }
        assert!(samples[2] <= samples[0] + 64, "{axis}: {samples:?}");
    }
}
