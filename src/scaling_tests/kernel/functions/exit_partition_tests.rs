use super::*;

#[test]
fn constructed_exit_and_observation_do_not_revisit_the_ambient_partition() {
    for axis in ["owners", "related", "private", "tokens", "aliases"] {
        let mut exits = Vec::new();
        let mut observations = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut facts = PureFactContext::new();
            let pointer = Address::symbolic(Variable(8_918_100));
            if axis == "private" {
                crate::kernel::set_never_address_taken_locals(
                    (0..count)
                        .map(|index| format!("exit_hidden_{index}").into())
                        .collect(),
                );
            }
            let mut resources = split_credits(2);
            if axis == "aliases" {
                resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                    MemoryRange::new_with_element_width(
                        pointer.clone(),
                        0u32.into(),
                        4u32.into(),
                        1,
                    ),
                ));
            }
            for index in 0..count {
                if axis == "aliases" {
                    facts = facts.assume_condition(
                        ConditionTerm::address_equal(
                            pointer.clone(),
                            Address::symbolic(Variable(8_918_200 + u64::from(index))),
                        ),
                        true,
                    );
                    continue;
                }
                let fact = if axis == "tokens" {
                    ResourceFact::own(Resource::Token {
                        name: "credit".into(),
                        arguments: vec![].into(),
                    })
                } else {
                    let (base, start) = match axis {
                        "related" => (pointer.clone(), index * 8),
                        "private" => (
                            SymbolicMemory::local_pointer(format!("exit_hidden_{index}")),
                            0,
                        ),
                        _ => (Address::symbolic(Variable(8_918_300 + u64::from(index))), 0),
                    };
                    ResourceFact::own_memory(MemoryRange::new_with_element_width(
                        base,
                        start.into(),
                        (start + 4).into(),
                        1,
                    ))
                };
                resources = resources.unchecked_with_fact(fact);
            }
            resources.synchronize_memory_equalities(&facts);
            let caller = ExecutionState::new().with_resource_context(resources);
            let function = Arc::new(program_function(
                ProgramType::Void,
                "bounded_exit",
                vec![],
                program_skip(),
            ));
            let receipt = capture_checked_boundary_resource_transfer(
                &caller,
                function.clone(),
                &[],
                &facts,
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap()
            .unwrap();
            let (completed, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast =
                    crate::kernel::search::FastOperationScope::enter("constructed function exit");
                complete_partition(
                    &caller,
                    &function,
                    &receipt,
                    StatementOutcome::Return {
                        value: ProgramValue::Void.into(),
                        state: Box::new(caller.clone()),
                    },
                    &facts,
                )
            });
            assert!(Arc::ptr_eq(
                &caller.resources().storage,
                &completed.resources().storage
            ));
            exits.push(work);
            // Private-address filtering has separate producer-maintenance
            // coverage; this measures observation of the visible partition.
            if axis != "private" {
                let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "constructed partition observation",
                    );
                    completed
                        .resources()
                        .observable_facts_assuming_valid(&facts)
                });
                assert_eq!(observed.len(), 1);
                observations.push(work);
            }
        }
        assert!(exits[2] <= exits[0] + 96, "{axis} exit: {exits:?}");
        if axis != "private" {
            assert!(
                observations[2] <= observations[0] + 32,
                "{axis} observation: {observations:?}"
            );
        }
    }
}
