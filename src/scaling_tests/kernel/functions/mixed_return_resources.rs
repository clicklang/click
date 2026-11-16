use super::*;

#[test]
fn mixed_return_composition_ignores_related_aliases_and_retained_owners() {
    for axis in ["aliases", "related owners", "unrelated owners"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(8_820_000)),
            };
            let other = |id: u32| Pointer::symbolic(Variable(8_830_000 + u64::from(id)));
            let owner = |base, start: u32| {
                ResourceFact::own_memory(MemoryRange::new(base, start.into(), (start + 1).into()))
            };
            let mut facts = PureFactContext::new();
            let mut frame = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_fact(owner(pointer.clone(), 4));
            for index in 0..count {
                match axis {
                    "aliases" => {
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(pointer.clone(), other(index)),
                            true,
                        )
                    }
                    "related owners" => {
                        frame = frame.unchecked_with_fact(owner(pointer.clone(), index * 4 + 8))
                    }
                    _ => frame = frame.unchecked_with_fact(owner(other(index), 0)),
                }
            }
            frame.synchronize_memory_equalities(&facts);
            let borrowed = owner(pointer, 0);
            let produced = owner(other(1_000), 0);
            let evaluated = EvaluatedReturnResources::new(&facts)
                .admit(produced.clone(), ReturnOwnershipOrigin::Description, &facts)
                .unwrap()
                .admit(borrowed.clone(), ReturnOwnershipOrigin::EntryBorrow, &facts)
                .unwrap();
            let ((result, occurrences), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _operation = crate::kernel::search::FastOperationScope::enter(
                        "mixed borrowed/produced return",
                    );
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(result.facts().len(), frame.facts().len() + 2);
            assert_eq!(
                result.owned_fact_for_occurrence(occurrences[0].destination),
                Some(&produced)
            );
            assert_eq!(
                result.owned_fact_for_occurrence(occurrences[1].destination),
                Some(&borrowed)
            );
            assert_eq!(occurrences[0].source, evaluated.occurrences[0].source);
            assert_eq!(occurrences[1].source, evaluated.occurrences[1].source);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 48),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn projecting_equal_return_descriptions_uses_selected_occurrences() {
    let mut samples = Vec::new();
    for count in [4_usize, 16, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let ticket = ResourceFact::own_token("repeated_return_ticket".into(), vec![]);
        let evaluated = (0..count).fold(EvaluatedReturnResources::new(&facts), |evaluated, _| {
            evaluated
                .admit(ticket.clone(), ReturnOwnershipOrigin::Description, &facts)
                .unwrap()
        });
        let (destination, transfers) = evaluated
            .restore_entry_borrows(
                ResourceContext::new_with_equalities(&facts),
                ReturnResourceComposition::ValidateDescriptions,
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        let state = ExecutionState::new();
        let ((projected, work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let _operation = crate::kernel::search::FastOperationScope::enter(
                    "selected returned occurrence projections",
                );
                project_return_resource_cores(
                    &evaluated.resources,
                    &transfers,
                    &FlatReturnBodies::default(),
                    &[],
                    &state,
                    &facts,
                    &destination,
                )
                .unwrap()
            })
        });
        assert_eq!(projected.len(), count);
        for (projected, transfer) in projected.iter().zip(&transfers) {
            assert_eq!(projected.destination, transfer.destination);
        }
        samples.push((count, work, maps));
    }
    for (count, work, maps) in &samples {
        let growth = count / samples[0].0;
        assert!(
            *work <= samples[0].1 * growth * 4 + count * 16,
            "{samples:?}"
        );
        assert!(*maps <= samples[0].2 * growth * 4, "{samples:?}");
    }
}

#[test]
fn consumed_scalar_return_ignores_aliases_and_retained_owners() {
    use crate::kernel::program_expression::{int32_literal, variable};
    for axis in [
        "aliases",
        "same block aliases",
        "related owners",
        "unrelated owners",
    ] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(8_870_000)),
            };
            let other = |id| {
                if axis == "same block aliases" {
                    Pointer {
                        block: pointer.block.clone(),
                        offset: PointerOffsetTerm::Variable(Variable(8_870_001 + u64::from(id))),
                    }
                } else {
                    Pointer::symbolic(Variable(8_870_001 + u64::from(id)))
                }
            };
            let owner = |base, start: u32| {
                ResourceFact::own_memory(MemoryRange::new(base, start.into(), (start + 1).into()))
            };
            let cell = owner(pointer.clone(), 0);
            let mut facts = PureFactContext::new();
            let mut caller =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(cell.clone());
            let function = super::tests::scalar_transfer_contract(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            ));
            // Entry discovery is legacy work, outside this return operation.
            // Extend its checked partition with disjoint retained owners and
            // fork its facts before measuring classification and restoration.
            let transfer = super::tests::prepare_scalar_transfer(
                &function,
                pointer.clone(),
                caller.clone(),
                &facts,
            );
            let mut frame = transfer.caller_resources_after_requirements.clone();
            for index in 0..count {
                match axis {
                    "aliases" | "same block aliases" => {
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(pointer.clone(), other(index)),
                            true,
                        )
                    }
                    "related owners" => {
                        let fact = owner(pointer.clone(), index + 2);
                        caller = caller.unchecked_with_fact(fact.clone());
                        frame = frame.unchecked_with_fact(fact)
                    }
                    _ => {
                        let fact = owner(other(index), 0);
                        caller = caller.unchecked_with_fact(fact.clone());
                        frame = frame.unchecked_with_fact(fact);
                    }
                }
            }
            caller.synchronize_memory_equalities(&facts);
            frame.synchronize_memory_equalities(&facts);
            let selected = transfer
                .consumed_cell_returns
                .get(0)
                .expect("explicit scalar transfer");
            let evaluated = EvaluatedReturnResources::new(&facts)
                .admit(
                    cell.clone(),
                    ReturnOwnershipOrigin::ConsumedCell(selected),
                    &facts,
                )
                .unwrap();
            let ((result, transfers), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "consumed scalar return composition",
                    );
                    let selected_again = ConsumedCellReturns::prepare(
                        function.contract_interface(),
                        transfer.stable_view_plan.as_ref().unwrap(),
                        &caller,
                    )
                    .get(0)
                    .unwrap();
                    assert_eq!(selected_again, selected);
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(transfers[0].consumed_input, Some(selected.input));
            assert_eq!(
                result.owned_fact_for_occurrence(transfers[0].destination),
                Some(&cell)
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 48),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn mixed_occurrence_transfers_ignore_ambient_aliases_and_owners() {
    for axis in ["aliases", "same block aliases", "owners"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let function = super::tests::mixed_scalar_contract(false, false);
            let state = super::tests::mixed_scalar_state();
            let mut facts = PureFactContext::new();
            let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
            let pointer = Pointer::symbolic(Variable(8_880_000));
            let mut caller = state.resources().clone();
            let mut frame = transfer.caller_resources_after_requirements.clone();
            for index in 0..count {
                let other = Pointer::symbolic(Variable(8_890_000 + u64::from(index)));
                if axis == "owners" {
                    let fact =
                        ResourceFact::own_memory(MemoryRange::new(other, 0u32.into(), 1u32.into()));
                    caller = caller.unchecked_with_fact(fact.clone());
                    frame = frame.unchecked_with_fact(fact);
                } else {
                    let alias = if axis == "same block aliases" {
                        Pointer {
                            block: pointer.block.clone(),
                            offset: PointerOffsetTerm::Variable(Variable(
                                8_890_000 + u64::from(index),
                            )),
                        }
                    } else {
                        other
                    };
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(pointer.clone(), alias),
                        true,
                    );
                }
            }
            caller.synchronize_memory_equalities(&facts);
            frame.synchronize_memory_equalities(&facts);
            let evaluated =
                super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
            let ((destination, mappings), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "mixed occurrence transfers",
                    );
                    let selected = ConsumedCellReturns::prepare(
                        function.contract_interface(),
                        transfer.stable_view_plan.as_ref().unwrap(),
                        &caller,
                    );
                    assert_eq!(selected, transfer.consumed_cell_returns);
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(destination.facts().len(), frame.facts().len() + 4);
            assert_eq!(
                mappings
                    .iter()
                    .filter(|mapping| mapping.consumed_input.is_some())
                    .count(),
                2
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 96),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn selected_scalar_transfers_scale_with_the_return_delta() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let mut samples = Vec::new();
    for count in [4_usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let base = super::tests::scalar_transfer_contract(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ));
        let pointer = Pointer::symbolic(Variable(8_900_000));
        let owner =
            |pointer| ResourceFact::own_memory(MemoryRange::new(pointer, 0u32.into(), 1u32.into()));
        let mut plan = super::tests::prepare_scalar_transfer(
            &base,
            pointer.clone(),
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(pointer)),
            &facts,
        )
        .stable_view_plan
        .unwrap();
        let mut parameters = Vec::new();
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut pieces = Vec::new();
        for index in 0..count {
            let name = format!("cell_{index}");
            let segment =
                MemorySegment::new(variable(name.as_str()), int32_literal(0), int32_literal(1));
            parameters.push(program_parameter(name.as_str(), ProgramType::Int32Pointer));
            inputs.push(
                ResourceSpec::owned_memory(segment.clone())
                    .with_role(ResourceTransferRole::Consume),
            );
            outputs.push(
                ResourceSpec::owned_memory(segment)
                    .with_role(ResourceTransferRole::Produce)
                    .with_state_source(ResourceStateSource::Post),
            );
            pieces.push(owner(Pointer::symbolic(Variable(8_901_000 + index as u64))));
        }
        let function = program_function(
            ProgramType::Void,
            "return_delta",
            parameters,
            program_skip(),
        )
        .with_resource_summary(inputs, outputs);
        // Assemble the explicit disjoint entry partition without timing legacy
        // discovery. Retain the producer's IDs for both independent contexts.
        let (caller, input_occurrences) = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts_and_occurrences(pieces.clone());
        plan.transferred_ownership = input_occurrences
            .iter()
            .enumerate()
            .map(|(index, (fact, _))| CheckedResourceFact {
                fact: fact.clone(),
                role: ResourceTransferRole::Consume,
                state_source: ResourceStateSource::Entry,
                clause_position: None,
                section_index: Some(index),
                selected_mutex_source: None,
            })
            .collect();
        plan.transferred_ownership_sources = input_occurrences
            .iter()
            .map(|(_, source)| Some(*source))
            .collect();
        let (resources, emitted) = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts_and_occurrences(pieces);
        let mut evaluated = EvaluatedReturnResources {
            resources,
            occurrences: emitted
                .into_iter()
                .map(|(_, source)| EvaluatedReturnOccurrence {
                    source,
                    origin: ReturnOwnershipOrigin::Description,
                })
                .collect(),
        };
        let (((destination, mappings), work), maps) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let _fast =
                        crate::kernel::search::FastOperationScope::enter("selected return delta");
                    let transfers =
                        ConsumedCellReturns::prepare(function.contract_interface(), &plan, &caller);
                    for (index, occurrence) in evaluated.occurrences.iter_mut().enumerate() {
                        occurrence.origin =
                            ReturnOwnershipOrigin::ConsumedCell(transfers.get(index).unwrap());
                    }
                    evaluated
                        .restore_entry_borrows(
                            ResourceContext::new_with_equalities(&facts),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                })
            });
        assert_eq!(mappings.len(), count);
        for (index, mapping) in mappings.iter().enumerate() {
            assert_eq!(mapping.consumed_input, Some(input_occurrences[index].1));
            assert_eq!(mapping.source, evaluated.occurrences[index].source);
            assert_eq!(
                destination.owned_fact_for_occurrence(mapping.destination),
                evaluated
                    .resources
                    .owned_fact_for_occurrence(mapping.source)
            );
        }
        samples.push((count, work, maps));
    }
    for (count, work, maps) in &samples {
        let growth = count / samples[0].0;
        assert!(
            *work <= samples[0].1 * growth * 4 + count * 32,
            "{samples:?}"
        );
        assert!(*maps <= samples[0].2 * growth * 4, "{samples:?}");
    }
}

#[test]
fn fixed_range_transfer_work_ignores_length_aliases_and_retained_owners() {
    use crate::kernel::program_expression::{int32_literal, variable};
    for axis in ["length", "aliases", "same block aliases", "owners"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut facts = PureFactContext::new();
            let pointer = Pointer::symbolic(Variable(8_920_000));
            let base = super::tests::scalar_transfer_contract(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            ));
            let mut plan = super::tests::prepare_scalar_transfer(
                &base,
                pointer.clone(),
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
                    ResourceFact::own_memory(MemoryRange::new(
                        pointer.clone(),
                        0u32.into(),
                        1u32.into(),
                    )),
                ),
                &facts,
            )
            .stable_view_plan
            .unwrap();
            let end = if axis == "length" {
                count * 1024 + 2
            } else {
                6
            };
            let owner = |base, start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base,
                    start.into(),
                    end.into(),
                    8,
                ))
            };
            let output = owner(pointer.clone(), 2, end);
            let (mut caller, original) = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_facts_and_occurrences([owner(pointer.clone(), 0, end + 2)]);
            plan.transferred_ownership[0].fact = output.clone();
            plan.transferred_ownership_sources = vec![Some(original[0].1)];
            let mut frame = ResourceContext::new_with_equalities(&facts).unchecked_with_facts([
                owner(pointer.clone(), 0, 2),
                owner(pointer.clone(), end, end + 2),
            ]);
            // The selected reservation is this explicit interval difference.
            // Legacy entry discovery is outside the operation being measured.
            for index in 0..count {
                let other = Pointer::symbolic(Variable(8_921_000 + u64::from(index)));
                match axis {
                    "aliases" | "same block aliases" => {
                        let alias = if axis == "aliases" {
                            other
                        } else {
                            Pointer {
                                block: pointer.block.clone(),
                                offset: PointerOffsetTerm::Variable(Variable(
                                    8_921_000 + u64::from(index),
                                )),
                            }
                        };
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(pointer.clone(), alias),
                            true,
                        );
                    }
                    "owners" => {
                        let fact = owner(other, 0, 1);
                        caller = caller.unchecked_with_fact(fact.clone());
                        frame = frame.unchecked_with_fact(fact);
                    }
                    _ => {}
                }
            }
            caller.synchronize_memory_equalities(&facts);
            frame.synchronize_memory_equalities(&facts);
            let segment = MemorySegment::new(variable("p"), int32_literal(2), int32_literal(end))
                .with_element_width(8);
            let function = super::tests::fixed_range_contract(
                ProgramType::Int64Pointer,
                segment.clone(),
                segment,
            );
            let (resources, inserted) = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_facts_and_occurrences([output.clone()]);
            let mut evaluated = EvaluatedReturnResources {
                resources,
                occurrences: vec![EvaluatedReturnOccurrence {
                    source: inserted[0].1,
                    origin: ReturnOwnershipOrigin::Description,
                }],
            };
            let ((result, mappings), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "fixed range ownership return",
                    );
                    let selected =
                        ConsumedCellReturns::prepare(function.contract_interface(), &plan, &caller)
                            .get(0)
                            .unwrap();
                    evaluated.occurrences[0].origin = ReturnOwnershipOrigin::ConsumedCell(selected);
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(mappings[0].consumed_input, Some(original[0].1));
            assert_eq!(
                result.owned_fact_for_occurrence(mappings[0].destination),
                Some(&output)
            );
            assert_eq!(result.facts().len(), frame.facts().len() + 1);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 96),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn fresh_allocation_returns_ignore_creation_history_aliases_and_retained_owners() {
    for axis in ["history", "aliases", "owners"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let (caller, entry, post, pointer) = super::fresh_allocation_tests::allocated_call(16);
            let creator = checked_allocation_creator(&caller, &entry).unwrap();
            let mut events = post.population_effects.creation.as_ref().unwrap().clone();
            let mut frame = caller.resources().clone();
            let mut facts = PureFactContext::new();
            for index in 0..count {
                match axis {
                    "history" => {
                        events = events.created(PointerBlock::Heap(8_940_000 + u64::from(index)))
                    }
                    "aliases" => {
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(
                                pointer.clone(),
                                Pointer::symbolic(Variable(8_940_000 + u64::from(index))),
                            ),
                            true,
                        )
                    }
                    _ => {
                        frame =
                            frame.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                                Pointer::symbolic(Variable(8_940_000 + u64::from(index))),
                                0u32.into(),
                                1u32.into(),
                            )))
                    }
                }
            }
            frame.synchronize_memory_equalities(&facts);
            let outputs = super::fresh_allocation_tests::fresh_return_facts(&pointer, 4);
            let mut evaluated = EvaluatedReturnResources::new(&facts);
            for fact in &outputs {
                let fresh =
                    FreshAllocationReturn::from_created_owner(fact, &creator, &events).unwrap();
                evaluated = evaluated
                    .admit(
                        fact.clone(),
                        ReturnOwnershipOrigin::FreshAllocation(fresh),
                        &facts,
                    )
                    .unwrap();
            }
            let ((result, mappings), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "fresh allocation return composition",
                    );
                    for fact in &outputs {
                        assert!(
                            FreshAllocationReturn::from_created_owner(fact, &creator, &events)
                                .is_some()
                        );
                        assert!(
                            FreshAllocationReturn::from_created_owner(
                                fact,
                                caller.population_effects.creation.as_ref().unwrap(),
                                &events
                            )
                            .is_none()
                        );
                    }
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::BodyAllocations {
                                creator: &creator,
                                events: &events,
                            },
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(result.facts().len(), frame.facts().len() + 2);
            for (index, mapping) in mappings.iter().enumerate() {
                assert!(mapping.fresh_allocation.is_some());
                assert_eq!(
                    result.owned_fact_for_occurrence(mapping.destination),
                    Some(&outputs[index])
                );
            }
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn fresh_allocation_return_work_scales_with_selected_return_pieces() {
    let mut samples = Vec::new();
    for count in [4_usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let (caller, entry, post, pointer) =
            super::fresh_allocation_tests::allocated_call(count as u32 * 4);
        let creator = checked_allocation_creator(&caller, &entry).unwrap();
        let events = post.population_effects.creation.as_ref().unwrap();
        let mut pieces = (0..count as u32)
            .map(|index| {
                ResourceFact::own_memory(MemoryRange::new(
                    pointer.clone(),
                    index.into(),
                    (index + 1).into(),
                ))
            })
            .collect::<Vec<_>>();
        pieces.push(ResourceFact::own_allocation(pointer, count as u32 * 4));
        let (resources, inserted) = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts_and_occurrences(pieces);
        let mut evaluated = EvaluatedReturnResources {
            resources,
            occurrences: inserted
                .iter()
                .map(|(_, source)| EvaluatedReturnOccurrence {
                    source: *source,
                    origin: ReturnOwnershipOrigin::Description,
                })
                .collect(),
        };
        let (((result, mappings), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let _fast = crate::kernel::search::FastOperationScope::enter(
                    "fresh allocation selected return delta",
                );
                for ((fact, _), occurrence) in inserted.iter().zip(&mut evaluated.occurrences) {
                    occurrence.origin = ReturnOwnershipOrigin::FreshAllocation(
                        FreshAllocationReturn::from_created_owner(fact, &creator, events).unwrap(),
                    );
                }
                evaluated
                    .restore_entry_borrows(
                        caller.resources().clone(),
                        ReturnResourceComposition::BodyAllocations {
                            creator: &creator,
                            events,
                        },
                        &facts,
                    )
                    .unwrap()
                    .finish(&facts)
                    .unwrap()
            })
        });
        assert_eq!(mappings.len(), count + 1);
        for ((fact, source), mapping) in inserted.iter().zip(&mappings) {
            assert_eq!(mapping.source, *source);
            assert_eq!(
                result.owned_fact_for_occurrence(mapping.destination),
                Some(fact)
            );
        }
        samples.push((count, work, maps));
    }
    for (count, work, maps) in &samples {
        let growth = count / samples[0].0;
        assert!(
            *work <= samples[0].1 * growth * 4 + count * 32,
            "{samples:?}"
        );
        assert!(*maps <= samples[0].2 * growth * 4, "{samples:?}");
    }
}

#[test]
fn flat_return_body_consumers_scale_with_output_and_ignore_ambient_state() {
    for axis in ["outputs", "owners", "aliases", "definitions"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Pointer::symbolic(Variable(8_839_001));
            let mut facts = PureFactContext::new();
            let mut frame = ResourceContext::new();
            let mut definitions = vec![tests::flat_body_definition(
                "selected",
                &pointer,
                if axis == "outputs" { count } else { 1 },
            )];
            for index in 0..count {
                let other = Pointer::symbolic(Variable(8_839_100 + u64::from(index)));
                match axis {
                    "owners" => {
                        frame = frame.unchecked_with_fact(ResourceFact::own_memory(
                            MemoryRange::new(other, 0u32.into(), 1u32.into()),
                        ))
                    }
                    "aliases" => {
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(pointer.clone(), other),
                            true,
                        )
                    }
                    "definitions" => definitions.push(tests::flat_body_definition(
                        &format!("unused_{index:04}"),
                        &other,
                        1,
                    )),
                    _ => {}
                }
            }
            definitions.sort_by(|a, b| a.name().cmp(b.name()));
            frame.synchronize_memory_equalities(&facts);
            let evaluated = EvaluatedReturnResources::new(&facts)
                .admit(
                    ResourceFact::own_composite("selected".into(), vec![]),
                    ReturnOwnershipOrigin::Description,
                    &facts,
                )
                .unwrap();
            let state = ExecutionState::new();
            let bodies = FlatReturnBodies::construct(&evaluated, &definitions, &state, &facts);
            assert_eq!(bodies.0.len(), 1);
            let prepared = evaluated
                .restore_entry_borrows(
                    frame,
                    ReturnResourceComposition::RestoreEntryBorrows,
                    &facts,
                )
                .unwrap();
            let (destination, transfers) = prepared.finish(&facts).unwrap();
            let (projected, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _operation =
                    crate::kernel::search::FastOperationScope::enter("carried flat return body");
                project_return_resource_cores(
                    &evaluated.resources,
                    &transfers,
                    &bodies,
                    &[],
                    &state,
                    &facts,
                    &destination,
                )
                .unwrap()
            });
            assert_eq!(
                projected[0].expansion.len(),
                if axis == "outputs" {
                    count as usize + 1
                } else {
                    2
                }
            );
            samples.push(work);
        }
        if axis == "outputs" {
            assert!(samples[2] <= samples[0] * 24 + 64, "{axis}: {samples:?}");
        } else {
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 48),
                "{axis}: {samples:?}"
            );
        }
    }
}

#[test]
fn flat_body_admission_ignores_retained_owners_and_aliases_on_hits_refusals_and_misses() {
    for axis in ["owners", "related owners", "aliases", "cold", "general"] {
        for overlap in [false, true] {
            let mut samples = Vec::new();
            for count in [4_u32, 16, 64] {
                let _session = crate::kernel::VerificationSession::enter();
                let pointer = Pointer::symbolic(Variable(8_839_500));
                let mut facts = PureFactContext::new();
                let owner = |base, start: u32| {
                    ResourceFact::own_memory(MemoryRange::new(
                        base,
                        start.into(),
                        (start + 1).into(),
                    ))
                };
                let mut frame =
                    ResourceContext::new().unchecked_with_fact(owner(pointer.clone(), 4));
                for index in 0..count {
                    let other = Pointer::symbolic(Variable(8_839_600 + u64::from(index)));
                    match axis {
                        "aliases" => {
                            facts = facts.assume_condition(
                                ConditionTerm::pointer_equal(pointer.clone(), other),
                                true,
                            )
                        }
                        "related owners" => {
                            frame =
                                frame.unchecked_with_fact(owner(pointer.clone(), index * 2 + 10))
                        }
                        _ => frame = frame.unchecked_with_fact(owner(other, 0)),
                    }
                }
                if overlap {
                    frame = frame.unchecked_with_fact(owner(pointer.clone(), 0));
                }
                if axis == "general" {
                    frame = frame.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                        pointer.clone(),
                        1000u32.into(),
                        MachineTerm::Variable(Variable(8_839_599)),
                    )));
                }
                if axis != "cold" {
                    frame.synchronize_memory_equalities(&facts);
                }
                let (evaluated, bodies) =
                    super::tests::constructed_flat_return(&pointer, 1, &facts);
                let source = evaluated.occurrences[0].source;
                let body = bodies.get(source).unwrap();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "indexed flat composite frontier",
                    );
                    let result = frame.admit_returned_flat_body(body, &facts);
                    if axis == "cold" || axis == "general" {
                        assert!(matches!(result, FlatBodyAdmission::Unsupported));
                    } else {
                        assert!(matches!(result, FlatBodyAdmission::Conflict { .. }) == overlap);
                        if !overlap {
                            assert!(matches!(result, FlatBodyAdmission::Admitted));
                        }
                        let error = produced_composite_frontier_conflict(
                            &frame,
                            std::iter::once((
                                evaluated
                                    .resources
                                    .owned_fact_for_occurrence(source)
                                    .unwrap(),
                                Some(body),
                            )),
                            &[],
                            &Memory::new(),
                            &facts,
                        );
                        assert_eq!(error.is_some(), overlap);
                    }
                });
                samples.push(work);
            }
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 64),
                "{axis}, overlap={overlap}: {samples:?}"
            );
        }
    }
}

#[test]
fn flat_body_admission_scales_with_the_constructed_frontier() {
    let mut samples = Vec::new();
    for count in [4_u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let pointer = Pointer::symbolic(Variable(8_839_800));
        let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(
                pointer.clone(),
                1000u32.into(),
                1001u32.into(),
            )),
        );
        frame.synchronize_memory_equalities(&facts);
        let (evaluated, bodies) = super::tests::constructed_flat_return(&pointer, count, &facts);
        let body = bodies.get(evaluated.occurrences[0].source).unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.admit_returned_flat_body(body, &facts)
        });
        assert!(matches!(result, FlatBodyAdmission::Admitted));
        samples.push(work);
    }
    assert!(samples[2] <= samples[0] * 20 + 64, "frontier: {samples:?}");
}
