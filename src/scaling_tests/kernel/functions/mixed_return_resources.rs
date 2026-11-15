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
                .admit(produced.clone(), false, &facts)
                .unwrap()
                .admit(borrowed.clone(), true, &facts)
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
            evaluated.admit(ticket.clone(), false, &facts).unwrap()
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
