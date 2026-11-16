use super::*;

fn owner(pointer: Pointer, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(pointer, start.into(), end.into()))
}

#[test]
fn mixed_composition_restores_symbolic_borrows_and_keeps_emitted_occurrence_order() {
    let facts = PureFactContext::new();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(8_810_000)),
    };
    let borrow = owner(pointer.clone(), 0, 1);
    let produced = owner(Pointer::symbolic(Variable(8_810_001)), 0, 1);
    let parent =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(pointer, 4, 5));
    parent.synchronize_memory_equalities(&facts);
    for produced_first in [false, true] {
        let (outputs, entry_borrows) = if produced_first {
            (vec![produced.clone(), borrow.clone()], vec![false, true])
        } else {
            (vec![borrow.clone(), produced.clone()], vec![true, false])
        };
        let evaluated = outputs.iter().cloned().zip(entry_borrows).fold(
            EvaluatedReturnResources::new(&facts),
            |evaluated, (fact, entry_borrow)| evaluated.admit(fact, entry_borrow, &facts).unwrap(),
        );
        let _operation =
            crate::kernel::search::FastOperationScope::enter("mixed return composition");
        let prepared = evaluated
            .restore_entry_borrows(
                parent.clone(),
                ReturnResourceComposition::RestoreEntryBorrows,
                &facts,
            )
            .unwrap();
        assert!(prepared.frame.contains_exact_representation(&borrow));
        assert_eq!(prepared.pending.facts(), &[produced.clone()]);
        let (context, inserted) = prepared.finish(&facts).unwrap();
        assert_eq!(context.facts().len(), 3);
        assert_eq!(inserted.len(), outputs.len());
        for ((transfer, source), fact) in inserted.iter().zip(&evaluated.occurrences).zip(&outputs)
        {
            assert_eq!(transfer.source, source.source);
            assert_eq!(
                evaluated
                    .resources
                    .owned_fact_for_occurrence(transfer.source),
                Some(fact)
            );
            assert_eq!(
                context.owned_fact_for_occurrence(transfer.destination),
                Some(fact)
            );
        }
        assert_eq!(parent.facts().len(), 1);
    }
}

#[test]
fn raw_description_mode_never_authorizes_restoration_from_a_role_marker() {
    let facts = PureFactContext::new();
    let borrow = owner(Pointer::symbolic(Variable(8_810_010)), 0, 1);
    let parent = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(borrow.clone());
    parent.synchronize_memory_equalities(&facts);
    let descriptions = EvaluatedReturnResources::new(&facts)
        .admit(borrow, true, &facts)
        .unwrap();
    let prepared = descriptions
        .restore_entry_borrows(
            parent,
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(prepared.restored.is_empty());
    assert!(matches!(
        prepared.finish(&facts),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
}

#[test]
fn equal_return_descriptions_keep_distinct_transfers_and_projection_lifetimes() {
    let facts = PureFactContext::new();
    let ticket = ResourceFact::own_token("returned_ticket".into(), vec![]);
    for borrowed_first in [false, true] {
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(ticket.clone(), borrowed_first, &facts)
            .unwrap()
            .admit(ticket.clone(), !borrowed_first, &facts)
            .unwrap();
        let sources = evaluated
            .occurrences
            .iter()
            .map(|entry| entry.source)
            .collect::<Vec<_>>();
        assert_ne!(sources[0], sources[1]);
        for _ in 0..2 {
            let prepared = evaluated
                .restore_entry_borrows(
                    ResourceContext::new_with_equalities(&facts),
                    ReturnResourceComposition::RestoreEntryBorrows,
                    &facts,
                )
                .unwrap();
            let restored = prepared.restored[0].1;
            let (mut destination, transfers) = prepared.finish(&facts).unwrap();
            assert_eq!(transfers[0].source, sources[0]);
            assert_eq!(transfers[1].source, sources[1]);
            assert_ne!(transfers[0].destination, transfers[1].destination);
            assert_eq!(
                transfers[usize::from(!borrowed_first)].destination,
                restored
            );
            let state = ExecutionState::new();
            let projected = project_return_resource_cores(
                &evaluated.resources,
                &transfers,
                &[],
                &state,
                &facts,
                &destination,
            )
            .unwrap();
            assert_eq!(projected.len(), 2);
            let mut views = Vec::new();
            for (projection, transfer) in projected.into_iter().zip(&transfers) {
                assert_eq!(projection.destination, transfer.destination);
                assert_eq!(projection.support, ticket);
                assert_eq!(projection.projected.len(), 1);
                let (next, inserted) = destination
                    .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                        projection.destination,
                        &projection.support,
                        projection.projected,
                        state.memory(),
                    );
                destination = next;
                views.push(inserted[0].1);
            }
            for removed in 0..2 {
                let kept = 1 - removed;
                let child = destination
                    .clone()
                    .without_exact_representation_for_occurrence(transfers[removed].destination)
                    .unwrap();
                assert!(
                    child
                        .owned_fact_for_occurrence(transfers[removed].destination)
                        .is_none()
                );
                assert!(child.view_fact_for_occurrence(views[removed]).is_none());
                assert_eq!(
                    child.owned_fact_for_occurrence(transfers[kept].destination),
                    Some(&ticket)
                );
                assert!(child.view_fact_for_occurrence(views[kept]).is_some());
                assert!(
                    destination
                        .view_fact_for_occurrence(views[removed])
                        .is_some()
                );
            }
        }
        assert_eq!(evaluated.resources.facts().len(), 2);
    }
}
