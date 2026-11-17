use super::*;

fn at(id: u64) -> Pointer {
    Pointer::symbolic(Variable(8_770_000 + id))
}
fn owner(base: Pointer, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        start.into(),
        end.into(),
        1,
    ))
}
fn guard() -> ResourceFact {
    ResourceFact::own(Resource::MutexGuard(crate::kernel::MutexIdentity {
        epoch: Some(8_770_000),
        mutex: at(9),
    }))
}

#[test]
fn indexed_admission_returns_a_successor_or_conflict_without_discovery() {
    let facts = PureFactContext::new();
    let held = owner(at(0), 4, 8);
    let parent = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held.clone());
    parent.synchronize_memory_equalities(&facts);
    let added = owner(at(0), 0, 4);
    let OwnershipAdmission::Admitted { context, inserted } = parent
        .clone()
        .admit_without_discovery([added.clone()], &facts)
    else {
        panic!("adjacent indexed ownership must be admitted");
    };
    assert_eq!(inserted.len(), 1);
    assert_eq!(inserted[0].0, added);
    assert_eq!(
        context.occurrence(context.storage.next_entry_id - 1),
        inserted[0].1
    );
    assert!(context.contains_exact_representation(&held));
    assert!(matches!(
        parent
            .clone()
            .admit_without_discovery([owner(at(0), 2, 6)], &facts),
        OwnershipAdmission::Conflict(
            ResourceContextValidityError::OverlappingOwnedMemoryResources { .. }
        )
    ));
    assert_eq!(parent.facts().len(), 1);
}

#[test]
fn unsupported_admission_resumes_once_and_retains_occurrences() {
    let facts = PureFactContext::new();
    let parent =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(at(0), 0, 4));
    parent.synchronize_memory_equalities(&facts);
    let symbolic_end = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        at(0),
        4u32.into(),
        MachineTerm::Variable(Variable(8_770_100)),
        1,
    ));
    let outputs = [owner(at(1), 0, 4), symbolic_end, guard()];
    let yielded = std::cell::Cell::new(0);
    let input = outputs
        .clone()
        .into_iter()
        .inspect(|_| yielded.set(yielded.get() + 1));
    let OwnershipAdmission::Unsupported(pending) =
        parent.clone().admit_without_discovery(input, &facts)
    else {
        panic!("a symbolic extent must remain unsupported");
    };
    assert_eq!(yielded.get(), outputs.len());
    assert_eq!(pending.first_unresolved, pending.first_new + 1);
    let occurrences = pending.inserted.clone();
    let (context, inserted) = pending.resume_legacy_discovery().unwrap();
    assert_eq!(yielded.get(), outputs.len());
    assert_eq!(inserted, occurrences);
    assert_eq!(context.facts().len(), parent.facts().len() + outputs.len());
    for (offset, (fact, occurrence)) in inserted.iter().enumerate() {
        let entry = parent.storage.next_entry_id + offset as u64;
        assert_eq!(context.fact(entry), fact);
        assert_eq!(context.occurrence(entry), *occurrence);
    }
    assert_eq!(parent.facts().len(), 1);
}

#[test]
fn multi_block_cold_overlap_keeps_its_explicit_compatibility_boundary() {
    let facts = PureFactContext::new();
    let parent =
        ResourceContext::new().unchecked_with_facts([owner(at(0), 0, 4), owner(at(1), 0, 4)]);
    let OwnershipAdmission::Unsupported(pending) = parent
        .clone()
        .admit_without_discovery([owner(at(0), 1, 3)], &facts)
    else {
        panic!("cold indexed coverage must not decide an overlap");
    };
    assert!(matches!(
        pending.resume_legacy_discovery(),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
    assert!(
        parent
            .try_compose_with_legacy_discovery_and_occurrences([owner(at(0), 1, 3)], &facts)
            .is_err()
    );
}

#[test]
fn unsupported_batches_preserve_conflict_order_and_later_exclusive_checks() {
    let facts = PureFactContext::new();
    // Stay cold so the first output needs legacy overlap validation, while
    // the second conflicts with an exclusive resource the parent holds.
    let parent = ResourceContext::new()
        .unchecked_with_fact(owner(at(0), 0, 4))
        .unchecked_with_fact(guard())
        .unchecked_with_fact(owner(at(1), 0, 4));
    for (start, end, overlap) in [(1, 3, true), (4, 8, false)] {
        let OwnershipAdmission::Unsupported(pending) = parent
            .clone()
            .admit_without_discovery([owner(at(0), start, end), guard()], &facts)
        else {
            panic!("the unresolved first output must precede later checks");
        };
        let error = pending.resume_legacy_discovery().unwrap_err();
        if overlap {
            assert!(matches!(
                error,
                ResourceContextValidityError::OverlappingOwnedMemoryResources { .. }
            ));
        } else {
            assert_eq!(
                error,
                ResourceContextValidityError::DuplicateOwnedResourceFact(guard())
            );
        }
    }
    // Without deferred memory checks, exclusive conflicts are immediate.
    assert!(matches!(
        parent.admit_without_discovery([guard()], &facts),
        OwnershipAdmission::Conflict(ResourceContextValidityError::DuplicateOwnedResourceFact(_))
    ));
}

#[test]
fn returned_boundary_names_exclusive_conflicts_without_installing_children() {
    let facts = PureFactContext::new();
    let held = guard();
    let parent = ResourceContext::new().unchecked_with_fact(held.clone());
    assert_eq!(
        parent
            .returned_boundary_conflict_with_legacy_discovery(std::slice::from_ref(&held), &facts),
        Some((held.clone(), held.clone())),
    );
    assert!(
        ResourceContext::new()
            .returned_boundary_conflict_with_legacy_discovery(std::slice::from_ref(&held), &facts)
            .is_none()
    );
    assert_eq!(parent.facts(), &[held]);
}

#[test]
fn cold_return_boundary_keeps_the_aliased_held_fact_and_parent_partition() {
    let facts =
        PureFactContext::new().assume_condition(ConditionTerm::pointer_equal(at(0), at(1)), true);
    let piece = owner(at(0), 0, 4);
    let parent = ResourceContext::new().unchecked_with_fact(owner(at(1), 4, 8));
    assert!(
        parent
            .returned_boundary_conflict_with_legacy_discovery(std::slice::from_ref(&piece), &facts)
            .is_none()
    );
    let held = owner(at(1), 0, 4);
    let branch = parent.clone().unchecked_with_fact(held.clone());
    assert_eq!(
        branch
            .returned_boundary_conflict_with_legacy_discovery(std::slice::from_ref(&piece), &facts),
        Some((piece.clone(), held))
    );
    assert!(
        parent
            .returned_boundary_conflict_with_legacy_discovery(&[piece], &facts)
            .is_none()
    );
    assert_eq!(parent.facts().len(), 1);
    assert_eq!(branch.facts().len(), 2);
}

#[test]
fn checked_output_composition_carries_the_sources_occurrences_and_projections() {
    let facts = PureFactContext::new();
    let owned = owner(at(0), 0, 4);
    let viewed = ResourceFact::view_memory(owned.memory_own_range().unwrap().clone());
    let (outputs, inserted) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([owned.clone()]);
    let source = inserted[0].1;
    let outputs = outputs.unchecked_with_supported_facts(&owned, [viewed.clone()]);
    let frame =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(at(0), 4, 8));
    let joined = frame.compose_checked_outputs(&outputs, &facts).unwrap();
    assert_eq!(joined.owned_fact_for_occurrence(source), Some(&owned));
    let consumed = joined
        .clone()
        .without_exact_representation_for_occurrence(source)
        .unwrap();
    assert!(!consumed.contains_exact_representation(&viewed));
    assert!(joined.compose_checked_outputs(&outputs, &facts).is_err());
    let conflicting_frame =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(at(0), 3, 8));
    assert!(
        conflicting_frame
            .compose_checked_outputs(&outputs, &facts)
            .is_err()
    );
}

#[test]
fn certified_symbolic_quantities_use_empty_frame_and_block_boundaries() {
    let quantity = MachineTerm::Variable(Variable(8_770_099));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(quantity.clone(), 1u32.into()), true);
    let output = ResourceFact::Own(
        Resource::Memory(MemoryRange::new_with_element_width(
            at(0),
            0u32.into(),
            4u32.into(),
            1,
        )),
        Box::new(quantity),
    );
    for retained in [
        ResourceFact::own_composite("frame".into(), Vec::new()),
        owner(at(1), 0, 4),
    ] {
        let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(retained);
        let _fast = crate::kernel::search::FastOperationScope::enter(
            "certified symbolic group beside an absent block",
        );
        let next = frame
            .try_compose_certified_group_into_valid_context_delaying_normalization(
                [output.clone()],
                &facts,
            )
            .unwrap();
        assert!(next.contains_exact_representation(&output));
    }
    let aliases = facts.assume_condition(ConditionTerm::pointer_equal(at(0), at(1)), true);
    let frame =
        ResourceContext::new_with_equalities(&aliases).unchecked_with_fact(owner(at(1), 0, 4));
    assert!(
        frame
            .try_compose_certified_group_into_valid_context_delaying_normalization(
                [output],
                &aliases,
            )
            .is_err(),
        "an empty exact block bucket must retain cross-block alias checks"
    );
}
