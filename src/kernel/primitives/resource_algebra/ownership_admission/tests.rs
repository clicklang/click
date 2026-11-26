use super::*;

fn at(id: u64) -> Address {
    Address::symbolic(Variable(8_770_000 + id))
}
fn owner(base: Address, start: u32, end: u32) -> ResourceFact {
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
fn missing_boundary_has_no_successor_and_accepts_its_explicit_premise() {
    let facts = PureFactContext::new();
    let parent =
        ResourceContext::new().unchecked_with_facts([owner(at(0), 0, 4), owner(at(1), 0, 4)]);
    let output = owner(at(2), 0, 4);
    let _fast = crate::kernel::search::FastOperationScope::enter("explicit owner boundary");
    let OwnershipAdmission::Unsupported(required) = parent
        .clone()
        .admit_without_discovery([output.clone()], &facts)
    else {
        panic!("a cold partition must require its missing premise");
    };
    assert_eq!(parent.facts().len(), 2);
    let proven = facts.assume_proposition(*required);
    let (context, inserted) = parent
        .clone()
        .try_compose_checked_ownership_and_occurrences([output.clone()], &proven)
        .unwrap();
    assert_eq!(inserted.len(), 1);
    assert_eq!(
        context.owned_fact_for_occurrence(inserted[0].1),
        Some(&output)
    );
    let changed = parent.unchecked_with_fact(owner(at(3), 0, 4));
    assert!(matches!(
        changed.try_compose_checked_ownership_and_occurrences([output], &proven),
        Err(ResourceContextValidityError::UnestablishedOwnedBoundary(_))
    ));
}

#[test]
fn cold_and_prepared_overlap_conflict_without_search() {
    let facts = PureFactContext::new();
    let parent = ResourceContext::new().unchecked_with_facts([
        owner(at(0), 0, 4),
        owner(at(1), 0, 4),
        guard(),
    ]);
    let _fast = crate::kernel::search::FastOperationScope::enter("cold ownership boundary");
    assert!(matches!(
        parent
            .clone()
            .admit_without_discovery([owner(at(0), 1, 3)], &facts),
        OwnershipAdmission::Conflict(
            ResourceContextValidityError::OverlappingOwnedMemoryResources { .. }
        )
    ));
    parent.synchronize_memory_equalities(&facts);
    assert!(matches!(
        parent
            .clone()
            .admit_without_discovery([owner(at(0), 1, 3)], &facts),
        OwnershipAdmission::Conflict(
            ResourceContextValidityError::OverlappingOwnedMemoryResources { .. }
        )
    ));
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
            .checked_frontier_boundary_conflict(std::slice::from_ref(&held), &facts)
            .unwrap(),
        Some((held.clone(), held.clone())),
    );
    assert!(
        ResourceContext::new()
            .checked_frontier_boundary_conflict(std::slice::from_ref(&held), &facts)
            .unwrap()
            .is_none()
    );
    assert_eq!(parent.facts(), &[held]);
}

#[test]
fn cold_return_boundary_keeps_the_aliased_held_fact_and_parent_partition() {
    let facts = PureFactContext::new()
        .assume_condition(OldConditionTerm::address_equal(at(0), at(1)), true);
    let piece = owner(at(0), 0, 4);
    let parent = ResourceContext::new().unchecked_with_fact(owner(at(1), 4, 8));
    assert!(matches!(
        parent.checked_frontier_boundary_conflict(std::slice::from_ref(&piece), &facts),
        Ok(None)
    ));
    parent.synchronize_memory_equalities(&facts);
    assert!(
        parent
            .checked_frontier_boundary_conflict(std::slice::from_ref(&piece), &facts)
            .unwrap()
            .is_none()
    );
    let held = owner(at(1), 0, 4);
    let branch = parent.clone().unchecked_with_fact(held.clone());
    assert_eq!(
        branch
            .checked_frontier_boundary_conflict(std::slice::from_ref(&piece), &facts)
            .unwrap(),
        Some((piece.clone(), held))
    );
    assert!(
        parent
            .checked_frontier_boundary_conflict(&[piece], &facts)
            .unwrap()
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
    let quantity = OldMachineTerm::Variable(Variable(8_770_099));
    let facts = PureFactContext::new()
        .assume_condition(OldConditionTerm::equal(quantity.clone(), 1u32.into()), true);
    let output = ResourceFact::Own(
        Resource::Memory(MemoryRange::new_with_element_width(
            at(0),
            0u32.into(),
            4u32.into(),
            1,
        )),
        Box::new(quantity.into()),
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
    let aliases = facts.assume_condition(OldConditionTerm::address_equal(at(0), at(1)), true);
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

#[test]
fn explicit_symbolic_boundary_covers_the_actual_partition_and_stays_branch_local() {
    let _session = crate::kernel::VerificationSession::enter();
    let n = OldMachineTerm::Variable(Variable(8_770_210));
    let m = OldMachineTerm::Variable(Variable(8_770_211));
    let span = |a, b| ResourceFact::own_memory(MemoryRange::new_with_element_width(at(0), a, b, 1));
    let left = span(0u32.into(), n.clone());
    let right = span(m.clone(), 16u32.into());
    let output = span(n, m);
    let facts = PureFactContext::new();
    let frame = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts([left.clone(), right.clone()]);
    frame.synchronize_memory_equalities(&facts);
    let _fast = crate::kernel::search::FastOperationScope::enter("explicit symbolic partition");
    let Err(ResourceContextValidityError::UnestablishedOwnedBoundary(required)) = frame
        .clone()
        .try_compose_checked_ownership_and_occurrences([output.clone()], &facts)
    else {
        panic!("two unknown footprints require an explicit relationship");
    };
    let stated = Proposition::ResourceSeparate {
        left: Box::new(output.resource().clone()),
        right: Box::new(Resource::star(
            right.resource().clone(),
            left.resource().clone(),
        )),
    };
    let branch = facts.clone().assume_proposition(stated);
    let (joined, outputs) = frame
        .clone()
        .try_compose_checked_ownership_and_occurrences([output.clone()], &branch)
        .unwrap();
    assert_eq!(
        joined.owned_fact_for_occurrence(outputs[0].1),
        Some(&output)
    );
    assert!(
        frame
            .clone()
            .try_compose_checked_ownership_and_occurrences([output.clone()], &facts)
            .is_err()
    );
    // The emitted goal is ordinary Surface-expressible separation, and its
    // cached conjunction has exactly the current raw-memory footprint.
    let exact = facts.assume_proposition(*required);
    assert!(
        frame
            .clone()
            .try_compose_checked_ownership_and_occurrences([output.clone()], &exact)
            .is_ok()
    );
    let changed = frame.unchecked_with_fact(owner(at(0), 32, 36));
    assert!(matches!(
        changed.try_compose_checked_ownership_and_occurrences([output], &branch),
        Err(ResourceContextValidityError::UnestablishedOwnedBoundary(_))
    ));
}

#[test]
fn private_frame_coverage_is_scoped_to_its_registry_and_defers_to_local_aliases() {
    crate::kernel::set_never_address_taken_locals(std::collections::BTreeSet::from([
        "boundary_private".into(),
    ]));
    let local = crate::kernel::SymbolicMemory::local_pointer("boundary_private");
    let frame = ResourceContext::new().unchecked_with_fact(owner(local.clone(), 0, 4));
    let output = owner(at(90), 0, 4);
    let facts = PureFactContext::new();
    let _fast = crate::kernel::search::FastOperationScope::enter("private owner partition");
    assert!(matches!(
        frame
            .clone()
            .admit_without_discovery([output.clone()], &facts),
        OwnershipAdmission::Admitted { .. }
    ));
    crate::kernel::set_never_address_taken_locals(std::collections::BTreeSet::new());
    assert!(matches!(
        frame
            .clone()
            .admit_without_discovery([output.clone()], &facts),
        OwnershipAdmission::Unsupported(_)
    ));
    let aliased = facts
        .clone()
        .assume_condition(OldConditionTerm::address_equal(at(90), local), true);
    frame.synchronize_memory_equalities(&aliased);
    assert!(matches!(
        frame.admit_without_discovery([output], &aliased),
        OwnershipAdmission::Conflict(_)
    ));
}

#[test]
fn automatic_storage_and_entry_arguments_keep_their_structural_partition() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = |block| Address::new(block, AddressOffset::constant(0));
    let argument = owner(pointer(AddressBase::ExternalArgument), 0, 4);
    let local = owner(pointer(AddressBase::Concrete("local:object".into())), 0, 4);
    let private = owner(pointer(AddressBase::Temporary(8_779_000)), 0, 4);
    let frame = ResourceContext::new().unchecked_with_facts([local.clone(), private.clone()]);
    let _fast =
        crate::kernel::search::FastOperationScope::enter("allocation-class ownership boundary");
    assert!(matches!(
        frame.admit_without_discovery([argument.clone()], &facts),
        OwnershipAdmission::Admitted { .. }
    ));
    let frame = ResourceContext::new().unchecked_with_facts([argument.clone(), private]);
    assert!(matches!(
        frame.admit_without_discovery([local], &facts),
        OwnershipAdmission::Admitted { .. }
    ));
    let global = owner(pointer(AddressBase::Concrete("global:object".into())), 0, 4);
    assert!(matches!(
        ResourceContext::new()
            .unchecked_with_fact(global)
            .admit_without_discovery([argument], &facts),
        OwnershipAdmission::Unsupported(_)
    ));
}

#[test]
fn cold_singleton_and_prepared_aliases_keep_the_selected_held_fact() {
    let facts = PureFactContext::new()
        .assume_condition(OldConditionTerm::address_equal(at(0), at(1)), true);
    let piece = owner(at(0), 0, 4);
    let parent = ResourceContext::new().unchecked_with_fact(owner(at(1), 4, 8));
    let _fast = crate::kernel::search::FastOperationScope::enter("bounded aliased return boundary");
    assert!(matches!(
        parent.admit_returned_frontier(std::slice::from_ref(&piece), &facts),
        FlatBodyAdmission::Admitted
    ));
    parent.synchronize_memory_equalities(&facts);
    assert!(matches!(
        parent.admit_returned_frontier(std::slice::from_ref(&piece), &facts),
        FlatBodyAdmission::Admitted
    ));
    let held = owner(at(1), 0, 4);
    let branch = parent.clone().unchecked_with_fact(held.clone());
    let FlatBodyAdmission::Conflict {
        piece: selected_piece,
        held: selected_held,
    } = branch.admit_returned_frontier(std::slice::from_ref(&piece), &facts)
    else {
        panic!("prepared alias conflict");
    };
    assert_eq!(*selected_piece, piece);
    assert_eq!(*selected_held, held);
    assert!(matches!(
        parent.admit_returned_frontier(&[piece], &facts),
        FlatBodyAdmission::Admitted
    ));
    assert_eq!(parent.facts().len(), 1);
    assert_eq!(branch.facts().len(), 2);
}

#[test]
fn legacy_composition_checks_only_new_ownership_and_keeps_untouched_occurrences() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let unrelated = owner(at(1), 0, 4);
    let (frame, originals) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([unrelated.clone(), owner(at(0), 0, 4)]);
    let _fast = crate::kernel::search::FastOperationScope::enter("legacy composition delta");
    // Adding a token does not re-prove the frame's unknown pointer geometry.
    let token = ResourceFact::own(Resource::Token {
        name: "credit".into(),
        arguments: vec![].into(),
    });
    let result = frame
        .clone()
        .try_compose_with_facts([token.clone(), token.clone()], &facts)
        .unwrap();
    assert_eq!(
        result.owned_fact_for_occurrence(originals[0].1),
        Some(&unrelated)
    );
    assert_eq!(result.facts().len(), 3);
    assert!(result.satisfies_fact(
        &ResourceFact::Own(token.resource().clone(), Box::new(2u32.into())),
        &facts
    ));
    // Raw descriptions still need the relationship to this exact frame.
    assert!(matches!(
        frame.clone().try_compose_with_fact(
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                at(0),
                1u32.into(),
                OldMachineTerm::Variable(Variable(8_770_999)),
                1,
            )),
            &facts
        ),
        Err(ResourceContextValidityError::UnestablishedOwnedBoundary(_))
    ));
    assert!(matches!(
        frame
            .clone()
            .try_compose_with_facts([owner(at(0), 4, 8), owner(at(0), 6, 10)], &facts),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
            | Err(ResourceContextValidityError::UnestablishedOwnedBoundary(_))
    ));
    assert_eq!(
        frame.owned_fact_for_occurrence(originals[0].1),
        Some(&unrelated)
    );
}

#[test]
fn legacy_composition_coalesces_written_neighbors_without_whole_normalization() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let frame = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts([owner(at(0), 0, 4), owner(at(0), 12, 16)]);
    let untouched = frame.first_exact_occurrence(&owner(at(0), 12, 16)).unwrap();
    let _ = take_whole_normalization_facts();
    let _fast = crate::kernel::search::FastOperationScope::enter("written composition neighbors");
    let result = frame
        .clone()
        .try_compose_with_fact(owner(at(0), 4, 8), &facts)
        .unwrap();
    assert!(result.contains_exact_representation(&owner(at(0), 0, 8)));
    assert_eq!(
        result.owned_fact_for_occurrence(untouched),
        Some(&owner(at(0), 12, 16))
    );
    assert_eq!(take_whole_normalization_facts(), 0);
    assert!(matches!(
        ResourceContext::new_with_equalities(&facts)
            .try_compose_with_facts([owner(at(0), 0, 4), owner(at(0), 0, 4)], &facts),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
}
