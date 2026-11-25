use super::*;

#[test]
fn section_read_supply_preserves_zero_and_unknown_owned_quantities() {
    let base = Address {
        base: AddressBase::Heap(8_991_700),
        offset: AddressOffset::Constant(0),
    };
    let range = MemoryRange::new(base.clone(), 0u32.into(), 1u32.into());
    let facts = PureFactContext::new();
    for (quantity, readable) in [
        (OldMachineTerm::constant(0), false),
        (OldMachineTerm::Variable(Variable(8_991_701)), false),
        (OldMachineTerm::constant(1), true),
    ] {
        let supplied = ResourceFact::own_quantity(Resource::Memory(range.clone()), quantity);
        let supply =
            resource_clause_section_supply(&ExecutionState::new(), &[supplied], &[], &facts);
        assert_eq!(supply.permits_memory_read(&base, 4, &facts), readable);
        if readable {
            assert!(supply.flat_owned_memory_ranges().is_empty());
        }
    }
}

#[test]
fn memory_waiter_requires_a_whole_range_supplier() {
    let base = Address {
        base: AddressBase::Concrete("resource-clause-adjacent".to_string()),
        offset: AddressOffset::Constant(0),
    };
    let wide = ResourceFact::view_memory(MemoryRange::new(
        base.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(2),
    ));
    let left = ResourceFact::view_memory(MemoryRange::new(
        base.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    let right = ResourceFact::view_memory(MemoryRange::new(
        base,
        OldMachineTerm::constant(1),
        OldMachineTerm::constant(2),
    ));
    let assumptions = PureFactContext::new();
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![wide.clone()], &mut dependencies, &mut waiters);
    let evaluated = vec![None];
    let mut queued = vec![false];
    let mut pending = VecDeque::new();
    let section_supply = ResourceContext::new().unchecked_with_fact(left.clone());

    assert!(!section_supply.satisfies_fact(&wide, &assumptions));
    resource_clause_enqueue_waiters(
        &left,
        &assumptions,
        &section_supply,
        &evaluated,
        &mut queued,
        &mut pending,
        &dependencies,
        &waiters,
    );
    assert!(pending.is_empty());

    let section_supply = section_supply.unchecked_with_fact(right.clone());
    // The query no longer searches for a composition of adjacent fragments.
    assert!(!section_supply.satisfies_fact(&wide, &assumptions));
    resource_clause_enqueue_waiters(
        &right,
        &assumptions,
        &section_supply,
        &evaluated,
        &mut queued,
        &mut pending,
        &dependencies,
        &waiters,
    );
    assert!(pending.is_empty());

    let section_supply = section_supply.unchecked_with_fact(wide.clone());
    assert!(section_supply.satisfies_fact(&wide, &assumptions));
    resource_clause_enqueue_waiters(
        &wide,
        &assumptions,
        &section_supply,
        &evaluated,
        &mut queued,
        &mut pending,
        &dependencies,
        &waiters,
    );
    assert_eq!(pending, VecDeque::from([0]));
}

/// Same-block disjoint ranges have one real dependency edge apiece.  The
/// interval index must visit those edges, not every waiter sharing the
/// block key.  The exact candidate count is the regression: the old
/// `MemoryBlock` index would produce `size * size` visits here.
#[test]
fn same_block_disjoint_waiters_use_interval_candidates() {
    let base = Address {
        base: AddressBase::Concrete("resource-clause-disjoint".to_string()),
        offset: AddressOffset::Constant(0),
    };
    let samples = [4_usize, 8, 16, 32]
            .into_iter()
            .map(|size| {
                let mut dependencies = vec![Vec::new(); size];
                let mut waiters = ResourceClauseWaiterIndex::default();
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let dependency = ResourceFact::view_memory(MemoryRange::new(
                        base.clone(),
                        OldMachineTerm::constant(start),
                        OldMachineTerm::constant(start + 1),
                    ));
                    resource_clause_register_waiters(
                        index,
                        vec![dependency],
                        &mut dependencies,
                        &mut waiters,
                    );
                }
                let mut candidate_visits = 0;
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let supplied = ResourceFact::view_memory(MemoryRange::new(
                        base.clone(),
                        OldMachineTerm::constant(start),
                        OldMachineTerm::constant(start + 1),
                    ));
                    let candidates = waiters.candidates_for_supplied(&supplied);
                    candidate_visits += candidates.len();
                    assert_eq!(
                        candidates.into_iter().collect::<Vec<_>>(),
                        vec![index],
                        "a disjoint supplied range woke unrelated same-block waiters: size={size} index={index}"
                    );
                }
                (size, candidate_visits)
            })
            .collect::<Vec<_>>();
    assert_eq!(
        samples,
        vec![(4, 4), (8, 8), (16, 16), (32, 32)],
        "same-block interval candidate work should follow actual dependency edges"
    );
}

#[test]
fn comparable_constant_bases_share_interval_space() {
    let block = AddressBase::Concrete("resource-clause-base-aware".to_string());
    let dependency_base = Address {
        base: block.clone(),
        offset: AddressOffset::Constant(0),
    };
    let supplied_base = Address {
        base: block,
        offset: AddressOffset::Constant(8),
    };
    let dependency = ResourceFact::view_memory(MemoryRange::new(
        dependency_base,
        OldMachineTerm::constant(2),
        OldMachineTerm::constant(3),
    ));
    let supplied = ResourceFact::view_memory(MemoryRange::new(
        supplied_base,
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn concrete_memory_waiters_share_physical_byte_space_across_widths() {
    let base = Address {
        base: AddressBase::Concrete("resource-clause-byte-space".to_string()),
        offset: AddressOffset::Constant(0),
    };
    let dependency = ResourceFact::view_memory(MemoryRange::new_with_element_width(
        base.clone(),
        OldMachineTerm::constant(8),
        OldMachineTerm::constant(12),
        1,
    ));
    let supplied = ResourceFact::view_memory(MemoryRange::new_with_element_width(
        base,
        OldMachineTerm::constant(2),
        OldMachineTerm::constant(3),
        4,
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn symbolic_memory_waiters_keep_conservative_block_fallback() {
    let base = Address {
        base: AddressBase::Concrete("resource-clause-symbolic".to_string()),
        offset: AddressOffset::Constant(0),
    };
    let dependency = ResourceFact::view_memory(MemoryRange::new(
        base.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::Variable(Variable(9_901)),
    ));
    let supplied = ResourceFact::view_memory(MemoryRange::new(
        base,
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn concrete_waiter_block_fallback_registers_and_unregisters_symmetrically() {
    let base = Address {
        base: AddressBase::Concrete("resource-clause-fallback-lifetime".to_string()),
        offset: AddressOffset::Constant(0),
    };
    let dependency = ResourceFact::view_memory(MemoryRange::new(
        base.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    let symbolic_supplied = ResourceFact::view_memory(MemoryRange::new(
        base,
        OldMachineTerm::constant(0),
        OldMachineTerm::Variable(Variable(9_902)),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&symbolic_supplied),
        BTreeSet::from([0])
    );
    resource_clause_unregister_waiters(0, &mut dependencies, &mut waiters);
    assert!(
        waiters
            .candidates_for_supplied(&symbolic_supplied)
            .is_empty()
    );
}

#[test]
fn retrying_a_composite_clause_keeps_the_point_of_its_nested_bound_read() {
    use crate::kernel::program_expression::{int32_literal, load, variable};

    let _session = crate::kernel::VerificationSession::enter();
    let slot = SymbolicMemory::global_pointer("retry_bound");
    let target = Address::symbolic(Variable(8_991_709));
    let ty = ProgramType::Int32Pointer;
    let definitions = [
        CompositeResourceDefinition::new(
            "retry_packet",
            vec![
                program_parameter("slot", ty),
                program_parameter("target", ty),
            ],
            None,
            false,
            vec![
                ResourceSpec::owned_memory(MemorySegment::new(
                    variable("slot"),
                    int32_literal(0),
                    int32_literal(1),
                )),
                ResourceSpec::owned_memory(MemorySegment::new(
                    variable("target"),
                    int32_literal(0),
                    load(variable("slot")),
                )),
            ],
            vec![],
        ),
        CompositeResourceDefinition::new(
            "retry_wrapper",
            vec![
                program_parameter("slot", ty),
                program_parameter("target", ty),
            ],
            None,
            false,
            vec![ResourceSpec::composite(
                ResourceAccessMode::Own,
                "retry_packet".into(),
                vec![variable("slot"), variable("target")],
                vec![ty, ty],
            )],
            vec![],
        ),
    ];
    let head = ResourceFact::own_composite(
        "retry_wrapper".into(),
        vec![
            ProgramValue::typed_pointer(slot.clone(), ty),
            ProgramValue::typed_pointer(target.clone(), ty),
        ],
    );
    let state = ExecutionState::new().begin_function_entry_memory();
    let state = state
        .clone()
        .with_function_entry_memory(state.memory().clone().with_block(slot.base.clone(), 4));
    let assumptions = PureFactContext::new();
    let batch = resource_clause_section_supply(
        &state,
        std::slice::from_ref(&head),
        &definitions,
        &assumptions,
    );
    let expected = batch
        .facts()
        .iter()
        .find(|fact| {
            fact.is_view() && fact.memory_range().is_some_and(|range| {
                range.base() == &target
                    && matches!(
                        range.end(), OldMachineTerm::MemoryLoad(at, address, LoadKind::Int32)
                            if **address == slot && at.read_version_id() == state.program_point_id()
                    )
            })
        })
        .expect("the section supplies the nested child using the actual point");
    let (_, added) = resource_clause_supply_with_fact(
        ResourceContext::new_with_equalities(&assumptions),
        head,
        &definitions,
        &state,
        &assumptions,
    );
    assert!(
        added.contains(expected),
        "retry named a different child range"
    );
}
