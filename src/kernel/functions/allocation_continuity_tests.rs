use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType, VerificationSession};

/// [`allocation_continuity`] of two 32-bit sizes.
fn int32_continuity(
    input_base: &Address,
    input_bytes: &OldMachineTerm,
    output_base: &Address,
    output_bytes: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> AllocationContinuity {
    allocation_continuity(
        input_base,
        &AllocationSize::int32(input_bytes.clone()),
        output_base,
        &AllocationSize::int32(output_bytes.clone()),
        assumptions,
    )
}

/// Two sizes of different formats are never one allocation's (D5): a pair
/// at one base, or at bases not proven distinct (two external pointers), is
/// refused rather than compared, and distinct blocks stay distinct. Two 64-bit sizes compare
/// at 64 bits.
#[test]
fn continuity_refuses_allocation_sizes_of_different_formats() {
    let base = Address::new(AddressBase::Heap(930_200), AddressOffset::constant(0));
    let other = Address::new(AddressBase::Heap(930_201), AddressOffset::constant(0));
    let count = OldMachineTerm::Variable(Variable(930_202));
    let wide = AllocationSize::new(
        OldMachineTerm::uint64_multiply(count.clone(), OldMachineTerm::uint64_constant(4)),
        AllocationSizeKind::UInt64,
    );
    let narrow = AllocationSize::int32(OldMachineTerm::constant(16));
    let assumptions = PureFactContext::new();
    for (input, output) in [(&wide, &narrow), (&narrow, &wide)] {
        assert_eq!(
            allocation_continuity(&base, input, &base, output, &assumptions),
            AllocationContinuity::CrossKind,
        );
        assert_eq!(
            allocation_continuity(
                &external_pointer(930_203),
                input,
                &external_pointer(930_205),
                output,
                &assumptions,
            ),
            AllocationContinuity::CrossKind,
        );
        assert_eq!(
            allocation_continuity(&base, input, &other, output, &assumptions),
            AllocationContinuity::Distinct,
        );
    }
    assert_eq!(
        allocation_continuity(&base, &wide, &base, &wide, &assumptions),
        AllocationContinuity::Same,
    );
    let other_wide = AllocationSize::new(
        OldMachineTerm::uint64_multiply(
            OldMachineTerm::Variable(Variable(930_204)),
            OldMachineTerm::uint64_constant(4),
        ),
        AllocationSizeKind::UInt64,
    );
    assert!(matches!(
        allocation_continuity(&base, &wide, &base, &other_wide, &assumptions),
        AllocationContinuity::Undecided(OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::Equal,
            ..
        }),
    ));
}

#[test]
fn preserved_fold_can_continue_an_allocation_loaded_from_another_block() {
    use crate::kernel::program_expression::{int32_literal, typed_load, variable};

    let slot_type = ProgramType::Int32PointerPointer;
    let function = program_function(
        ProgramType::Void,
        "unused",
        vec![],
        program_return(program_void_value()),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "descriptor",
        vec![program_parameter("slot", slot_type)],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(
                MemorySegment::new(variable("slot"), int32_literal(0), int32_literal(1))
                    .with_element_width(ProgramType::Int32Pointer.byte_width()),
            ),
            ResourceSpec::token(
                ResourceAccessMode::Own,
                ResourceFact::ALLOCATION_RESOURCE_NAME.into(),
                vec![
                    typed_load(variable("slot"), ProgramType::Int32Pointer),
                    int32_literal(4),
                ],
                vec![ProgramType::Int32Pointer, ProgramType::Int32],
            ),
        ],
        vec![],
    )]);
    let heap = |id| Address::new(AddressBase::Heap(id), AddressOffset::constant(0));
    let consumed = heap(934_000);
    let slot = heap(934_001);
    let bytes = OldMachineTerm::constant(4);
    let memory = SymbolicMemory::new()
        .with_heap_allocation_claim(consumed.clone(), AllocationSize::int32(bytes.clone()))
        .expect("live input allocation")
        .with_heap_allocation_claim(
            slot.clone(),
            AllocationSize::int32(OldMachineTerm::constant(
                ProgramType::Int32Pointer.byte_width(),
            )),
        )
        .expect("live descriptor")
        .store(slot.clone(), ProgramValue::pointer(consumed.clone()));
    let state = ExecutionState::new().with_memory(memory.clone());
    let input = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(consumed.clone(), bytes));
    let kept = ResourceContext::new().unchecked_with_fact(ResourceFact::own_composite(
        "descriptor".into(),
        vec![ProgramValue::typed_pointer(slot, slot_type)],
    ));
    let result = apply_verified_heap_allocation_delta(
        &state,
        &input,
        &kept,
        &ResourceContext::new(),
        function.contract_interface(),
        &PureFactContext::new(),
        &state,
        &state,
    )
    .expect("the kept descriptor still supplies the input allocation");
    assert!(result.retired_allocations.is_empty());
    assert!(result.memory.live_heap_block_size(&consumed).is_some());
}

#[test]
fn contract_retirement_invalidates_creation_history_even_with_replacement() {
    let base = Address::new(AddressBase::Heap(930_100), AddressOffset::constant(0));
    let bytes = OldMachineTerm::constant(16);
    let input = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(base.clone(), bytes.clone()));
    let memory = SymbolicMemory::new()
        .with_heap_allocation_claim(base.clone(), AllocationSize::int32(bytes.clone()))
        .expect("live input allocation");
    let mut state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(memory.clone());
    state.record_population_storage_creation(base.base.clone());
    assert!(
        state
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&base.base)
    );
    let replacement_bytes = OldMachineTerm::Variable(Variable(930_101));
    assert!(matches!(
        int32_continuity(
            &base,
            &bytes,
            &base,
            &replacement_bytes,
            &PureFactContext::new(),
        ),
        AllocationContinuity::Undecided(_)
    ));
    for output in [
        ResourceContext::new(),
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_allocation(
            base.clone(),
            replacement_bytes.clone(),
        )),
    ] {
        let VerifiedAllocationDelta {
            memory: after_memory,
            retired_allocations: retired,
            ..
        } = apply_verified_heap_allocation_delta(
            &state,
            &input,
            &ResourceContext::new(),
            &output,
            &FunctionContractInterface::new(ProgramType::Void, vec![]),
            &PureFactContext::new(),
            &state,
            &state,
        )
        .expect("checked allocation retirement");
        assert_eq!(retired.len(), 1);
        assert_eq!(
            retired[0],
            AllocationSize::int32(bytes.clone()).byte_range(base.clone())
        );
        let mut returned = state.clone().with_memory(after_memory);
        for range in retired {
            returned
                .retire_population_storage(&range.base().base)
                .unwrap();
        }
        assert!(
            !returned
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .created_here(&base.base)
        );
    }
}

fn external_pointer(variable: u64) -> Address {
    Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(variable)), 4),
    )
}

#[test]
fn contract_allocation_retirement_respects_initialized_mutex_storage() {
    for continuity_undecided in [false, true] {
        let base = external_pointer(930_004);
        let bytes = OldMachineTerm::constant(48);
        let input = ResourceContext::new()
            .try_compose_with_fact(
                ResourceFact::own_allocation(base.clone(), bytes.clone()),
                &PureFactContext::new(),
            )
            .unwrap();
        let empty = ResourceContext::new();
        let output = if continuity_undecided {
            ResourceContext::new()
                .try_compose_with_fact(
                    ResourceFact::own_allocation(external_pointer(930_005), bytes.clone()),
                    &PureFactContext::new(),
                )
                .unwrap()
        } else {
            ResourceContext::new()
        };
        let interface = FunctionContractInterface::new(ProgramType::Void, vec![]);
        for mutex in [
            base.offset_by_bytes(8),
            Address::symbolic(Variable(930_006)),
        ] {
            let symbolic = matches!(mutex.base, AddressBase::Symbolic(_));
            let state = super::super::mutexes::MutexContext::new(ExecutionState::new())
                .initialize_empty(mutex, 40)
                .unwrap()
                .into_state();
            let result = apply_verified_heap_allocation_delta(
                &state,
                &input,
                &empty,
                &output,
                &interface,
                &PureFactContext::new(),
                &state,
                &state,
            );
            if symbolic {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        RuntimeError::MutexStorageSeparationRequired { .. }
                    ))
                ));
            } else {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        RuntimeError::MutexStorageInUse { .. }
                    ))
                ));
            }
        }
    }
}

#[test]
fn continuity_requires_both_the_allocation_base_and_size() {
    let assumptions = PureFactContext::new();
    let input = external_pointer(930_000);
    assert_eq!(
        int32_continuity(
            &input,
            &OldMachineTerm::constant(4),
            &input,
            &OldMachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Same,
    );
    assert_eq!(
        int32_continuity(
            &input,
            &OldMachineTerm::constant(4),
            &input,
            &OldMachineTerm::constant(8),
            &assumptions,
        ),
        AllocationContinuity::Inconsistent,
    );
    assert_eq!(
        int32_continuity(
            &Address::new(AddressBase::Heap(930_002), AddressOffset::constant(0)),
            &OldMachineTerm::constant(4),
            &Address::new(AddressBase::Heap(930_003), AddressOffset::constant(0)),
            &OldMachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Distinct,
    );

    let other = external_pointer(930_001);
    assert_eq!(
        int32_continuity(
            &input,
            &OldMachineTerm::constant(4),
            &other,
            &OldMachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Undecided(OldConditionTerm::address_equal(input, other)),
    );
}

#[test]
fn allocation_size_continuity_uses_graph_with_state_scope() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_memory(SymbolicMemory::new().with_block("alloc-size", 8));
    let pointer = |index| Address::new("alloc-size".into(), AddressOffset::scale_int32(index, 4));
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (
        OldMachineTerm::Variable(Variable(930_010)),
        OldMachineTerm::Variable(Variable(930_011)),
    );
    let after = crate::kernel::intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let size = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    let input_size = size(load(&before, a.clone()));
    let output_size = size(load(&before, b.clone()));
    let later_size = size(load(&after, b.clone()));
    let base = external_pointer(930_012);
    let premise = OldConditionTerm::equal(a, b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();

    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert_eq!(
        int32_continuity(&base, &input_size, &base, &output_size, &branch),
        AllocationContinuity::Same,
    );
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    for (size, context) in [(&later_size, &branch), (&output_size, &parent)] {
        assert!(matches!(
            int32_continuity(&base, &input_size, &base, size, context),
            AllocationContinuity::Undecided(OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: _,
                right: _
            }),
        ));
    }
    assert_ne!(
        int32_continuity(
            &base,
            &input_size,
            &external_pointer(930_013),
            &output_size,
            &branch
        ),
        AllocationContinuity::Same,
    );
}

/// One allocation is lent to a helper beside storage the caller keeps.
fn allocation_companion_call(unrelated: u64) -> (Address, ExecutionState, ExecutionState) {
    let base = Address::new(AddressBase::Heap(984_000), AddressOffset::constant(0));
    let memory = SymbolicMemory::new()
        .with_heap_allocation_claim(base.clone(), AllocationSize::int32(4))
        .unwrap();
    let mut caller = ExecutionState::new()
        .with_memory(memory)
        .with_population_creation_tracking();
    caller.record_population_storage_creation(base.base.clone());
    for id in 0..unrelated {
        caller.record_population_storage_creation(AddressBase::Heap(985_000 + id));
    }
    let mut callee = caller.clone();
    Arc::make_mut(&mut callee.population_effects).creation = Some(
        caller
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .enter_call(),
    );
    let input = ResourceFact::own_allocation(base.clone(), 4);
    let lent = transfer_population_call_facts(
        callee.clone(),
        &caller,
        &callee,
        &caller,
        std::iter::once(&input),
        &[],
        &PureFactContext::new(),
    )
    .unwrap();
    (base, caller, lent)
}

#[test]
fn allocation_companion_returns_through_a_proven_alias_only() {
    let _session = VerificationSession::enter();
    let (base, caller, callee) = allocation_companion_call(0);
    let alias = Address::symbolic(Variable(984_001));
    let output = ResourceFact::own_allocation(alias.clone(), 4);
    let missing = PureFactContext::new();
    let proven = missing
        .clone()
        .assume_condition(OldConditionTerm::address_equal(alias, base.clone()), true);
    let caller_events = caller.population_effects.creation.as_ref().unwrap();
    for (facts, accepted) in [(&missing, false), (&proven, true)] {
        let returned = transfer_population_call_facts(
            callee.clone(),
            &callee,
            &caller,
            &callee,
            std::iter::once(&output),
            &[],
            facts,
        )
        .unwrap();
        let finished = returned
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .finish_call(caller_events);
        if accepted {
            let resumed = finished.unwrap();
            assert!(resumed.created_here(&base.base));
            assert!(resumed.retired(&base.base).is_ok());
        } else {
            assert!(matches!(finished,
                Err(crate::kernel::population_authority::storage_creation::CreationRefusal::OutstandingOwnership)));
        }
    }
}

#[test]
fn a_return_alias_does_not_recreate_a_retired_cleanup_anchor() {
    let _session = VerificationSession::enter();
    let (base, caller, mut callee) = allocation_companion_call(0);
    callee.retire_population_storage(&base.base).unwrap();
    let alias = Address::symbolic(Variable(984_002));
    let output = ResourceFact::own_allocation(alias.clone(), 4);
    let facts = PureFactContext::new()
        .assume_condition(OldConditionTerm::address_equal(alias, base.clone()), true);
    let returned = transfer_population_call_facts(
        callee.clone(),
        &callee,
        &caller,
        &callee,
        std::iter::once(&output),
        &[],
        &facts,
    )
    .unwrap();
    let finished = returned
        .population_effects
        .creation
        .as_ref()
        .unwrap()
        .finish_call(caller.population_effects.creation.as_ref().unwrap())
        .unwrap();
    assert!(!finished.tracks_storage_anchor(&base.base));
    assert!(!finished.created_here(&base.base));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/allocation_continuity_tests.rs");
}

/// A contract's `uint64` `allocation` byte count is a 64-bit size only
/// under `malloc`'s decision (`design/heap-allocation-sizes.md`, stage 3): a product
/// `n * 4u64` needs `1 <= n <= PTRDIFF_MAX / 4` decided, a product of two
/// symbolic factors is never one, and a constant that fits a 32-bit size is
/// that size. A clause already established elsewhere (a contract's own
/// entry clause, a held body) is assumed.
#[test]
fn a_contract_uint64_allocation_size_needs_the_no_wrap_decision() {
    let count = OldMachineTerm::Variable(Variable(930_300));
    let other = OldMachineTerm::Variable(Variable(930_301));
    let product =
        OldMachineTerm::uint64_multiply(count.clone(), OldMachineTerm::uint64_constant(4));
    let unbounded = PureFactContext::new();
    let bounded = [
        OldConditionTerm::uint64_greater_than(count.clone(), OldMachineTerm::uint64_constant(0)),
        OldConditionTerm::uint64_less_equal(count.clone(), OldMachineTerm::uint64_constant(1000)),
        OldConditionTerm::uint64_greater_than(other.clone(), OldMachineTerm::uint64_constant(0)),
        OldConditionTerm::uint64_less_equal(other.clone(), OldMachineTerm::uint64_constant(1000)),
    ]
    .into_iter()
    .fold(PureFactContext::new(), |context, condition| {
        context.assume_condition(condition, true)
    });

    assert_eq!(
        uint64_allocation_size_argument(&OldMachineTerm::uint64_constant(16), &unbounded),
        Ok(ProgramValue::Int32(OldMachineTerm::constant(16))),
    );
    assert!(matches!(
        uint64_allocation_size_argument(&product, &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert_eq!(
        uint64_allocation_size_argument(&product, &bounded),
        Ok(ProgramValue::UInt64(product.clone())),
    );
    assert_eq!(
        uint64_allocation_size_argument(&product, &unbounded.clone().assume_entry_clause_spans()),
        Ok(ProgramValue::UInt64(product.clone())),
    );
    let symbolic_product = OldMachineTerm::uint64_multiply(count.clone(), other);
    assert!(matches!(
        uint64_allocation_size_argument(&symbolic_product, &bounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert!(matches!(
        uint64_allocation_size_argument(&OldMachineTerm::uint64_constant(0), &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert!(matches!(
        uint64_allocation_size_argument(&OldMachineTerm::uint64_constant(u64::MAX), &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
}
