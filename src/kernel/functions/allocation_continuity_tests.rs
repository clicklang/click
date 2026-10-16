use super::*;

#[test]
fn contract_retirement_invalidates_creation_provenance_even_with_replacement() {
    let base = Pointer {
        block: PointerBlock::Heap(930_100),
        offset: PointerOffsetTerm::Constant(0),
    };
    let bytes = Bitvector32Term::Constant(16);
    let input = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(base.clone(), bytes.clone()));
    let memory = CMemory::new()
        .with_heap_allocation_claim(base.clone(), bytes.clone())
        .expect("live input allocation");
    let mut state = CState::new()
        .with_population_creation_tracking()
        .with_memory(memory.clone());
    state.record_population_storage_creation(base.block.clone());
    assert!(
        state
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&base.block)
    );
    let replacement_bytes = Bitvector32Term::Variable(Variable(930_101));
    assert!(matches!(
        allocation_continuity(
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
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_allocation(
            base.clone(),
            replacement_bytes.clone(),
        )),
    ] {
        let (after_memory, _, retired) = apply_verified_heap_allocation_delta(
            memory.clone(),
            &memory,
            &input,
            &ResourceContext::new(),
            &output,
            &CFunctionContractInterface::new(CType::Void, vec![]),
            &PureFactContext::new(),
            None,
            &state,
            &state,
        )
        .expect("checked allocation retirement");
        assert_eq!(retired, vec![base.block.clone()]);
        let mut returned = state.clone().with_memory(after_memory);
        for block in retired {
            returned.retire_population_storage(&block).unwrap();
        }
        assert!(
            !returned
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .created_here(&base.block)
        );
    }
}

fn external_pointer(variable: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(variable)), 4),
    }
}

#[test]
fn contract_allocation_retirement_respects_initialized_mutex_storage() {
    for continuity_undecided in [false, true] {
        let base = external_pointer(930_004);
        let bytes = Bitvector32Term::Constant(48);
        let input = ResourceContext::new()
            .try_compose_with_fact(
                CResourceFact::own_allocation(base.clone(), bytes.clone()),
                &PureFactContext::new(),
            )
            .unwrap();
        let empty = ResourceContext::new();
        let output = if continuity_undecided {
            ResourceContext::new()
                .try_compose_with_fact(
                    CResourceFact::own_allocation(external_pointer(930_005), bytes.clone()),
                    &PureFactContext::new(),
                )
                .unwrap()
        } else {
            ResourceContext::new()
        };
        let interface = CFunctionContractInterface::new(CType::Void, vec![]);
        for mutex in [
            base.offset_by_bytes(8),
            Pointer::symbolic(Variable(930_006)),
        ] {
            let symbolic = matches!(mutex.block, PointerBlock::Symbolic(_));
            let state = super::super::mutexes::MutexContext::new(CState::new())
                .initialize_empty(mutex, 40)
                .unwrap()
                .into_state();
            let result = apply_verified_heap_allocation_delta(
                state.memory.clone(),
                &state.memory,
                &input,
                &empty,
                &output,
                &interface,
                &PureFactContext::new(),
                None,
                &state,
                &state,
            );
            if symbolic {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        CRuntimeError::MutexStorageSeparationRequired { .. }
                    ))
                ));
            } else {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        CRuntimeError::MutexStorageInUse { .. }
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
        allocation_continuity(
            &input,
            &Bitvector32Term::Constant(4),
            &input,
            &Bitvector32Term::Constant(4),
            &assumptions,
        ),
        AllocationContinuity::Same,
    );
    assert_eq!(
        allocation_continuity(
            &input,
            &Bitvector32Term::Constant(4),
            &input,
            &Bitvector32Term::Constant(8),
            &assumptions,
        ),
        AllocationContinuity::Inconsistent,
    );
    assert_eq!(
        allocation_continuity(
            &Pointer {
                block: PointerBlock::Heap(930_002),
                offset: PointerOffsetTerm::Constant(0),
            },
            &Bitvector32Term::Constant(4),
            &Pointer {
                block: PointerBlock::Heap(930_003),
                offset: PointerOffsetTerm::Constant(0),
            },
            &Bitvector32Term::Constant(4),
            &assumptions,
        ),
        AllocationContinuity::Distinct,
    );

    let other = external_pointer(930_001);
    assert_eq!(
        allocation_continuity(
            &input,
            &Bitvector32Term::Constant(4),
            &other,
            &Bitvector32Term::Constant(4),
            &assumptions,
        ),
        AllocationContinuity::Undecided(ConditionTerm::pointer_equal(input, other)),
    );
}

#[test]
fn allocation_size_continuity_uses_graph_with_snapshot_scope() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_c_memory(CMemory::new().with_block("alloc-size", 8));
    let pointer = |index| Pointer {
        block: "alloc-size".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (
        Bitvector32Term::Variable(Variable(930_010)),
        Bitvector32Term::Variable(Variable(930_011)),
    );
    let after = crate::kernel::intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let size = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let input_size = size(load(&before, a.clone()));
    let output_size = size(load(&before, b.clone()));
    let later_size = size(load(&after, b.clone()));
    let base = external_pointer(930_012);
    let premise = ConditionTerm::equal(a, b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();

    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert_eq!(
        allocation_continuity(&base, &input_size, &base, &output_size, &branch),
        AllocationContinuity::Same,
    );
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    for (size, context) in [(&later_size, &branch), (&output_size, &parent)] {
        assert!(matches!(
            allocation_continuity(&base, &input_size, &base, size, context),
            AllocationContinuity::Undecided(ConditionTerm::Bitvector32Equal(_, _)),
        ));
    }
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(matches!(
        allocation_continuity(&base, &input_size, &base, &output_size, &withdrawn),
        AllocationContinuity::Undecided(ConditionTerm::Bitvector32Equal(_, _)),
    ));
    assert_ne!(
        allocation_continuity(
            &base,
            &input_size,
            &external_pointer(930_013),
            &output_size,
            &branch
        ),
        AllocationContinuity::Same,
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/allocation_continuity_tests.rs");
}
