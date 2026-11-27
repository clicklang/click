use super::*;

#[test]
fn exact_pointer_read_reuses_the_indexed_store_across_local_history() {
    let work = [4u32, 16, 64, 256].map(|count| {
        let _session = VerificationSession::enter();
        let slot = Address::new(
            "local:pointer-holding-slot".into(),
            AddressOffset::constant(0),
        );
        let unrelated = Address::new("local:unrelated-scalar".into(), AddressOffset::constant(0));
        let value_type = ProgramType::Int32Pointer;
        let target = Pointer::new(Address::symbolic(Variable(989_013)), value_type);
        let mut state = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block(slot.base.clone(), value_type.byte_width())
                .with_block(unrelated.base.clone(), 4)
                .store(slot.clone(), ProgramValue::Pointer(target.clone())),
        );
        for index in 0..count {
            let memory = state
                .memory()
                .clone()
                .store(unrelated.clone(), ProgramValue::Int32(index.into()));
            state = state.with_memory(memory);
        }
        let read = |state: &ExecutionState| {
            Pointer::from_point_read(state.program_point().for_exact_read(), value_type, &slot)
        };
        let exact = read(&state);
        let (stored, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_read_over_write_program_value(exact.address())
        });
        assert_eq!(stored, Some(target));
        let memory = state
            .memory()
            .clone()
            .store(slot.clone(), ProgramValue::Int32(0u32.into()));
        assert_eq!(
            pointer_read_over_write_program_value(read(&state.with_memory(memory)).address()),
            None
        );
        work
    });
    assert!(work.iter().all(|units| *units == work[0]), "{work:?}");
}

#[test]
fn stored_address_base_queries_scale_with_new_read_definitions() {
    fn work(steps: u64, unrelated: u64) -> usize {
        let _session = VerificationSession::enter();
        let target = Address::new(AddressBase::Heap(989_010), AddressOffset::constant(0));
        let other = AddressBase::Heap(989_011);
        let slot = Address::symbolic(Variable(989_012));
        let mut memory = SymbolicMemory::new()
            .with_block(target.base.clone(), 8)
            .with_block(other.clone(), 8);
        for index in 0..unrelated {
            memory = memory.store(
                Address::symbolic(Variable(990_000 + index)),
                ProgramValue::Int32(0u32.into()),
            );
        }
        let mut pointer = target;
        let mut reads = Vec::new();
        for _ in 0..steps {
            memory = memory.clone().store(
                slot.clone(),
                ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
            );
            pointer = Address::loaded_value(&intern_memory_ref(&memory), &slot);
            reads.push(pointer.clone());
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for read in &reads {
                assert!(read.base.proven_distinct(&other));
            }
        });
        work
    }
    let costs = [4, 8, 16, 32].map(|steps| work(steps, 0));
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    let unrelated_costs = [0, 8, 32, 128].map(|unrelated| work(8, unrelated));
    assert!(
        unrelated_costs
            .iter()
            .all(|cost| *cost == unrelated_costs[0]),
        "{unrelated_costs:?}"
    );
}

#[test]
fn structural_read_comparison_forms_scale_with_selected_observations() {
    fn work(selected: u64, unrelated: u64) -> usize {
        let _session = VerificationSession::enter();
        let address = |index| Address::new(AddressBase::Heap(index), AddressOffset::constant(0));
        let mut memory = SymbolicMemory::new();
        for index in 0..selected + unrelated {
            memory = memory.store(address(index), ProgramValue::Int32(37u32.into()));
        }
        let memory = intern_memory(memory);
        let goals: Vec<_> = (0..selected)
            .map(|index| {
                let read = OldMachineTerm::read_named(
                    ProgramPoint::at(&memory),
                    Box::new(address(index)),
                    LoadKind::Int32,
                );
                let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, read).unwrap();
                Proposition::condition_is(
                    OldConditionTerm::integer_equal(observed, IntegerTerm::constant_i64(37)),
                    true,
                )
            })
            .collect();
        // These observations own their reads; comparison must not need names.
        clear_load_variable_registry();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for goal in &goals {
                assert!(holds_by_read_over_write(goal));
            }
        });
        assert_eq!(load_variable_registry_len(), 0);
        work
    }
    let costs = [4, 8, 16, 32].map(|n| work(n, 0));
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    let ambient = [0, 8, 32, 128].map(|n| work(8, n));
    assert!(
        ambient.iter().all(|cost| *cost == ambient[0]),
        "{ambient:?}"
    );
}

/// A library value held in memory, such as a borrowed Rust iterator, is read
/// as an algebraic load; exact comparison reads it as the stored value, at a
/// cost in the reads compared and none in the memory's other cells.
#[test]
fn algebraic_read_comparison_forms_scale_with_selected_observations() {
    fn work(selected: u64, unrelated: u64) -> usize {
        let _session = VerificationSession::enter();
        let address = |index| Address::new(AddressBase::Heap(index), AddressOffset::constant(0));
        // A library instance, as Surface registers it: opaque, of fixed width.
        TypeParameterName::declare_library_instance("SliceIter<uint8>");
        let algebraic_type = AlgebraicType {
            rigid: true,
            name: "SliceIter<uint8>".into(),
            arguments: vec![],
            variants: std::sync::Arc::new([]),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::new())),
        };
        let stored = |index| AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(991_000 + index)),
        };
        let mut memory = SymbolicMemory::new();
        for index in 0..selected + unrelated {
            memory = memory.store(
                address(index),
                ProgramValue::Parameter(Box::new(stored(index))),
            );
        }
        let memory = intern_memory(memory);
        let goals: Vec<_> = (0..selected)
            .map(|index| {
                let read = AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::MemoryLoad {
                        point: crate::kernel::ProgramPoint::at(&memory.clone()),
                        pointer: Box::new(address(index)),
                    },
                };
                Proposition::condition_is(
                    OldConditionTerm::AlgebraicEqual(Box::new(read), Box::new(stored(index))),
                    true,
                )
            })
            .collect();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (index, goal) in (0..).zip(&goals) {
                assert_eq!(
                    comparison_form(goal),
                    Some(Proposition::condition_is(
                        OldConditionTerm::AlgebraicEqual(
                            Box::new(stored(index)),
                            Box::new(stored(index))
                        ),
                        true,
                    ))
                );
            }
        });
        work
    }
    let costs = [4, 8, 16, 32].map(|n| work(n, 0));
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    let ambient = [0, 8, 32, 128].map(|n| work(8, n));
    assert!(
        ambient.iter().all(|cost| *cost == ambient[0]),
        "{ambient:?}"
    );
}
