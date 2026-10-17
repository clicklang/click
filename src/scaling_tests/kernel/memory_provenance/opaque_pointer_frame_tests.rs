// Deterministic work for the selected bounded pointer-value query.
use super::*;

#[test]
fn bounded_pointer_value_skips_unrelated_facts_cells_and_history() {
    let mut samples = Vec::new();
    let mut wide_samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let possible_write = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(9_880_301)),
            4,
        );
        let stored = Pointer::symbolic(Variable(9_880_302));
        let mut memory = CMemory::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            let block = format!("local:irrelevant-{index}");
            memory = memory.with_block(block.clone(), 4).store(
                Pointer {
                    block: PointerBlock::Concrete(block),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::Int32(Bitvector32Term::Constant(1)),
            );
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(9_881_000 + 2 * index)),
                    Pointer::symbolic(Variable(9_881_001 + 2 * index)),
                ),
                true,
            );
        }
        memory = memory.store(
            field.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        memory =
            memory.without_possible_aliasing_cells(&possible_write, 4, &PureFactContext::new());
        let snapshot = intern_c_memory(memory);
        let read = Pointer::loaded_value(&snapshot, &field);
        context
            .equality_graph
            .register_pointer_read_definition(&read, &snapshot, &field);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_read_has_recorded_value(&read, &stored, &context)
        });
        assert!(holds);
        assert!(work > 0);
        samples.push(work);
        let wide_address = field.offset_by_bytes(32);
        let write_alias = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(9_880_303)),
            4,
        );
        context = context.assume_condition(
            ConditionTerm::pointer_equal(write_alias.clone(), wide_address.clone()),
            true,
        );
        let parent = Pointer::symbolic(Variable(9_880_304));
        let parent_alias = Pointer::symbolic(Variable(9_880_305));
        context = context.assume_condition(
            ConditionTerm::pointer_equal(parent.clone(), parent_alias.clone()),
            true,
        );
        let value = Bitvector32Term::PointerAddress(
            Box::new(parent),
            crate::kernel::AddressObjectClass::NONE,
        );
        let wanted = Bitvector32Term::PointerAddress(
            Box::new(parent_alias),
            crate::kernel::AddressObjectClass::NONE,
        );
        let source = intern_c_memory(
            snapshot
                .memory()
                .clone()
                .store(write_alias, CValue::UInt64(value.clone())),
        );
        let projected = canonical_projected_load_memory(&source, &wide_address);
        let wide_read =
            Bitvector32Term::MemoryLoad(projected, Box::new(wide_address), LoadKind::Bits64);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            wide_read_has_recorded_value(&wide_read, &wanted, &context)
        });
        assert!(holds);
        assert!(work > 0);
        wide_samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
    assert!(
        wide_samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{wide_samples:?}"
    );
}

#[test]
fn complete_read_domains_use_numeric_storage_classes_without_scanning_other_classes() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new();
        let equal = |a: Pointer, b: Pointer| {
            ConditionTerm::uint64_equal(
                Bitvector32Term::pointer_address(a),
                Bitvector32Term::pointer_address(b),
            )
        };
        for index in 0..size {
            facts = facts.assume_condition(
                equal(
                    Pointer::symbolic(Variable(9_890_000 + index * 2)),
                    Pointer::symbolic(Variable(9_890_001 + index * 2)),
                ),
                true,
            );
        }
        let a = Pointer::symbolic(Variable(9_889_000));
        let b = Pointer::symbolic(Variable(9_889_001));
        facts = facts.assume_condition(equal(a.clone(), b.clone()), true);
        let memory = intern_c_memory(CMemory::new());
        let left = Pointer::loaded_value(&memory, &a);
        let right = Pointer::loaded_value(&memory, &b);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_read_designations_equal(&left, &right, &facts)
                && pointer_read_extents_equal(&left, &right, &facts)
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn copied_pointer_frames_ignore_unrelated_separations() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let separation = |a: Pointer, a_words: u32, b: Pointer| Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new(
                a,
                0u32.into(),
                a_words.into(),
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new(
                b,
                0u32.into(),
                8u32.into(),
            ))),
        };
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_proposition(separation(
                Pointer::symbolic(Variable(9_910_000 + index * 2)),
                4,
                Pointer::symbolic(Variable(9_910_001 + index * 2)),
            ));
        }
        let header = Pointer::symbolic(Variable(9_909_000));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Pointer::symbolic(Variable(9_909_001));
        let target = Pointer::symbolic(Variable(9_909_002));
        let stored = CPointerValue::new(target.clone(), CType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: target,
                width: 4u32.into(),
            },
        ));
        let memory = intern_c_memory(
            CMemory::new()
                .store(field.clone(), CValue::Pointer(stored.clone()))
                .store(
                    buffer.clone().offset_by_bytes(4),
                    CValue::Int32(7u32.into()),
                ),
        );
        facts = facts.assume_proposition(separation(header, 4, buffer));
        let read = CPointerValue::from_read(
            stored.pointer().clone(),
            CType::Int32Pointer,
            &memory,
            &field,
        );
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.pointer_designations_match(&read, &stored)
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn sibling_pointer_reads_stop_before_unrelated_shared_history() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_920_000));
        let mut memory = CMemory::new().with_block("local:read-common-history", 4096);
        for index in 0..size {
            memory = memory.store(
                Pointer {
                    block: "local:read-common-history".into(),
                    offset: PointerOffsetTerm::Constant(index as i64 * 4),
                },
                CValue::Int32(0u32.into()),
            );
        }
        let left = intern_c_memory(memory.clone().store(
            field.offset_by_bytes(8),
            CValue::UInt64(Bitvector32Term::UInt64Constant(1)),
        ));
        let right = intern_c_memory(memory.store(
            field.offset_by_bytes(16),
            CValue::UInt64(Bitvector32Term::UInt64Constant(2)),
        ));
        let producer = crate::kernel::equality_graph::EqualityGraph::default();
        for index in 0..size {
            producer.register_pointer_read_definition(
                &Pointer::loaded(
                    field.block.clone(),
                    Bitvector32Term::Variable(Variable(9_930_000 + index)),
                    4,
                ),
                &left,
                &field.offset_by_bytes(32 + index as u32 * 8),
            );
        }
        let legacy = |memory: &SharedCMemory| {
            Pointer::loaded(
                field.block.clone(),
                Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(field.clone()),
                    LoadKind::Bits32,
                ),
                4,
            )
        };
        let a = legacy(&left);
        let b = legacy(&right);
        producer.register_pointer_read_definition(&a, &left, &field);
        producer.register_pointer_read_definition(&b, &right, &field);
        let context = PureFactContext::new();
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            complete_pointer_reads_equal_across_frame(&a, &b, &context)
                && pointer_read_designations_equal(
                    &Pointer::loaded_value(&left, &field),
                    &Pointer::loaded_value(&right, &field),
                    &context,
                )
                && pointer_read_extents_equal(
                    &Pointer::loaded_value(&left, &field),
                    &Pointer::loaded_value(&right, &field),
                    &context,
                )
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}
