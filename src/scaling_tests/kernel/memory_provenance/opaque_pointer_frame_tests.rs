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
        let value = Bitvector32Term::PointerAddress(Box::new(parent), crate::kernel::AddressObjectClass::NONE);
        let wanted = Bitvector32Term::PointerAddress(Box::new(parent_alias), crate::kernel::AddressObjectClass::NONE);
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
