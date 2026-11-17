use super::*;

#[test]
fn copying_a_union_drops_destination_views_absent_from_source() {
    let source = Pointer {
        block: "union-copy-source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let destination = Pointer {
        block: "union-copy-destination".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let layout = AggregateLayout::with_unions(
        4,
        4,
        vec![],
        vec![AggregateUnion::new(
            "u",
            0,
            4,
            vec![
                AggregateUnionField::new("byte", 0, ProgramType::UInt8),
                AggregateUnionField::new("word", 0, ProgramType::Int32),
            ],
        )],
    );
    let memory = SymbolicMemory::new()
        .with_block(source.block.clone(), 4)
        .with_block(destination.block.clone(), 4)
        .store_union(
            source.clone(),
            ProgramType::UInt8,
            crate::kernel::uint8(0xAA),
        )
        .store_union(
            destination.clone(),
            ProgramType::Int32,
            ProgramValue::Int32(MachineTerm::constant(0x5151)),
        );

    let copied = copy_aggregate_fields(memory, &source, &destination, &layout);

    assert_eq!(
        copied.known_union_value(&destination, ProgramType::UInt8),
        Some(crate::kernel::uint8(0xAA)),
    );
    assert_eq!(
        copied.known_union_value(&destination, ProgramType::Int32),
        None
    );
}

/// A local `{ int32 tag; union { int32 number; uint8 byte; } }` whose
/// cached values an unplaced store into the block forgot, the union's
/// written only when `union_written`.
fn forgotten_local_packet(
    union_written: bool,
) -> (SymbolicMemory, Pointer, Pointer, AggregateLayout) {
    let source = Pointer {
        block: "local:forgotten-packet-source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let destination = Pointer {
        block: "local:forgotten-packet-destination".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let layout = AggregateLayout::with_unions(
        8,
        4,
        vec![AggregateField::new("tag", 0, ProgramType::Int32)],
        vec![AggregateUnion::new(
            "u",
            4,
            4,
            vec![
                AggregateUnionField::new("number", 0, ProgramType::Int32),
                AggregateUnionField::new("byte", 0, ProgramType::UInt8),
            ],
        )],
    );
    let mut memory = SymbolicMemory::new()
        .with_block(source.block.clone(), 8)
        .with_block(destination.block.clone(), 8)
        .store(
            source.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
    if union_written {
        memory = memory.store_union(
            source.offset_by_bytes(4),
            ProgramType::Int32,
            ProgramValue::Int32(MachineTerm::constant(2)),
        );
    }
    // `source[u] = …` for an index the facts do not place: every cell
    // and view of the block may be the one it writes.
    let unplaced = Pointer {
        block: source.block.clone(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(925_001)), 4),
    };
    let memory = memory.without_possible_aliasing_cells(&unplaced, 4, &PureFactContext::new());
    assert!(memory.known_value(&source).is_none());
    assert!(
        memory
            .known_union_value(&source.offset_by_bytes(4), ProgramType::Int32)
            .is_none()
    );
    (memory, source, destination, layout)
}

#[test]
fn copying_forgotten_initialized_fields_carries_unknown_values() {
    let (memory, source, destination, layout) = forgotten_local_packet(true);
    let copied = copy_aggregate_fields_checked(memory, &source, &destination, &layout)
        .expect("forgotten but initialized fields are not an uninitialized read");
    // The destination holds a value for every member, so it is
    // initialized: each is the typed load of the forgotten source.
    assert!(copied.known_value(&destination).is_some());
    assert!(
        copied
            .known_union_value(&destination.offset_by_bytes(4), ProgramType::Int32)
            .is_some()
    );
}

#[test]
fn copying_a_never_written_union_member_stays_an_uninitialized_read() {
    let (memory, source, destination, layout) = forgotten_local_packet(false);
    assert_eq!(
        copy_aggregate_fields_checked(memory, &source, &destination, &layout).err(),
        Some(UndefinedBehavior::UninitializedRead),
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/aggregate_union_copy_tests.rs");
}

#[test]
fn aggregate_and_union_copies_keep_retained_pointer_producers() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = SymbolicMemory::local_pointer("retained_copy_source");
    let target = SymbolicMemory::local_pointer("retained_copy_target");
    let pointer = PointerValue::new(
        Pointer::symbolic(Variable(1027800)),
        ProgramType::Int32Pointer,
    )
    .with_pointee_constant(true);
    let root = KernelTerm::shared_pointer_call(
        KernelTerm::checked_call(
            KernelType::Program(ProgramType::Int32Pointer),
            "copied".into(),
            vec![],
        ),
        crate::kernel::SharedPointerValue::import(&pointer),
    );
    let memory = SymbolicMemory::new()
        .with_block(source.block.clone(), 8)
        .with_block(target.block.clone(), 8)
        .store_retained(source.clone(), root.clone().into());
    let layout = AggregateLayout::new(
        8,
        8,
        vec![AggregateField::new("pointer", 0, ProgramType::Int32Pointer)],
    );
    let copied = copy_aggregate_fields(memory.clone(), &source, &target, &layout);
    assert_eq!(
        copied.known_retained_value(&target).unwrap().shared(),
        Some(&root)
    );
    let layout = AggregateLayout::with_unions(
        8,
        8,
        vec![],
        vec![AggregateUnion::new(
            "u",
            0,
            8,
            vec![AggregateUnionField::new(
                "pointer",
                0,
                ProgramType::Int32Pointer,
            )],
        )],
    );
    let copied = copy_aggregate_fields(memory, &source, &target, &layout);
    assert_eq!(
        copied
            .known_retained_union_value(&target, ProgramType::Int32Pointer)
            .unwrap()
            .shared(),
        Some(&root)
    );
    let paths = crate::kernel::eval::evaluate_retained_memory_load_paths(
        &copied,
        target.clone(),
        ProgramType::Int32Pointer,
        ExecutionFacts::new(),
        vec![],
        &PureFactContext::new(),
        false,
        false,
        None,
        None,
    );
    assert_eq!(paths.len(), 1);
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("union pointer load")
    };
    assert_eq!(value.shared(), Some(&root));
    assert!(value.pointer().unwrap().pointee_constant());
    let overwritten = copied.store(
        target.clone(),
        ProgramValue::Int32(MachineTerm::constant(0)),
    );
    assert!(
        overwritten
            .known_retained_union_value(&target, ProgramType::Int32Pointer)
            .is_none()
    );
}
