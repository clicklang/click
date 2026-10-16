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
    let layout = CAggregateLayout::with_unions(
        4,
        4,
        vec![],
        vec![CAggregateUnion::new(
            "u",
            0,
            4,
            vec![
                CAggregateUnionField::new("byte", 0, CType::UInt8),
                CAggregateUnionField::new("word", 0, CType::Int32),
            ],
        )],
    );
    let memory = CMemory::new()
        .with_block(source.block.clone(), 4)
        .with_block(destination.block.clone(), 4)
        .store_union(
            source.clone(),
            CType::UInt8,
            CValue::UInt8(Bitvector32Term::Constant(0xAA)),
        )
        .store_union(
            destination.clone(),
            CType::Int32,
            CValue::Int32(Bitvector32Term::Constant(0x5151)),
        );

    let copied = copy_aggregate_fields(memory, &source, &destination, &layout);

    assert_eq!(
        copied.known_union_value(&destination, CType::UInt8),
        Some(CValue::UInt8(Bitvector32Term::Constant(0xAA))),
    );
    assert_eq!(copied.known_union_value(&destination, CType::Int32), None);
}

/// A local `{ int32 tag; union { int32 number; uint8 byte; } }` whose
/// cached values an unplaced store into the block forgot, the union's
/// written only when `union_written`.
fn forgotten_local_packet(union_written: bool) -> (CMemory, Pointer, Pointer, CAggregateLayout) {
    let source = Pointer {
        block: "local:forgotten-packet-source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let destination = Pointer {
        block: "local:forgotten-packet-destination".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let layout = CAggregateLayout::with_unions(
        8,
        4,
        vec![CAggregateField::new("tag", 0, CType::Int32)],
        vec![CAggregateUnion::new(
            "u",
            4,
            4,
            vec![
                CAggregateUnionField::new("number", 0, CType::Int32),
                CAggregateUnionField::new("byte", 0, CType::UInt8),
            ],
        )],
    );
    let mut memory = CMemory::new()
        .with_block(source.block.clone(), 8)
        .with_block(destination.block.clone(), 8)
        .store(source.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
    if union_written {
        memory = memory.store_union(
            source.offset_by_bytes(4),
            CType::Int32,
            CValue::Int32(Bitvector32Term::Constant(2)),
        );
    }
    // `source[u] = …` for an index the facts do not place: every cell
    // and view of the block may be the one it writes.
    let unplaced = Pointer {
        block: source.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(925_001)), 4),
    };
    let memory = memory.without_possible_aliasing_cells(&unplaced, 4, &PureFactContext::new());
    assert!(memory.known_value(&source).is_none());
    assert!(
        memory
            .known_union_value(&source.offset_by_bytes(4), CType::Int32)
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
            .known_union_value(&destination.offset_by_bytes(4), CType::Int32)
            .is_some()
    );
}

#[test]
fn copying_a_never_written_union_member_stays_an_uninitialized_read() {
    let (memory, source, destination, layout) = forgotten_local_packet(false);
    assert_eq!(
        copy_aggregate_fields_checked(memory, &source, &destination, &layout).err(),
        Some(CUndefinedBehavior::UninitializedRead),
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/aggregate_union_copy_tests.rs");
}
