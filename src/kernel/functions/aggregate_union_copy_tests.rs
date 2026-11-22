use super::*;

#[test]
fn copying_a_union_drops_destination_views_absent_from_source() {
    let source = Address {
        base: "union-copy-source".into(),
        offset: AddressOffset::Constant(0),
    };
    let destination = Address {
        base: "union-copy-destination".into(),
        offset: AddressOffset::Constant(0),
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
        .with_block(source.base.clone(), 4)
        .with_block(destination.base.clone(), 4)
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
) -> (SymbolicMemory, Address, Address, AggregateLayout) {
    let source = Address {
        base: "local:forgotten-packet-source".into(),
        offset: AddressOffset::Constant(0),
    };
    let destination = Address {
        base: "local:forgotten-packet-destination".into(),
        offset: AddressOffset::Constant(0),
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
        .with_block(source.base.clone(), 8)
        .with_block(destination.base.clone(), 8)
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
    let unplaced = Address {
        base: source.base.clone(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(925_001)), 4),
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

#[test]
fn aggregate_copy_array_keeps_its_caller_source_point_after_an_earlier_field() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let target = SymbolicMemory::frame_local_pointer(1, "record_copy");
    let layout = AggregateLayout::new(
        20,
        4,
        vec![
            AggregateField::new("tag", 0, ProgramType::UInt32),
            AggregateField::new("data", 4, ProgramType::UInt32Array(4)),
        ],
    );
    let entry = ExecutionState::new().begin_function_entry_memory();
    let state = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(target.base.clone(), layout.size_bytes()),
    );
    let point = state.program_point();
    let copied = copy_aggregate_fields_checked_at(&state, &source, &target, &layout).unwrap();
    assert!(
        copied.known_value(&target).is_some(),
        "the earlier scalar field was copied"
    );
    let mut runs = copied.cells.runs_in_block(&target.base);
    let run = runs
        .next()
        .expect("compact capture of the unknown array field");
    assert!(runs.next().is_none());
    assert_eq!(run.count(), 4);
    assert_eq!(run.source_point().id(), point.id());
    let Some(ProgramValue::UInt32(MachineTerm::MemoryLoad(version, address, kind))) =
        copied.known_value(&target.offset_by_bytes(8))
    else {
        panic!("a typed read from the caller's field");
    };
    assert_eq!(kind, LoadKind::UInt32);
    assert_eq!(*address, source.offset_by_bytes(8));
    assert_eq!(version.read_version_id(), entry.program_point_id());
}

#[test]
fn aggregate_copy_names_uncached_scalar_fields_at_the_caller_versions() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let target = SymbolicMemory::frame_local_pointer(1, "scalar_record_copy");
    let layout = AggregateLayout::new(
        24,
        8,
        vec![
            AggregateField::new("tag", 0, ProgramType::Int32),
            AggregateField::new("count", 4, ProgramType::UInt32),
            AggregateField::new("x", 8, ProgramType::Float32),
            AggregateField::new("y", 16, ProgramType::Float64),
        ],
    );
    let entry = ExecutionState::new().begin_function_entry_memory();
    let state = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(target.base.clone(), layout.size_bytes()),
    );
    let entry_id = entry.program_point_id();
    let copy_id = state.observation_point_id();
    assert_ne!(entry_id, copy_id);
    let copied = copy_aggregate_fields_checked_at(&state, &source, &target, &layout).unwrap();
    for (offset, ty, expected) in [
        (0, ProgramType::Int32, entry_id),
        (4, ProgramType::UInt32, entry_id),
        (8, ProgramType::Float32, copy_id),
        (16, ProgramType::Float64, copy_id),
    ] {
        assert!(
            state
                .memory()
                .known_value(&source.offset_by_bytes(offset))
                .is_none()
        );
        let value = copied.known_value(&target.offset_by_bytes(offset)).unwrap();
        assert_eq!(value.program_type(), ty);
        let Some(MachineTerm::MemoryLoad(point, address, kind)) =
            crate::kernel::spec::program_value_bitvector_term(&value)
        else {
            panic!("expected a typed source read");
        };
        assert_eq!(point.read_version_id(), expected);
        assert_eq!(*address, source.offset_by_bytes(offset));
        assert_eq!(Some(kind), LoadKind::of_type(ty));
    }
}

#[test]
fn aggregate_copy_keeps_the_entry_version_of_an_uncached_opaque_field() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let target = SymbolicMemory::frame_local_pointer(1, "opaque_record_copy");
    let parameter = crate::kernel::TypeParameterName::intern("CopyField");
    let ty = ProgramType::Parameter(parameter);
    let layout = AggregateLayout::new(
        ty.byte_width(),
        4,
        vec![AggregateField::new("value", 0, ty)],
    );
    let entry = ExecutionState::new().begin_function_entry_memory();
    let state = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(target.base.clone(), layout.size_bytes()),
    );
    assert!(state.memory().known_value(&source).is_none());
    assert_ne!(state.observation_point_id(), entry.program_point_id());

    let copied = copy_aggregate_fields_checked_at(&state, &source, &target, &layout).unwrap();
    let Some(ProgramValue::Parameter(read)) = copied.known_value(&target) else {
        panic!("the copy contains a read of the opaque source field");
    };
    let crate::kernel::AlgebraicTermNode::MemoryLoad { point, pointer } = read.node else {
        panic!("the copied value reads the caller's field");
    };
    assert_eq!(read.algebraic_type, parameter.algebraic_type());
    assert_eq!(point.read_version_id(), entry.program_point_id());
    assert_eq!(*pointer, source);
}

#[test]
fn aggregate_copy_names_forgotten_integer_fields_by_their_typed_stores() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let target = SymbolicMemory::frame_local_pointer(1, "forgotten_record_copy");
    for value in [
        crate::kernel::uint8(17),
        ProgramValue::UInt64(MachineTerm::uint64_constant(42)),
    ] {
        let ty = value.program_type();
        let bytes = ty.byte_width();
        let layout = AggregateLayout::new(bytes, bytes, vec![AggregateField::new("value", 0, ty)]);
        let initial = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(target.base.clone(), bytes));
        let stored = initial
            .clone()
            .with_memory(initial.memory().clone().store(source.clone(), value));
        let forgotten = stored.memory().without_possible_aliasing_cells(
            &source,
            bytes,
            &PureFactContext::new(),
        );
        let before = stored.clone().with_memory(forgotten);
        assert!(before.memory().known_value(&source).is_none());
        let copied = copy_aggregate_fields_checked_at(&before, &source, &target, &layout).unwrap();
        let value = copied.known_value(&target).unwrap();
        assert_eq!(value.program_type(), ty);
        let Some(MachineTerm::MemoryLoad(point, address, kind)) =
            crate::kernel::spec::program_value_bitvector_term(&value)
        else {
            panic!("expected a typed source read");
        };
        assert_eq!(point.read_version_id(), stored.observation_point_id());
        assert_eq!(*address, source);
        assert_eq!(Some(kind), LoadKind::of_type(ty));
    }
}

#[test]
fn aggregate_copy_names_forgotten_pointer_fields_by_the_complete_typed_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let field = source.offset_by_bytes(8);
    let target = SymbolicMemory::frame_local_pointer(1, "pointer_record_copy");
    for ty in [ProgramType::UInt8Pointer, ProgramType::UInt32Pointer] {
        let layout = AggregateLayout::new(
            16,
            8,
            vec![
                AggregateField::new("tag", 0, ProgramType::UInt32),
                AggregateField::new("link", 8, ty),
            ],
        );
        let domain = Address::symbolic(Variable(986_246));
        let value = Pointer::new(domain.offset_by_bytes(4), ty).with_bounds(Some(
            crate::kernel::SubobjectBounds {
                start: domain,
                width: 16u32.into(),
            },
        ));
        let initial = ExecutionState::new().with_memory(
            SymbolicMemory::new().with_block(target.base.clone(), layout.size_bytes()),
        );
        let stored = initial.clone().with_memory(
            initial
                .memory()
                .clone()
                .store(field.clone(), ProgramValue::Pointer(value.clone())),
        );
        let forgotten = stored.memory().without_possible_aliasing_cells(
            &field,
            ty.byte_width(),
            &PureFactContext::new(),
        );
        let before = stored.clone().with_memory(forgotten);
        assert!(before.memory().known_value(&field).is_none());
        let copied = copy_aggregate_fields_checked_at(&before, &source, &target, &layout).unwrap();
        let Some(ProgramValue::Pointer(read)) = copied.known_value(&target.offset_by_bytes(8))
        else {
            panic!("expected a complete pointer read");
        };
        let descriptor = read.address().as_loaded_value().expect("read pointer");
        assert_eq!(
            descriptor.point.read_version_id(),
            stored.observation_point_id()
        );
        assert_eq!(descriptor.defining_address, field);
        assert_eq!(descriptor.value_type, Some(ty));
        assert_eq!(read.provenance(), read.address());
        assert_eq!(read.bounds_owner(), Some(read.address()));
        assert_eq!(
            crate::kernel::eval::pointer_read_over_write_program_value(read.address()),
            Some(value),
        );
    }
}

#[test]
fn aggregate_copy_union_reads_keep_the_caller_versions() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let source_member = source.offset_by_bytes(8);
    let target = SymbolicMemory::frame_local_pointer(1, "union_record_copy");
    let target_member = target.offset_by_bytes(8);
    let pointer_type = ProgramType::UInt32Pointer;
    let layout = AggregateLayout::with_unions(
        16,
        8,
        vec![AggregateField::new("tag", 0, ProgramType::UInt32)],
        vec![AggregateUnion::new(
            "payload",
            8,
            8,
            vec![
                AggregateUnionField::new("word", 0, ProgramType::Int32),
                AggregateUnionField::new("link", 0, pointer_type),
            ],
        )],
    );
    let entry = ExecutionState::new().begin_function_entry_memory();
    let initial = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(target.base.clone(), layout.size_bytes()),
    );

    let copied = copy_aggregate_fields_checked_at(&initial, &source, &target, &layout).unwrap();
    let Some(ProgramValue::Int32(MachineTerm::MemoryLoad(point, address, kind))) =
        copied.known_union_value(&target_member, ProgramType::Int32)
    else {
        panic!("expected a typed caller word");
    };
    assert_eq!(kind, LoadKind::Int32);
    assert_eq!(point.read_version_id(), entry.program_point_id());
    assert_eq!(*address, source_member);

    let domain = Address::symbolic(Variable(986_247));
    let value = Pointer::new(domain.offset_by_bytes(4), pointer_type).with_bounds(Some(
        crate::kernel::SubobjectBounds {
            start: domain,
            width: 16u32.into(),
        },
    ));
    let stored = initial.clone().with_memory(
        initial
            .memory()
            .clone()
            .store(source_member.clone(), ProgramValue::Pointer(value.clone())),
    );
    let forgotten = stored.memory().without_possible_aliasing_cells(
        &source_member,
        pointer_type.byte_width(),
        &PureFactContext::new(),
    );
    let before = stored.clone().with_memory(forgotten);
    assert!(before.memory().known_value(&source_member).is_none());
    let copied = copy_aggregate_fields_checked_at(&before, &source, &target, &layout).unwrap();
    let Some(ProgramValue::Pointer(read)) = copied.known_union_value(&target_member, pointer_type)
    else {
        panic!("expected a complete pointer read");
    };
    let descriptor = read.address().as_loaded_value().expect("read pointer");
    assert_eq!(
        descriptor.point.read_version_id(),
        stored.observation_point_id()
    );
    assert_eq!(descriptor.defining_address, source_member);
    assert_eq!(descriptor.value_type, Some(pointer_type));
    assert_eq!(
        crate::kernel::eval::pointer_read_over_write_program_value(read.address()),
        Some(value),
    );
}

#[test]
fn verified_aggregate_argument_keeps_caller_entry_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let caller = ExecutionState::new().begin_function_entry_memory();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let layout = AggregateLayout::new(
        4,
        4,
        vec![AggregateField::new("word", 0, ProgramType::Int32)],
    );
    let function = program_function(
        ProgramType::Void,
        "by_value",
        vec![
            ProgramParameter::new("input", ProgramType::VoidPointer).with_aggregate_layout(layout),
        ],
        program_return(program_void_value()),
    );
    let argument = ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer);
    let bound = bind_contract_arguments(
        &caller,
        function.contract_interface(),
        &VerifiedCallArguments::Native(vec![argument.clone()]),
        None,
        &[argument.into()],
        &mut Vec::new(),
    )
    .expect("bind a checked aggregate argument");

    let slot = bound.locals.slot("input").expect("private argument slot");
    let Some(ProgramValue::Int32(MachineTerm::MemoryLoad(point, address, kind))) =
        bound.memory().known_value(slot)
    else {
        panic!("expected a typed caller word");
    };
    assert_eq!(kind, LoadKind::Int32);
    assert_eq!(point.read_version_id(), caller.program_point_id());
    assert_eq!(*address, source);
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
    let pointer = Pointer::new(
        Address::symbolic(Variable(1027800)),
        ProgramType::Int32Pointer,
    );
    let root = KernelTerm::shared_pointer_call(
        KernelTerm::checked_call(
            KernelType::Program(ProgramType::Int32Pointer),
            "copied".into(),
            vec![],
        ),
        crate::kernel::SharedPointer::import(&pointer),
    );
    let memory = SymbolicMemory::new()
        .with_block(source.base.clone(), 8)
        .with_block(target.base.clone(), 8)
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
        &crate::kernel::ProgramPoint::of_memory(&copied),
        target.clone(),
        ProgramType::Int32Pointer,
        ExecutionFacts::new(),
        vec![],
        &PureFactContext::new(),
        false,
        false,
        None,
        None,
        false,
    );
    assert_eq!(paths.len(), 1);
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("union pointer load")
    };
    assert_eq!(value.shared(), Some(&root));
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
