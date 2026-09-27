use super::*;

fn storage_function(name: &str, globals: Vec<CGlobal>) -> CFunction {
    c_function(CType::Int32, name, vec![], c_return(c_int32_literal(0)))
        .with_global_variables(globals)
}

fn scalar_ownership(name: &str) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(
        CMemory::global_pointer(name),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ))
}

#[test]
fn static_declaration_preserves_a_cell_materialized_before_its_block() {
    let function =
        storage_function("increment", vec![]).with_static_variables(vec![CStaticLocal::new(
            "calls",
            "calls",
            CType::Int32,
            int32(5),
        )]);
    let pointer = CMemory::static_pointer("increment", "calls");
    let state = CState::new().with_memory(CMemory::new().store(pointer.clone(), int32(37)));
    assert!(!state.memory().has_block(&pointer.block));
    let initialized = initialize_c_function_globals(&state, &function);
    assert!(initialized.memory().has_block(&pointer.block));
    assert_eq!(
        initialized.memory().load(&pointer),
        CExpressionOutcome::Value(int32(37))
    );
    assert!(initialized.resources().facts().is_empty());
}

#[test]
fn ordinary_function_entry_does_not_restore_static_initializers() {
    let global = CGlobal::new("state", CType::Int32, int32(7));
    let function =
        storage_function("read", vec![global]).with_static_variables(vec![CStaticLocal::new(
            "calls",
            "calls",
            CType::Int32,
            int32(11),
        )]);

    let ordinary = initialize_c_function_globals(&CState::new(), &function);
    assert!(
        ordinary
            .memory()
            .has_block(&CMemory::global_pointer("state").block)
    );
    assert_ne!(
        ordinary.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(7))
    );
    assert!(
        ordinary
            .memory()
            .has_block(&CMemory::static_pointer("read", "calls").block)
    );
    assert_ne!(
        ordinary
            .memory()
            .load(&CMemory::static_pointer("read", "calls")),
        CExpressionOutcome::Value(int32(11))
    );

    let startup = initialize_c_program_storage([function]);
    assert_eq!(
        startup.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("read", "calls")),
        CExpressionOutcome::Value(int32(11))
    );
}

#[test]
fn startup_coalesces_declarations_and_calls_cannot_replenish_ownership() {
    let global = CGlobal::new("state", CType::Int32, int32(7));
    let left = storage_function("left", vec![global.clone()]);
    let right = storage_function("right", vec![global]);
    let startup = initialize_c_program_storage([left.clone(), right]);
    let owned = scalar_ownership("state");
    let assumptions = PureFactContext::new();
    assert_eq!(startup.resources().facts().len(), 1);
    assert!(startup.resources().satisfies_fact(&owned, &assumptions));
    assert!(
        !initialize_c_function_globals(&CState::new(), &left)
            .resources()
            .satisfies_fact(&owned, &assumptions)
    );
    let consumed = startup
        .resources()
        .clone()
        .without_fact(&owned, &assumptions)
        .unwrap();
    assert!(
        consumed
            .clone()
            .without_fact(&owned, &assumptions)
            .is_none()
    );
    let state = startup.with_resource_context(consumed).with_memory(
        initialize_c_function_globals(&CState::new(), &left)
            .memory()
            .clone()
            .store(CMemory::global_pointer("state"), int32(19)),
    );
    let call = initialize_c_function_globals(&state, &left);
    assert!(!call.resources().satisfies_fact(&owned, &assumptions));
    assert_eq!(
        call.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(19))
    );
}

#[test]
fn startup_preserves_private_identities_and_const_permissions() {
    let left = storage_function(
        "left",
        vec![CGlobal::new_with_kernel_name(
            "state",
            "left::state",
            CType::Int32,
            int32(7),
        )],
    );
    let right = storage_function(
        "right",
        vec![
            CGlobal::new_with_kernel_name("state", "right::state", CType::Int32, int32(40))
                .with_constant(true),
        ],
    );
    let state = initialize_c_program_storage([left, right]);
    let assumptions = PureFactContext::new();
    assert_eq!(state.resources().facts().len(), 2);
    assert!(
        state
            .resources()
            .satisfies_fact(&scalar_ownership("left::state"), &assumptions)
    );
    let readonly = scalar_ownership("right::state");
    assert!(!state.resources().satisfies_fact(&readonly, &assumptions));
    assert!(state.resources().satisfies_fact(
        &CResourceFact::View(readonly.resource().clone()),
        &assumptions
    ));
    assert!(!state.locals().contains_name("state"));
}

#[test]
fn startup_permission_partition_visits_scale_with_cells_and_blocks() {
    for count in [16u32, 64, 256] {
        let mut memory = CMemory::new();
        for index in 0..count {
            let pointer = CMemory::global_pointer(&format!("state_{index}"));
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer, int32(7));
        }
        let mut visits = 0;
        let resources = initial_static_resources(&memory, || visits += 1);
        assert_eq!(resources.facts().len(), count as usize);
        assert_eq!(visits, 4 * count);
    }
}

#[test]
fn startup_contract_cannot_be_packaged_as_an_ordinary_rule() {
    let function = storage_function("main", vec![])
        .with_program_entry()
        .with_contract(
            vec![],
            vec![],
            vec![],
            vec![CFunctionContractClaim::body_safety()],
            true,
        );
    assert!(c_recursive_function_contract_hypothesis(function.clone()).is_none());
    assert!(c_external_function_rule(function.clone()).is_none());
    assert!(c_verified_function_rule(function, &[]).is_none());
}

#[test]
fn binding_program_entry_does_not_upgrade_literal_views_to_ownership() {
    let function = storage_function("main", vec![])
        .with_string_literals(vec![CStringLiteral::new("text", vec![b'x', 0])])
        .with_program_entry();
    let startup = initialize_c_program_storage([function.clone()]);
    let entry = initialize_c_function_globals(&startup, &function);
    assert_eq!(entry.resources().facts().len(), 1);
    assert!(entry.resources().facts()[0].is_view());
    let ordinary = initialize_c_function_globals(&CState::new(), &function);
    assert!(ordinary.resources().facts().is_empty());
}

#[test]
fn startup_includes_uncalled_local_statics_and_typed_arrays() {
    let left = storage_function("left", vec![]).with_static_variables(vec![CStaticLocal::new(
        "state",
        "state",
        CType::Int32,
        int32(3),
    )]);
    let right = storage_function("right", vec![]).with_static_variables(vec![CStaticLocal::new(
        "state",
        "state",
        CType::Int32,
        int32(5),
    )]);
    let array = storage_function("array", vec![]).with_global_arrays(vec![
        CGlobalArray::new_with_kernel_name(
            "values",
            "values",
            CType::UInt16,
            2,
            vec![uint16(7), uint16(9)],
        ),
    ]);
    let startup = initialize_c_program_storage([left, right, array]);
    assert_eq!(startup.resources().facts().len(), 3);
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("left", "state")),
        CExpressionOutcome::Value(int32(3))
    );
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("right", "state")),
        CExpressionOutcome::Value(int32(5))
    );
    let owned = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        CMemory::global_pointer("values"),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
        2,
    ));
    assert!(
        startup
            .resources()
            .satisfies_fact(&owned, &PureFactContext::new())
    );
}

/// A zero of each global-array element type, for initializers the symbolic
/// entry below never reads.
fn zero_element(element_type: CType) -> CValue {
    match element_type {
        CType::Int8 => int8(0),
        CType::Int16 => int16(0),
        CType::Int32 => int32(0),
        CType::UInt8 => uint8(0),
        CType::UInt16 => uint16(0),
        CType::UInt32 => uint32(0),
        CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(0)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        pointer => CValue::typed_pointer(Pointer::null(), pointer),
    }
}

fn function_with_global_array(element_type: CType, length: u32) -> CFunction {
    storage_function("read", vec![]).with_global_arrays(vec![CGlobalArray::new_with_kernel_name(
        "buf",
        "buf",
        element_type,
        length,
        vec![zero_element(element_type); length as usize],
    )])
}

/// An ordinary function's entry names every element of a global array it has
/// no initializer authority over by its symbolic entry value. The elements
/// are one run and their access widths one declaration, and together they
/// are exactly what materializing each element by itself leaves: the same
/// cells, and the same width recorded at every element before and after the
/// elements are named one by one.
#[test]
fn a_symbolic_global_array_entry_holds_exactly_the_per_element_cells() {
    for element_type in [
        CType::Int8,
        CType::Int32,
        CType::UInt8,
        CType::UInt16,
        CType::Int64,
        CType::UInt64,
        CType::Int32Pointer,
        CType::UInt8Pointer,
    ] {
        for length in [1u32, 5, 64, 65, 300] {
            crate::kernel::eval::clear_load_variable_registry();
            let function = function_with_global_array(element_type, length);
            let entry = initialize_c_function_globals(&CState::new(), &function);
            let base = CMemory::global_pointer("buf");
            let width = element_type.byte_width();
            assert_eq!(
                entry.memory().cells.representation_len(),
                1,
                "{element_type:?}[{length}] is one run"
            );
            let source =
                crate::kernel::intern_c_memory(symbolic_memory_base(entry.memory(), &base));
            let slot = |index: u32| base.offset_by_bytes(index * width);
            // An object pointer's entry load records no width.
            let expected_width = (!element_type.is_object_pointer()).then_some(width);
            let widths = |memory: &SharedCMemory| {
                (0..length)
                    .map(|index| {
                        (
                            crate::kernel::eval::recorded_load_access_width(memory, &slot(index)),
                            crate::kernel::load_access_width_at_address_or_widest(&slot(index)),
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let declared = widths(&source);
            assert!(
                declared.iter().all(|(exact, _)| *exact == expected_width),
                "{element_type:?}[{length}] declares its widths: {declared:?}"
            );
            let mut reference =
                CMemory::new().with_block_or_read_only(base.block.clone(), length * width, false);
            for index in 0..length {
                reference = materialize_symbolic_cell(reference, &slot(index), element_type);
            }
            assert_eq!(
                entry.memory().cells.logical(),
                reference.cells.logical(),
                "{element_type:?}[{length}] holds the per-element cells"
            );
            // Recording each element's width again, as the per-element path
            // just did, changes no answer: the declaration was those records.
            assert_eq!(widths(&source), declared, "{element_type:?}[{length}]");
            for index in [0, length / 2, length - 1] {
                assert_eq!(
                    entry.memory().load(&slot(index)),
                    reference.load(&slot(index)),
                    "{element_type:?}[{length}] element {index}"
                );
            }
            // A store into the array writes that element alone.
            let stored = zero_element(element_type);
            let written = entry
                .memory()
                .clone()
                .store(slot(length - 1), stored.clone());
            assert_eq!(
                written.load(&slot(length - 1)),
                CExpressionOutcome::Value(stored)
            );
            if length > 1 {
                assert_eq!(written.load(&slot(0)), reference.load(&slot(0)));
            }
        }
    }
}

/// Entering a function that names a global array costs the same whatever
/// the array's declared length. Before runs, every element was materialized
/// as its own cell, named and width-recorded one by one, so a
/// `static char buf[65536]` cost 65,536 cells at every entry.
#[test]
fn a_symbolic_global_array_entry_costs_the_same_whatever_its_length() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            crate::kernel::eval::clear_load_variable_registry();
            let function = function_with_global_array(element_type, length);
            let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
                initialize_c_function_globals(&CState::new(), &function)
            });
            (length, work, entry.memory().cells.representation_len())
        });
        let least = samples
            .iter()
            .map(|(_, work, _)| *work)
            .min()
            .expect("samples");
        let most = samples
            .iter()
            .map(|(_, work, _)| *work)
            .max()
            .expect("samples");
        assert_eq!(
            least, most,
            "{element_type:?} entry work depends on the array's length: {samples:?}"
        );
        assert!(
            samples.iter().all(|(_, _, entries)| *entries == 1),
            "{element_type:?} entry is one run: {samples:?}"
        );
    }
}

/// Entering a function over a global array, collecting the variables its
/// entry state mentions, and one statement's store into an element and read
/// of another cost the same whatever the array's length, and name exactly the
/// elements read. Collecting the entry state's variables used to name every
/// element to find its load variable, so a one-million-element array minted
/// a million load identities at function entry and exhausted the load
/// registry before the first statement.
#[test]
fn a_symbolic_global_array_names_only_the_elements_a_function_reads() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let width = i64::from(element_type.byte_width());
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            // Each sample is its own verification, so none reuses another's
            // named loads or memoized answers.
            let _session = crate::kernel::VerificationSession::enter();
            let function = function_with_global_array(element_type, length);
            let registered = crate::kernel::eval::load_variable_registry_len;
            let before_entry = registered();
            let (entry, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
                let entry = initialize_c_function_globals(&CState::new(), &function);
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_c_state_bitvector_variables(
                    &entry,
                    &mut variables,
                );
                entry
            });
            let entry_named = registered() - before_entry;
            let base = CMemory::global_pointer("buf");
            let element = |index: i64| Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(index * width),
            };
            let before_statement = registered();
            let (read, statement_work) = crate::instrumentation::measure_deterministic_work(|| {
                let stored = entry
                    .memory()
                    .clone()
                    .store(element(5), zero_element(element_type));
                let read = stored.load(&element(6));
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_memory_bitvector_variables(
                    &stored,
                    &mut variables,
                );
                read
            });
            assert!(
                matches!(read, CExpressionOutcome::Value(_)),
                "{element_type:?}[{length}] element 6 reads its entry value: {read:?}"
            );
            let statement_named = registered() - before_statement;
            (
                length,
                entry_work,
                entry_named,
                statement_work,
                statement_named,
            )
        });
        let (_, entry_work, entry_named, statement_work, statement_named) = samples[0];
        assert!(
            samples
                .iter()
                .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                    == (entry_work, entry_named, statement_work, statement_named)),
            "{element_type:?} entry or statement cost depends on the array's length \
             (length, entry work, identities named at entry, statement work, identities \
             named by the statement): {samples:?}"
        );
        assert!(
            statement_named <= 2,
            "{element_type:?} a statement reading one element names at most its load \
             and the stored cell's: {samples:?}"
        );
    }
}
