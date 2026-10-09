//! Compatibility oracles for the existing field-copy result mode. These do
//! not claim that C++ returned construction or destination forwarding is admitted.
use super::*;

fn node_layout() -> CAggregateLayout {
    CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("self", 0, CType::Int32Pointer),
            CAggregateField::new("value", 8, CType::Int32),
        ],
    )
}

fn copy_function() -> CFunction {
    c_function(
        CType::VoidPointer,
        "copy_result",
        vec![c_parameter("source", CType::VoidPointer)],
        c_return(c_variable("source")),
    )
    .with_return_aggregate_layout(node_layout())
}

fn pointer(value: &CValue) -> Pointer {
    let CValue::Pointer(value) = value else {
        panic!("expected an aggregate storage pointer");
    };
    value.pointer().clone()
}

fn destination_procedure(name: &str, body: CStatement) -> CFunction {
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("destination"),
        c_int32_literal(0),
        c_int32_literal(4),
    ));
    c_function(
        CType::Void,
        name,
        vec![
            c_parameter("destination", CType::Int32Pointer),
            c_parameter("input", CType::Int32),
        ],
        c_seq(body, c_return(c_void_value())),
    )
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

// This tests the existing explicit-destination procedure building block,
// without the legacy placeholder-seeding declaration. It does not pass a
// supplied destination off as a by-value aggregate result.
#[test]
fn supplied_constructor_destination_survives_two_procedure_boundaries() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = c_pointer_offset_bytes(c_variable("destination"), 8);
    let constructor = destination_procedure(
        "initialize_node",
        c_seq(
            c_typed_store(
                c_variable("destination"),
                field.clone(),
                CType::Int32Pointer,
            ),
            c_typed_store(field, c_variable("input"), CType::Int32),
        ),
    );
    let forward = destination_procedure(
        "forward_node",
        c_call(
            "initialize_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let outer = destination_procedure(
        "outer_node",
        c_call(
            "forward_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let destination = CMemory::frame_local_pointer(100, "caller_node");
    let memory = CMemory::new().with_block(destination.block.clone(), 16);
    assert!(!memory.has_initialized_bytes_at(&destination, 16));
    let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
        CMemoryRange::new(destination.clone(), 0u32.into(), 4u32.into()),
    ));
    let caller = CState::new()
        .with_memory(memory)
        .with_resource_context(resources);
    let paths = execute_c_function_call_paths(
        &caller,
        &outer,
        &[c_pointer_value(destination.clone()), c_int32_literal(37)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new()
            .with_function(constructor)
            .with_function(forward),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("forwarded constructor execution");
    let [path] = paths.as_slice() else {
        panic!("one constructor path expected");
    };
    let CFunctionOutcome::Return { value, state } = &path.outcome else {
        panic!("constructor failed: {:?}", path.outcome);
    };
    assert_eq!(*value, CValue::Void);
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    assert_eq!(
        state.memory.known_value(&destination),
        Some(CValue::typed_pointer(
            destination.offset_by_bytes(8),
            CType::Int32Pointer,
        )),
    );
    assert_eq!(
        state.memory.known_value(&destination.offset_by_bytes(8)),
        Some(CValue::Int32(Bitvector32Term::Constant(37))),
    );
    assert_eq!(state.next_local_frame, caller.next_local_frame);
    assert!(state.memory.has_block(&destination.block));
}

// C++ copy-assignment coverage does not exercise the function return
// materializer. A future destination-return path must not silently change
// this existing copy mode to rebase self-pointers or elide its copies.
#[test]
fn aggregate_copy_return_preserves_self_pointer_through_two_materializations() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "node");
    let self_pointer = CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer);
    let memory = CMemory::new()
        .with_block(source.block.clone(), 16)
        .store(source.clone(), self_pointer.clone())
        .store(
            source.offset_by_bytes(8),
            CValue::Int32(Bitvector32Term::Constant(37)),
        );
    let mut state = CState::new().with_memory(memory);
    let function = copy_function();
    let first = materialize_aggregate_return(
        &mut state,
        &function,
        CValue::typed_pointer(source.clone(), CType::VoidPointer),
    )
    .expect("first copy result");
    let second = materialize_aggregate_return(&mut state, &function, first.clone())
        .expect("second copy result");
    assert_ne!(pointer(&first).block, source.block);
    assert_ne!(pointer(&second).block, pointer(&first).block);
    for result in [&first, &second] {
        let result = pointer(result);
        assert_eq!(
            state.memory.known_value(&result),
            Some(self_pointer.clone())
        );
        assert_ne!(pointer(&self_pointer), result.offset_by_bytes(8));
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(CValue::Int32(Bitvector32Term::Constant(37))),
        );
    }
}

// Retiring a copied descriptor's callee-local source must distinguish a
// self-pointer from an external backing pointer. Keeping the result alive
// must neither rescue the former allocation nor retire the latter.
#[test]
fn aggregate_copy_return_retirement_preserves_only_independently_live_backing() {
    for points_to_self in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::frame_local_pointer(100, "descriptor");
        let backing = CMemory::frame_local_pointer(101, "caller_backing");
        let caller = CMemory::new().with_block(backing.block.clone(), 4).store(
            backing.clone(),
            CValue::Int32(Bitvector32Term::Constant(23)),
        );
        let referent = if points_to_self {
            source.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        let field = CValue::typed_pointer(referent.clone(), CType::Int32Pointer);
        let memory = caller
            .clone()
            .with_block(source.block.clone(), 16)
            .store(source.clone(), field.clone())
            .store(
                source.offset_by_bytes(8),
                CValue::Int32(Bitvector32Term::Constant(23)),
            );
        let mut state = CState::new().with_memory(memory);
        state.locals.set_aggregate_object_at(
            "descriptor".to_string(),
            node_layout(),
            source.clone(),
        );
        let function = copy_function();
        let result = materialize_aggregate_return(
            &mut state,
            &function,
            CValue::typed_pointer(source.clone(), CType::VoidPointer),
        )
        .expect("copy result");
        set_function_result(&mut state, &function, result.clone());
        let memory =
            end_function_body_automatic_lifetimes(&state, &function, &caller, Some(&result))
                .expect("callee retirement");
        assert!(!memory.has_block(&source.block));
        assert!(memory.has_block(&pointer(&result).block));
        assert!(memory.has_block(&backing.block));
        assert_eq!(memory.known_value(&pointer(&result)), Some(field));
        assert_eq!(memory.has_block(&referent.block), !points_to_self);
        assert_eq!(
            memory.known_value(&backing),
            Some(CValue::Int32(Bitvector32Term::Constant(23))),
        );
    }
}

// Modular field-copy results intentionally have fresh identities. The new
// construction mode needs a different binding; changing this helper globally
// would break existing C framing and would conceal destination aliasing.
#[test]
fn aggregate_copy_symbolic_result_has_a_fresh_identity_per_call() {
    let _session = crate::kernel::VerificationSession::enter();
    let function = copy_function();
    let first = symbolic_contract_result(function.contract_interface(), Variable(870_001));
    let second = symbolic_contract_result(function.contract_interface(), Variable(870_002));
    assert!(matches!(pointer(&first).block, PointerBlock::Temporary(_)));
    assert!(matches!(pointer(&second).block, PointerBlock::Temporary(_)));
    assert_ne!(pointer(&first).block, pointer(&second).block);
}

// Return completion must reject before allocating a result or copying any
// prefix. The two body-completion paths must not supply separate, drifting
// checks for this precondition.
#[test]
fn aggregate_copy_return_refuses_partial_initialization_without_changing_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "partial");
    let mut state =
        CState::new().with_memory(CMemory::new().with_block(source.block.clone(), 16).store(
            source.clone(),
            CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer),
        ));
    let before = state.clone();
    assert_eq!(
        materialize_aggregate_return(
            &mut state,
            &copy_function(),
            CValue::typed_pointer(source, CType::VoidPointer),
        ),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    assert_eq!(state, before);
}

// Symbolic proof-entry destinations must not inherit the existing convention
// that unspecified external argument memory is initialized. This is the
// completion check's negative oracle before adding the new result mode.
#[test]
fn symbolic_construction_storage_requires_written_fields_before_copy_return() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_003));
    let mut state = CState::new()
        .with_memory(CMemory::new().with_uninitialized_block(source.block.clone(), 16));
    let value = CValue::typed_pointer(source.clone(), CType::VoidPointer);
    assert_eq!(
        materialize_aggregate_return(&mut state, &copy_function(), value.clone()),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.clone(),
        CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer),
    ));
    assert_eq!(
        materialize_aggregate_return(&mut state, &copy_function(), value.clone()),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.offset_by_bytes(8),
        CValue::Int32(Bitvector32Term::Constant(37)),
    ));
    assert!(materialize_aggregate_return(&mut state, &copy_function(), value).is_ok());
}

#[test]
fn symbolic_construction_storage_is_unreadable_until_written() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_004));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    for (mode, assumptions) in [
        ("ordinary", PureFactContext::new()),
        (
            "preferred",
            PureFactContext::new().prefer_symbolic_external_loads(),
        ),
        (
            "forced",
            PureFactContext::new().force_symbolic_external_loads(),
        ),
    ] {
        for written in [false, true] {
            let memory = if written {
                raw.clone()
                    .store(source.clone(), CValue::Int32(Bitvector32Term::Constant(37)))
            } else {
                raw.clone()
            };
            let state = CState::new().with_memory(memory).with_resource_context(
                ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new(source.clone(), 0u32.into(), 1u32.into()),
                )),
            );
            let paths = execute_c_statement_paths(
                &state,
                &c_return(c_typed_load(c_pointer_value(source.clone()), CType::Int32)),
                &assumptions,
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            )
            .expect("raw destination read");
            let [path] = paths.as_slice() else {
                panic!("expected one read path");
            };
            if written {
                assert!(matches!(path.outcome, CStatementOutcome::Return { .. }));
            } else {
                assert!(
                    matches!(
                        path.outcome,
                        CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                    ),
                    "{mode}: {:?}",
                    path.outcome
                );
            }
        }
    }
}

// A supplied destination may alias an ordinary input. That equality must
// neither make unwritten storage readable nor hide a write through the alias.
#[test]
fn symbolic_construction_storage_respects_known_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_005));
    let alias = Pointer::symbolic(Variable(870_006));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(source.clone(), alias.clone()),
        true,
    );
    for forgotten in [false, true] {
        for written in [false, true] {
            for read in [&source, &alias] {
                let mut memory = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
                if written {
                    memory = memory.store(alias.clone(), CValue::Int32(37u32.into()));
                }
                if forgotten {
                    memory = memory.with_loop_memory_havoc_preserving_loans(
                        Variable(870_020),
                        &BTreeSet::new(),
                        None,
                        None,
                    );
                }
                let state = CState::new().with_memory(memory).with_resource_context(
                    ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                        CMemoryRange::new(source.clone(), 0u32.into(), 1u32.into()),
                    )),
                );
                let paths = execute_c_statement_paths(
                    &state,
                    &c_return(c_typed_load(c_pointer_value(read.clone()), CType::Int32)),
                    &assumptions,
                    &CExecutionEnvironment::new(),
                    CExecutionSemantics::EXECUTE_BODIES,
                    &mut ExecutionBudget::default(),
                )
                .expect("aliased destination read");
                assert!(!paths.is_empty());
                for path in paths {
                    if written {
                        assert!(
                            matches!(path.outcome, CStatementOutcome::Return { .. }),
                            "{:?}",
                            path.outcome
                        );
                    } else {
                        assert!(
                            matches!(
                                path.outcome,
                                CStatementOutcome::UndefinedBehavior(
                                    CUndefinedBehavior::UninitializedRead
                                )
                            ),
                            "{:?}",
                            path.outcome
                        );
                    }
                }
            }
        }
    }
}

// Resource projection is a logical name, not a constructor store, including
// when the resource uses another spelling that could alias the destination.
#[test]
fn naming_symbolic_construction_storage_does_not_initialize_it() {
    let source = Pointer::symbolic(Variable(870_007));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    for address in [source.clone(), Pointer::symbolic(Variable(870_008))] {
        let named = raw
            .clone()
            .materialize_named_cell(address.clone(), CValue::Int32(37u32.into()));
        assert_eq!(named, raw);
        assert!(!named.has_initialized_bytes_at(&address, 4));
    }
}

// Forgetting values preserves writes; a branch that skipped the write still
// prevents the joined destination from counting as completely initialized.
#[test]
fn symbolic_construction_initialization_survives_havoc_and_intersects_at_join() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_009));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 8);
    let partial = raw
        .clone()
        .store(source.clone(), CValue::Int32(37u32.into()));
    let full = partial
        .clone()
        .store(source.offset_by_bytes(4), CValue::Int32(42u32.into()));
    let forgotten = full.with_loop_memory_havoc_preserving_loans(
        Variable(870_010),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(forgotten.has_initialized_bytes_at(&source, 8));
    assert!(forgotten.may_read_uninitialized_object(&source, 8));
    assert!(forgotten.known_value(&source).is_none());
    let joined = forgotten
        .clone()
        .with_interface_memory_havoc(Variable(870_011), &BTreeSet::new(), &[&forgotten, &partial])
        .expect("construction initialization join");
    assert!(joined.has_initialized_bytes_at(&source, 4));
    assert!(!joined.has_initialized_bytes_at(&source, 8));
    assert!(joined.may_read_uninitialized_object(&source, 8));
}

// Substitution retains the byte footprint even at a nonzero offset. This
// metadata does not authorize resizing the caller object or subobject construction.
#[test]
fn symbolic_construction_initialization_substitution_preserves_extent() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(870_012);
    let source = Pointer::symbolic(variable);
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    let destination = CMemory::frame_local_pointer(20, "container").offset_by_bytes(8);
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_memory(
        &raw,
        variable,
        &destination,
    );
    assert!(mapped.may_read_uninitialized_object(&destination, 4));
    assert!(!mapped.may_read_uninitialized_object(&destination.offset_by_bytes(4), 4));
    assert!(!mapped.may_read_uninitialized_object(
        &CMemory::frame_local_pointer(20, "container").offset_by_bytes(4),
        4
    ));
    assert!(!mapped.has_initialized_bytes_at(&destination, 4));
}

// Query work is bounded by potentially aliasing tracked objects, not other
// caller allocations. Concrete unrelated raw objects are excluded by the index.
#[test]
fn construction_initialization_lookup_ignores_unrelated_caller_storage() {
    let mut work_by_size = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::frame_local_pointer(21, "construction");
        let mut memory = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
        for index in 0..count {
            memory = memory.with_uninitialized_block(format!("local:unrelated:{index}"), 4);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.may_read_uninitialized_object(&source, 4)
        });
        assert!(result);
        work_by_size.push(work);
    }
    assert!(
        work_by_size
            .iter()
            .all(|work| *work <= work_by_size[0].max(1) * 2),
        "{work_by_size:?}"
    );
}

// Instantiating an object can put a variable only in its byte offset. Both
// whole and incremental collectors must reserve it against fresh witnesses.
#[test]
fn construction_object_offsets_participate_in_fresh_variable_collection() {
    let _session = crate::kernel::VerificationSession::enter();
    let source_variable = Variable(870_013);
    let offset_variable = Variable(870_014);
    let source = Pointer::symbolic(source_variable);
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    let destination = Pointer {
        block: "local:variable-container".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(offset_variable), 4),
    };
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_memory(
        &raw,
        source_variable,
        &destination,
    );
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&mapped, &mut whole);
    assert!(whole.contains(&offset_variable));
    assert!(!whole.contains(&source_variable));
    let before = crate::kernel::intern_c_memory(mapped.clone());
    let mut cached = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&before, &mut cached);
    assert_eq!(cached, whole);
    let after = crate::kernel::intern_c_memory(mapped.store(
        CMemory::frame_local_pointer(22, "unrelated"),
        CValue::Int32(37u32.into()),
    ));
    let mut updated = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&after, &mut updated);
    assert_eq!(updated, whole);
}

// Neither compact resource naming nor a claimed havoc edge may manufacture
// initialization or discard the marker that requires it.
#[test]
fn construction_initialization_cannot_be_erased_or_seeded_by_a_proof_shortcut() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_015));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    assert!(
        raw.clone()
            .with_symbolic_storage_run(
                source.clone(),
                CType::Int32,
                1,
                crate::kernel::intern_c_memory(raw.clone())
            )
            .is_err()
    );
    let assumptions = PureFactContext::new();
    let mut havoc = raw
        .clone()
        .with_call_memory_havoc(Variable(870_016), &[], &assumptions, None);
    assert!(havoc.matches_call_memory_havoc_result(&raw, &[], &assumptions, None));
    Arc::make_mut(&mut havoc.heap).uninitialized_objects.clear();
    assert!(!havoc.matches_call_memory_havoc_result(&raw, &[], &assumptions, None));
}

// An actual write can use an alias whose variable survives only in the byte
// initialization record after havoc. Fresh witnesses must not reuse it.
#[test]
fn forgotten_construction_writes_keep_their_address_variables_reserved() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_017));
    let alias_variable = Variable(870_018);
    let alias = Pointer::symbolic(alias_variable);
    let written = CMemory::new()
        .with_uninitialized_block(source.block.clone(), 4)
        .store(alias.clone(), CValue::Int32(37u32.into()));
    let before = crate::kernel::intern_c_memory(written.clone());
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&before, &mut variables);
    assert!(variables.contains(&alias_variable));
    let forgotten = written.with_loop_memory_havoc_preserving_loans(
        Variable(870_019),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(forgotten.known_value(&alias).is_none());
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&forgotten, &mut whole);
    let mut cached = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(
        &crate::kernel::intern_c_memory(forgotten),
        &mut cached,
    );
    assert!(cached.contains(&alias_variable));
    assert_eq!(whole, cached);
}
