use super::*;
use crate::kernel::prelude::*;

fn pending_malloc(state: &CState) -> CState {
    let paths = execute_c_statement_paths(
        state,
        &c_heap_allocate("p", 16),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("actual malloc statement executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("expected one pending allocation path");
    };
    pending.clone()
}

fn resolved_malloc(pending: &CState, success: bool) -> CState {
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        panic!("pending allocation has a result pointer");
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
        !success,
    ));
    crate::kernel::resolve_pending_heap_allocations(pending, &assumptions)
}

#[test]
fn only_successful_real_malloc_records_creation() {
    let entry = CState::new()
        .with_local("p", CValue::pointer(Pointer::null()))
        .with_population_creation_tracking();
    let pending = pending_malloc(&entry);
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    assert!(!pending.population_storage_created_here(pending_pointer));

    let failed = resolved_malloc(&pending, false);
    let Some(CValue::Pointer(failed_pointer)) = failed.locals().get("p") else {
        unreachable!();
    };
    assert!(!failed.population_storage_created_here(failed_pointer));

    let succeeded = resolved_malloc(&pending, true);
    let Some(CValue::Pointer(created)) = succeeded.locals().get("p") else {
        unreachable!();
    };
    assert!(succeeded.population_storage_created_here(created));
    assert!(!entry.population_storage_created_here(created));
    assert!(!succeeded.population_storage_created_here(&created.pointer().offset_by_bytes(4)));
    assert_eq!(
        succeeded
            .clone()
            .with_population_creation_tracking()
            .population_effects
            .creation,
        succeeded.population_effects.creation,
        "opt-in cannot reset a live provenance ledger"
    );

    let imported = CState::new()
        .with_population_creation_tracking()
        .with_memory(
            CMemory::new()
                .with_heap_allocation_claim(created.pointer().clone(), 16)
                .expect("assumed allocation claim"),
        );
    assert!(!imported.population_storage_created_here(created));

    let helper = c_function(
        CType::Void,
        "helper",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_void_value()),
    );
    let callee = bind_c_function_arguments(
        &succeeded,
        &helper,
        &[CValue::pointer(created.pointer().clone())],
    )
    .expect("bind actual helper environment");
    let Some(CValue::Pointer(copied)) = callee.locals().get("q") else {
        unreachable!();
    };
    assert!(!callee.population_storage_created_here(copied));
    let returned = callee
        .population_effects
        .creation
        .as_ref()
        .expect("callee ledger")
        .return_to(
            succeeded
                .population_effects
                .creation
                .as_ref()
                .expect("caller ledger"),
        );
    let mut resumed = succeeded.clone();
    Arc::make_mut(&mut resumed.population_effects).creation = Some(returned);
    assert!(resumed.population_storage_created_here(created));
    assert_ne!(
        resumed.population_effects.creation, succeeded.population_effects.creation,
        "a call return advances invocation identity even when its ownership is unchanged"
    );
    assert_eq!(
        resumed
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&created.block),
        succeeded
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&created.block),
        "the new identity preserves the caller's creation right"
    );

    let freed = execute_c_statement_paths(
        &succeeded,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("free executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after_free),
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("free should consume allocation and storage");
    };
    assert!(!after_free.population_storage_created_here(created));

    let legacy = resolved_malloc(
        &pending_malloc(&CState::new().with_local("p", CValue::pointer(Pointer::null()))),
        true,
    );
    assert!(legacy.population_effects.creation.is_none());
}

#[test]
fn caller_pending_malloc_resolved_in_helper_keeps_caller_origin() {
    let caller = CState::new()
        .with_local("p", CValue::pointer(Pointer::null()))
        .with_population_creation_tracking();
    let pending = pending_malloc(&caller);
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    let helper = c_function(
        CType::Int32,
        "resolve_in_helper",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_if(
            c_variable("q"),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        ),
    );
    let callee = bind_c_function_arguments(
        &pending,
        &helper,
        &[CValue::pointer(pending_pointer.pointer().clone())],
    )
    .expect("bind actual helper environment");
    let paths = execute_c_statement_paths(
        &callee,
        helper.body(),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("helper decides caller's pending malloc result");
    assert_eq!(paths.len(), 2);
    let mut saw_success = false;
    let mut saw_failure = false;
    for path in paths {
        let CStatementOutcome::Return { value, state } = path.outcome else {
            panic!("helper must return from both branches");
        };
        let Some(CValue::Pointer(pointer)) = state.locals().get("q") else {
            panic!("helper retains its resolved parameter");
        };
        assert!(!state.memory().has_pending_heap_allocation());
        assert!(!state.population_storage_created_here(pointer));

        let mut resumed = pending.clone().with_memory(state.memory().clone());
        resumed.restore_population_creation_after_call(
            pending.population_effects.creation.as_ref(),
            state.population_effects.creation.as_ref(),
        );
        if pointer.pointer() == &Pointer::null() {
            saw_failure = true;
            assert_eq!(value, CValue::Int32(0.into()));
            assert!(!resumed.population_storage_created_here(pointer));
        } else {
            saw_success = true;
            assert_eq!(value, CValue::Int32(1.into()));
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            assert!(resumed.population_storage_created_here(pointer));
        }
    }
    assert!(saw_success && saw_failure);
}

#[test]
fn creation_lookup_and_call_transport_ignore_unrelated_events() {
    let sizes = [64_u64, 256, 1024];
    let mut work = Vec::new();
    for size in sizes {
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events.created(PointerBlock::Heap(id));
            events = events.member_created(&PointerBlock::Heap(id), "reference");
            events = events.pending_creation(PointerBlock::Symbolic(Variable(id)));
        }
        let selected = PointerBlock::Heap(size / 2);
        let pending_block = PointerBlock::Symbolic(Variable(10_000 + size));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.created_here(&selected));
            assert_eq!(
                events.establish(&selected, "reference"),
                Err(CreationRefusal::MembersAlreadyExisted)
            );
            assert!(events.establish(&selected, "other").is_ok());
            let callee = events.enter_call();
            assert!(!callee.created_here(&selected));
            assert!(callee.return_to(&events).created_here(&selected));
            let started = events.pending_creation(pending_block.clone());
            let resolved = started
                .enter_call()
                .resolve_pending(&pending_block, Some(PointerBlock::Heap(size)));
            assert!(!resolved.created_here(&PointerBlock::Heap(size)));
            assert!(
                resolved
                    .return_to(&events)
                    .created_here(&PointerBlock::Heap(size))
            );
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn actual_stack_declaration_grants_one_lifetime_creation_event() {
    let entry = CState::new().with_population_creation_tracking();
    let paths = execute_c_statement_paths(
        &entry,
        &c_declare("x", CType::Int32),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("declaration executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(declared),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("one declaration path");
    };
    let slot = declared.locals().slot("x").expect("declared slot").clone();
    assert!(declared.population_storage_created_here(&slot));
    assert!(!entry.population_storage_created_here(&slot));
    assert!(!declared.population_storage_created_here(&slot.offset_by_bytes(1)));

    let ended = crate::kernel::eval::end_scope_automatic_lifetimes(declared, &["x".to_owned()])
        .expect("scope exit");
    assert!(!ended.population_storage_created_here(&slot));
    let second = execute_c_statement_paths(
        &ended,
        &c_declare("x", CType::Int32),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("re-enter declaration");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(second),
            ..
        },
    ] = second.as_slice()
    else {
        panic!("one re-entry path");
    };
    let second_slot = second.locals().slot("x").expect("new slot");
    assert_ne!(slot.block, second_slot.block);
    assert!(second.population_storage_created_here(second_slot));
    assert!(!second.population_storage_created_here(&slot));
}

#[test]
fn member_history_blocks_late_establishment_after_transfer_and_return() {
    let block = PointerBlock::Heap(940_100);
    let caller = CreationEvents::new().created(block.clone());
    let moved = caller.member_created(&block, "reference");
    let helper = moved.enter_call();
    assert_eq!(
        helper.establish(&block, "reference"),
        Err(CreationRefusal::NotCreationEnvironment),
    );
    let resumed = helper.return_to(&caller);
    assert_eq!(
        resumed.establish(&block, "reference"),
        Err(CreationRefusal::MembersAlreadyExisted),
    );
    let established_other = resumed
        .establish(&block, "other")
        .expect("unrelated family remains pristine");
    assert_eq!(
        established_other.establish(&block, "other"),
        Err(CreationRefusal::AlreadyEstablished),
    );
    assert_eq!(
        established_other.retired(&block),
        Err(CreationRefusal::OutstandingAuthority),
    );
    let retired_other = established_other
        .retire_authority(&block, "other")
        .expect("zero-member authority retires");
    let ended = retired_other.retired(&block).expect("empty lifetime ends");
    assert_eq!(
        ended.establish(&block, "other"),
        Err(CreationRefusal::NotCreationEnvironment),
    );
}

#[test]
fn pending_member_history_follows_actual_malloc_result() {
    let pending = PointerBlock::Symbolic(Variable(940_101));
    let live = PointerBlock::Heap(940_102);
    let caller = CreationEvents::new()
        .pending_creation(pending.clone())
        .member_created(&pending, "reference");
    let helper = caller.enter_call();
    let decided = helper.resolve_pending(&pending, Some(live.clone()));
    let resumed = decided.return_to(&caller);
    assert_eq!(
        resumed.establish(&live, "reference"),
        Err(CreationRefusal::MembersAlreadyExisted),
    );
    assert!(resumed.establish(&live, "other").is_ok());
}

#[test]
fn storage_cannot_expire_with_outstanding_population_authority() {
    let block = PointerBlock::Heap(940_103);
    let created = CreationEvents::new().created(block.clone());
    let established = created
        .establish(&block, "reference")
        .expect("creation environment establishes empty population");
    assert_eq!(
        established.retirement_refusal(&block),
        Some(CreationRefusal::OutstandingAuthority)
    );
    assert_eq!(
        established.retired(&block),
        Err(CreationRefusal::OutstandingAuthority)
    );
    let retired = established
        .retire_authority(&block, "reference")
        .expect("zero-member authority retires")
        .retired(&block)
        .expect("empty storage lifetime retires");
    assert!(!retired.created_here(&block));
}

#[test]
fn repeated_entry_recheck_reuses_the_same_creation_environment() {
    let caller = CreationEvents::new();
    let first = caller.enter_call();
    assert_eq!(first, caller.enter_call());
    assert_ne!(first, caller);
    let advanced = caller.created(PointerBlock::Heap(940_104));
    assert_ne!(first, advanced.enter_call());
}

#[test]
fn rechecking_c_creation_events_reuses_exact_successor_roots() {
    let live = PointerBlock::Heap(940_107);
    let start = CreationEvents::new();
    assert_eq!(start.created(live.clone()), start.created(live));

    let pending = PointerBlock::Symbolic(Variable(940_108));
    let first = start.pending_creation(pending.clone());
    assert_eq!(first, start.pending_creation(pending.clone()));
    let resolved = first.resolve_pending(&pending, Some(PointerBlock::Heap(940_109)));
    assert_eq!(
        resolved,
        first.resolve_pending(&pending, Some(PointerBlock::Heap(940_109)))
    );
}

fn member_description(block: PointerBlock) -> ResourceDescription {
    ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block,
                offset: PointerOffsetTerm::Constant(0),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    )
}

#[test]
fn opaque_helper_import_has_no_count_and_exchanges_one_member() {
    let description = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_110)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    assert!(entry.owns_population_authority(&description));
    assert!(entry.owns_population_member(&description));
    let proof_entry = entry.enter_proof_entry();
    assert!(proof_entry.owns_population_authority(&description));
    assert_eq!(proof_entry, entry.enter_proof_entry());
    let nested_call = proof_entry.enter_call();
    assert!(!nested_call.owns_population_authority(&description));
    assert!(!nested_call.owns_population_member(&description));
    assert_eq!(
        entry.observe(&PointerBlock::ExternalArgument, "reference"),
        Err(CreationRefusal::UnknownTotal)
    );
    let (retained, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("retain may add one member while already holding a member");
    assert!(retained.born_imported_member_since(&entry, &description));
    assert!(retained.observe_symbolic(&description).is_none());
    assert!(matches!(
        retained.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::MissingMembers)
    ));
    let (restored, _) = retained
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(restored.owns_population_member(&description));
    assert_eq!(
        restored.imported_member_delta_since_entry(&description),
        None
    );
    let two = CreationEvents::new()
        .import_opaque_contract_population(&description, 2)
        .unwrap();
    let (one, _) = two
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(one.spent_imported_member_since(&two, &description));
    assert!(one.owns_population_member(&description));
    assert!(matches!(
        one.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let empty = CreationEvents::new()
        .import_opaque_contract_population(&description, 0)
        .unwrap();
    let (born, _) = empty
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("an opaque helper can birth its exact member once");
    assert!(born.born_imported_member_since(&empty, &description));
    assert!(born.owns_population_member(&description));
    assert!(matches!(
        born.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::MissingMembers)
    ));
    let (spent, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .expect("an opaque helper can spend its exact imported member once");
    assert!(spent.spent_imported_member_since(&entry, &description));
    assert!(!spent.owns_population_member(&description));
    assert!(matches!(
        spent.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let other = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_111)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let both = entry.import_opaque_contract_population(&other, 1).unwrap();
    assert!(both.owns_population_authority(&description));
    assert!(both.owns_population_member(&other));
    let (spent_first, _) = both
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(!spent_first.owns_population_member(&description));
    assert!(spent_first.owns_population_member(&other));
    assert!(!spent_first.spent_imported_member_since(&both, &other));
    let (spent_second, _) = spent_first
        .checked_member_exchange(&PointerBlock::ExternalArgument, &other, false)
        .unwrap();
    assert!(spent_second.spent_imported_member_since(&spent_first, &other));
    assert!(!spent_second.spent_imported_member_since(&spent_first, &description));
    assert_eq!(
        both.import_opaque_contract_population(&description, 0),
        Err(CreationRefusal::OpaqueImportConflict)
    );

    let authority = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(
            ResourceContext::new().unchecked_with_facts([authority.clone(), member]),
        );
    assert!(!state.recognizes_population_authority(&description));
    let imported = state.import_opaque_population(&authority, 1).unwrap();
    assert!(imported.recognizes_population_authority(&description));
    assert!(
        imported
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .observe_symbolic(&description)
            .is_none()
    );
}

#[test]
fn opaque_symbolic_batch_has_one_checked_exchange_and_current_custody() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Constant(5);
    let assumptions = PureFactContext::new();
    let held = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(quantity.clone()),
            Some(quantity.clone()),
            None,
        )
        .unwrap();
    assert!(held.owns_population_member(&description));
    assert!(matches!(
        held.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::InvalidQuantity)
    ));
    let (spent, _) = held
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(!spent.owns_population_member(&description));
    assert!(matches!(
        spent.checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        ),
        Err(CreationRefusal::InvalidQuantity)
    ));

    let empty = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(0)),
            None,
            None,
        )
        .unwrap();
    let (born, _) = empty
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            true,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(born.owns_population_member(&description));
    assert!(matches!(
        born.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::InvalidQuantity)
    ));
}

#[test]
fn independent_opaque_symbolic_populations_keep_their_own_counts_and_members() {
    let first = member_description(PointerBlock::ExternalArgument);
    let second = ResourceDescription::new(
        "other_reference".into(),
        first.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let first_quantity = Bitvector32Term::Constant(3);
    let second_quantity = Bitvector32Term::Constant(5);
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &first,
            0,
            Some(Bitvector32Term::Constant(7)),
            Some(first_quantity.clone()),
            None,
        )
        .unwrap()
        .import_opaque_contract_population_inner(
            &second,
            0,
            Some(Bitvector32Term::Constant(11)),
            Some(second_quantity.clone()),
            None,
        )
        .unwrap();
    let (spent, _) = entry
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &first,
            false,
            &first_quantity,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(!spent.owns_population_member(&first));
    assert!(spent.owns_population_member(&second));
    assert_eq!(
        spent
            .observe_symbolic(&first)
            .unwrap()
            .entry_count
            .as_const(),
        Some(7)
    );
    assert_eq!(
        spent
            .observe_symbolic(&second)
            .unwrap()
            .entry_count
            .as_const(),
        Some(11)
    );
    assert!(spent.imported_member_delta_since_entry(&second).is_none());
    let (spent_both, _) = spent
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &second,
            false,
            &second_quantity,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(
        spent_both.imported_member_delta_since_entry(&first),
        Some((false, first_quantity))
    );
    assert_eq!(
        spent_both.imported_member_delta_since_entry(&second),
        Some((false, second_quantity))
    );
}

#[test]
fn opaque_population_lookup_and_exchange_ignore_unrelated_imports() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(950_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events
                .import_opaque_contract_population_inner(
                    &description_at(id),
                    1,
                    Some(Bitvector32Term::Constant(3)),
                    None,
                    None,
                )
                .unwrap();
        }
        let selected = description_at(size / 2);
        let neighbor = description_at(size / 2 + 1);
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.owns_population_authority(&selected));
            assert_eq!(events.observe_symbolic(&selected).unwrap().delta, 0);
            let (spent, _) = events
                .checked_member_exchange(&PointerBlock::ExternalArgument, &selected, false)
                .unwrap();
            assert_eq!(spent.observe_symbolic(&selected).unwrap().delta, -1);
            assert_eq!(spent.observe_symbolic(&neighbor).unwrap().delta, 0);
            assert!(spent.spent_imported_member_since(&events, &selected));
            assert!(!spent.spent_imported_member_since(&events, &neighbor));
            assert!(
                spent
                    .enter_proof_entry()
                    .owns_population_authority(&selected)
            );
            assert!(!spent.enter_call().owns_population_authority(&selected));
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn checked_control_import_observes_only_its_exact_entry_population() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(940_112)),
    };
    let selected = CResourceFact::own(CResource::Composite {
        name: "control".into(),
        arguments: vec![CValue::pointer(pointer.clone()).into()].into(),
    });
    let reference = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "reference".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(reference),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let cell = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::PointerOffset {
            pointer: Box::new(SpecExpression::CExpression(c_variable("p"))),
            elements: Box::new(SpecExpression::Value(int32(0))),
            byte_width: 4,
        }),
        value_type: CType::Int32,
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::CExpression(c_variable("p")))],
    };
    let definition = CCompositeResourceDefinition::new(
        "control",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            authority,
        ],
        vec![SpecProposition::Comparison {
            left: cell,
            operator: CComparisonOperator::Equal,
            right: count,
        }],
    );
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let entry = state.population_effects.creation.as_ref().unwrap();
    let imported = entry
        .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
        .expect("checked control body authenticates its entry count");
    let description = ResourceDescription::new(
        "reference".into(),
        vec![CValue::pointer(pointer.clone()).into()].into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let observed = imported.observe_symbolic(&description).unwrap();
    let wrong_population = ResourceDescription::new(
        "other_reference".into(),
        description.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(imported.observe_symbolic(&wrong_population).is_none());
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let retiring_state = state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_facts([selected.clone(), member]),
    );
    let retiring_entry = retiring_state.population_effects.creation.as_ref().unwrap();
    let imported_with_member = retiring_entry
        .import_checked_control_wrapper(
            &retiring_state,
            &selected,
            &definition,
            &PureFactContext::new(),
        )
        .unwrap();
    let (spent, _) = imported_with_member
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    let retirement_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(spent.observe_symbolic(&description).unwrap().entry_count),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            true,
        ));
    assert!(
        spent
            .checked_retire_imported(&description, &PureFactContext::new())
            .is_err()
    );
    let (retired, _) = spent
        .checked_retire_imported(&description, &retirement_assumptions)
        .unwrap();
    assert!(!retired.owns_population_authority(&description));
    assert_eq!(observed.delta, 0);
    assert_eq!(observed.entry_owned_members, 0);
    assert!(
        matches!(observed.entry_count, Bitvector32Term::MemoryLoad(_, loaded) if *loaded == pointer)
    );
    let count_expression = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(CValue::pointer(
            pointer.clone(),
        )))],
    };
    let evaluate_count = |state: &CState| {
        crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &count_expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut ExecutionBudget::default(),
        )
    };
    let mut folded = state.clone();
    Arc::make_mut(&mut folded.population_effects).creation = Some(imported.clone());
    let folded_paths = evaluate_count(&folded).expect("owned control opens for a count read");
    assert!(folded.resources().contains_exact_representation(&selected));
    assert_eq!(folded.resources().facts().len(), 1);
    let absent_control = folded.clone().with_resource_context(ResourceContext::new());
    assert!(evaluate_count(&absent_control).is_err());
    let viewed_control = folded.clone().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::View(selected.resource().clone())),
    );
    assert!(evaluate_count(&viewed_control).is_err());
    let unrelated_control = CResourceFact::own(CResource::Composite {
        name: "other_control".into(),
        arguments: wrong_population.arguments().to_vec().into(),
    });
    // A different definition cannot substitute for the authenticated head,
    // even when its C argument is identical.
    assert!(
        evaluate_count(
            &folded.clone().with_resource_context(
                ResourceContext::new().unchecked_with_fact(unrelated_control)
            )
        )
        .is_err()
    );
    let mut retired_control = folded.clone();
    Arc::make_mut(&mut retired_control.population_effects).creation = Some(retired.clone());
    assert_eq!(
        evaluate_count(&retired_control).unwrap()[0].value,
        CValue::Int32(Bitvector32Term::Constant(0))
    );
    let mut nested_control = folded.clone();
    Arc::make_mut(&mut nested_control.population_effects).creation = Some(imported.enter_call());
    assert!(evaluate_count(&nested_control).is_err());
    let mut rechecked_control = folded.clone();
    Arc::make_mut(&mut rechecked_control.population_effects).creation =
        Some(imported.enter_proof_entry());
    assert_eq!(
        evaluate_count(&rechecked_control).unwrap()[0].value,
        folded_paths[0].value
    );
    let mut projected =
        state
            .clone()
            .with_resource_context(
                ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::PopulationAuthority(description.clone()),
                )),
            );
    Arc::make_mut(&mut projected.population_effects).creation = Some(imported.clone());
    let paths = evaluate_count(&projected).expect("checked import permits exact count");
    assert_eq!(paths[0].value, folded_paths[0].value);
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].value,
        CValue::Int32(Bitvector32Term::MemoryLoad(_, _))
    ));
    // A population entry in the ledger is insufficient without current
    // ownership. Preserve the same ledger while changing only custody.
    let absent = projected
        .clone()
        .with_resource_context(ResourceContext::new());
    assert!(evaluate_count(&absent).is_err());
    let unrelated =
        projected
            .clone()
            .with_resource_context(
                ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::PopulationAuthority(wrong_population.clone()),
                )),
            );
    assert!(evaluate_count(&unrelated).is_err());
    // Proof-entry rechecking retains the explicit import; an ordinary nested
    // invocation must receive authority through its checked call transfer.
    let mut rechecked = projected.clone();
    Arc::make_mut(&mut rechecked.population_effects).creation = Some(imported.enter_proof_entry());
    assert_eq!(evaluate_count(&rechecked).unwrap()[0].value, paths[0].value);
    let mut nested = projected.clone();
    Arc::make_mut(&mut nested.population_effects).creation = Some(imported.enter_call());
    assert!(evaluate_count(&nested).is_err());
    let mut retired_state = projected.clone();
    Arc::make_mut(&mut retired_state.population_effects).creation = Some(retired);
    assert_eq!(
        evaluate_count(&retired_state).unwrap()[0].value,
        CValue::Int32(Bitvector32Term::Constant(0))
    );
    assert!(
        evaluate_count(&state).is_err(),
        "a folded wrapper alone cannot read count"
    );
    let (with_member, _) = imported
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .unwrap();
    let born_count = with_member.observe_symbolic(&description).unwrap();
    assert_eq!(born_count.delta, 1);
    assert_eq!(born_count.entry_owned_members, 0);
    let (without_member, _) = with_member
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert_eq!(
        without_member.observe_symbolic(&description).unwrap().delta,
        0
    );
    let wrong = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_113)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(imported.observe_symbolic(&wrong).is_none());
    let mut wrong_fact = definition.clone();
    wrong_fact.facts.clear();
    let arbitrary = entry
        .import_checked_control_wrapper(&state, &selected, &wrong_fact, &PureFactContext::new())
        .unwrap();
    let arbitrary_count = arbitrary
        .observe_symbolic(&description)
        .unwrap()
        .entry_count;
    assert!(matches!(arbitrary_count, Bitvector32Term::Variable(_)));
    assert_ne!(arbitrary_count, Bitvector32Term::Constant(0));
    assert_eq!(
        arbitrary_count,
        entry
            .import_checked_control_wrapper(&state, &selected, &wrong_fact, &PureFactContext::new())
            .unwrap()
            .observe_symbolic(&description)
            .unwrap()
            .entry_count
    );
    assert!(!arbitrary.checked_empty_population(&description));
    assert!(
        entry
            .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
            .is_ok()
    );
    let missing = CState::new().with_population_creation_tracking();
    assert!(
        entry
            .import_checked_control_wrapper(
                &missing,
                &selected,
                &definition,
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn helper_call_transfers_authority_and_member_without_changing_total() {
    let block = PointerBlock::Heap(940_106);
    let description = member_description(block.clone());
    let caller = CreationEvents::new().created(block.clone());
    let (caller, _) = caller.checked_establish(&block, &description).unwrap();
    let (caller, _) = caller
        .checked_member_exchange(&block, &description, true)
        .unwrap();
    let callee = caller.enter_call();
    assert!(!callee.owns_population_authority(&description));
    let entry = callee
        .transfer_call_fact(&caller, &callee, &description, true)
        .unwrap()
        .transfer_call_fact(&caller, &callee, &description, false)
        .unwrap();
    assert_eq!(entry.observe(&block, "reference"), Ok(1));
    assert!(entry.owns_population_authority(&description));
    assert!(
        !entry
            .return_to(&caller)
            .owns_population_authority(&description)
    );
    assert_eq!(
        entry.finish_call(&caller),
        Err(CreationRefusal::OutstandingOwnership)
    );
    let returned = entry
        .transfer_call_fact(&callee, &caller, &description, false)
        .unwrap()
        .transfer_call_fact(&callee, &caller, &description, true)
        .unwrap();
    let resumed = returned.finish_call(&caller).unwrap();
    assert!(resumed.owns_population_authority(&description));
    assert!(!returned.owns_population_authority(&description));
    assert_eq!(resumed.observe(&block, "reference"), Ok(1));
    assert_eq!(returned.finish_call(&caller).unwrap(), resumed);
    assert_ne!(resumed.enter_call(), callee);
    assert_eq!(
        resumed.transfer_call_fact(&callee, &caller, &description, false),
        Err(CreationRefusal::MissingMembers)
    );
}

#[test]
fn checked_member_exchange_conserves_exact_authority_total() {
    let block = PointerBlock::Heap(940_105);
    let description = member_description(block.clone());
    let created = CreationEvents::new().created(block.clone());
    assert_eq!(
        created.observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
    assert_eq!(
        created
            .checked_member_exchange(&block, &description, true)
            .err(),
        Some(CreationRefusal::MissingAuthority)
    );
    let established = created.establish(&block, "reference").unwrap();
    assert_eq!(established.observe(&block, "reference"), Ok(0));
    assert_eq!(
        established
            .checked_member_exchange(&block, &description, false)
            .err(),
        Some(CreationRefusal::MissingMembers)
    );
    let (one, birth) = established
        .checked_member_exchange(&block, &description, true)
        .unwrap();
    assert!(birth.matches(&established, &one, &description, true));
    assert!(!birth.matches(&established, &one, &description, false));
    assert!(!birth.matches(&created, &one, &description, true));
    assert_eq!(one.observe(&block, "reference"), Ok(1));
    assert_eq!(
        one.retire_authority(&block, "reference"),
        Err(CreationRefusal::OutstandingMembers)
    );
    let (zero, death) = one
        .checked_member_exchange(&block, &description, false)
        .unwrap();
    assert!(death.matches(&one, &zero, &description, false));
    assert_eq!(zero.observe(&block, "reference"), Ok(0));
    assert_eq!(
        zero.checked_member_exchange(&block, &description, false)
            .err(),
        Some(CreationRefusal::MissingMembers)
    );
    assert_eq!(
        zero.retire_authority(&block, "reference")
            .unwrap()
            .observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
}

#[test]
fn checked_member_exchange_requires_exact_field_free_anchor_and_holder() {
    let block = PointerBlock::Heap(940_106);
    let established = CreationEvents::new()
        .created(block.clone())
        .establish(&block, "reference")
        .unwrap();
    let base = member_description(block.clone());
    let offset = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(4),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let wrong_block = PointerBlock::Heap(940_107);
    let fielded = ResourceDescription::new(
        "reference".into(),
        base.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::Integer)]).unwrap(),
    );
    for invalid in [&offset, &fielded] {
        assert_eq!(
            established
                .checked_member_exchange(&block, invalid, true)
                .err(),
            Some(CreationRefusal::InvalidMember)
        );
    }
    assert_eq!(
        established
            .checked_member_exchange(&wrong_block, &base, true)
            .err(),
        Some(CreationRefusal::InvalidMember)
    );
    let callee = established.enter_call();
    assert_eq!(
        callee.observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
    assert_eq!(
        callee.checked_member_exchange(&block, &base, true).err(),
        Some(CreationRefusal::MissingAuthority)
    );
}

#[test]
fn opaque_nested_numeric_custody_transfer_and_return() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 2)
        .unwrap();
    assert!(entry.tracks_population(&description));
    let child = entry.enter_call();
    assert!(matches!(
        child.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingAuthority)
    ));
    let sent = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    assert_eq!(
        sent,
        child
            .transfer_call_fact(&entry, &child, &description, true)
            .unwrap()
    );
    assert!(sent.owns_population_authority(&description));
    assert!(
        !sent
            .return_to(&entry)
            .owns_population_authority(&description)
    );
    assert!(matches!(
        sent.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let sent = sent
        .transfer_call_fact(&entry, &child, &description, false)
        .unwrap();
    assert_eq!(
        sent.0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        2
    );
    assert_eq!(
        sent.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    );
    let (spent, _) = sent
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert_eq!(
        spent
            .0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        1
    );
    assert!(!spent.owns_population_member(&description));
    let returned = spent
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap();
    let returned = returned.finish_call(&entry).unwrap();
    assert!(returned.owns_population_authority(&description));
    assert!(returned.owns_population_member(&description));
    assert!(returned.spent_imported_member_since(&entry, &description));
    assert_eq!(
        returned
            .0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        1
    );
}

#[test]
fn opaque_returned_authority_cannot_strand_members() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    let child = entry.enter_call();
    let sent = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap()
        .transfer_call_fact(&entry, &child, &description, false)
        .unwrap();
    let authority_returned = sent
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap();
    assert_eq!(
        authority_returned.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    );
    assert!(matches!(
        authority_returned.checked_member_exchange(
            &PointerBlock::ExternalArgument,
            &description,
            false
        ),
        Err(CreationRefusal::MissingAuthority)
    ));
    let all_returned = authority_returned
        .transfer_call_fact(&child, &entry, &description, false)
        .unwrap()
        .finish_call(&entry)
        .unwrap();
    assert!(all_returned.owns_population_member(&description));
    assert_eq!(
        all_returned.imported_member_delta_since_entry(&description),
        None
    );
}

#[test]
fn opaque_symbolic_nested_transfer_is_explicitly_unsupported() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(7)),
            Some(Bitvector32Term::Constant(3)),
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    assert_eq!(
        child.transfer_call_fact(&entry, &child, &description, true),
        Err(CreationRefusal::InvalidQuantity)
    );
    assert_eq!(
        child.transfer_call_fact_quantity(
            &entry,
            &child,
            &description,
            false,
            &Bitvector32Term::Constant(3),
            &PureFactContext::new()
        ),
        Err(CreationRefusal::InvalidQuantity)
    );
}

#[test]
fn proof_entry_keeps_opaque_assumptions_without_creator_privilege() {
    let description = member_description(PointerBlock::ExternalArgument);
    let imported = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    let block = PointerBlock::Heap(777);
    let created = imported.created(block.clone());
    let proof = created.enter_proof_entry();
    assert!(proof.owns_population_authority(&description));
    assert!(!proof.created_here(&block));
    assert_eq!(
        proof.establish(&block, "reference"),
        Err(CreationRefusal::NotCreationEnvironment)
    );
}

#[test]
fn opaque_transfer_and_finish_index_scale_with_selected_population() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(970_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut entry = CreationEvents::new();
        for id in 0..size {
            entry = entry
                .import_opaque_contract_population(&description_at(id), 1)
                .unwrap();
        }
        let selected = description_at(size / 2);
        let child = entry.enter_call();
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            let sent = child
                .transfer_call_fact(&entry, &child, &selected, true)
                .unwrap()
                .transfer_call_fact(&entry, &child, &selected, false)
                .unwrap();
            assert_eq!(
                sent.finish_call(&entry),
                Err(CreationRefusal::OutstandingOwnership)
            );
            let returned = sent
                .transfer_call_fact(&child, &entry, &selected, true)
                .unwrap()
                .transfer_call_fact(&child, &entry, &selected, false)
                .unwrap()
                .finish_call(&entry)
                .unwrap();
            assert!(returned.owns_population_authority(&selected));
            assert!(returned.owns_population_member(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 40, "{work:?}");
}

#[test]
fn checked_empty_retirement_survives_free_but_not_a_new_lifetime() {
    let block = PointerBlock::Heap(980_100);
    let description = member_description(block.clone());
    let created = CreationEvents::new().created(block.clone());
    assert!(!created.checked_empty_population(&description));
    let (established, _) = created.checked_establish(&block, &description).unwrap();
    assert!(!established.checked_empty_population(&description));
    let (retired, _) = established.checked_retire(&block, &description).unwrap();
    assert!(retired.checked_empty_population(&description));
    assert!(!retired.owns_population_authority(&description));
    assert!(
        retired
            .checked_member_exchange(&block, &description, true)
            .is_err()
    );
    let freed = retired.retired(&block).unwrap();
    assert!(freed.checked_empty_population(&description));
    let wrong_family = ResourceDescription::new(
        "other_reference".into(),
        description.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(!freed.checked_empty_population(&wrong_family));
    let wrong_offset = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(4),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(!freed.checked_empty_population(&wrong_offset));
    let recreated = freed.created(block.clone());
    assert!(!recreated.checked_empty_population(&description));
}

#[test]
fn opaque_retirement_requires_global_count_proof_not_local_exhaustion() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry_count = Bitvector32Term::Variable(Variable(980_200));
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            1,
            Some(entry_count.clone()),
            None,
            None,
        )
        .unwrap();
    let (spent, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(!spent.checked_empty_population(&description));
    assert_eq!(
        spent
            .checked_retire_imported(&description, &PureFactContext::new())
            .unwrap_err(),
        CreationRefusal::UnknownTotal
    );
    let wrong_total = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(entry_count.clone()),
            Box::new(Bitvector32Term::Constant(2)),
        ),
        true,
    ));
    assert!(
        spent
            .checked_retire_imported(&description, &wrong_total)
            .is_err()
    );
    let right_total = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(entry_count),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    ));
    let (retired, _) = spent
        .checked_retire_imported(&description, &right_total)
        .unwrap();
    assert!(retired.checked_empty_population(&description));
    assert!(!retired.owns_population_authority(&description));
}

#[test]
fn checked_empty_lookup_scales_over_unrelated_retired_populations() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let mut events = CreationEvents::new();
        for id in 0..size {
            let block = PointerBlock::Heap(990_000 + id);
            let description = member_description(block.clone());
            events = events.created(block.clone());
            events = events.checked_establish(&block, &description).unwrap().0;
            events = events.checked_retire(&block, &description).unwrap().0;
            events = events.retired(&block).unwrap();
        }
        let selected = member_description(PointerBlock::Heap(990_000 + size / 2));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.checked_empty_population(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 10, "{work:?}");
}
