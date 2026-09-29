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
    assert!(matches!(
        entry.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::MissingMembers)
    ));
    let empty = CreationEvents::new()
        .import_opaque_contract_population(&description, 0)
        .unwrap();
    let (born, _) = empty
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("an opaque helper can birth its exact member once");
    assert!(born.born_imported_member_since(&empty));
    assert!(born.owns_population_member(&description));
    assert!(matches!(
        born.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::MissingMembers)
    ));
    let (spent, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .expect("an opaque helper can spend its exact imported member once");
    assert!(spent.spent_imported_member_since(&entry));
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
    assert_eq!(
        entry.import_opaque_contract_population(&other, 1),
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
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].value,
        CValue::Int32(Bitvector32Term::MemoryLoad(_, _))
    ));
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
    assert!(
        entry
            .import_checked_control_wrapper(&state, &selected, &wrong_fact, &PureFactContext::new())
            .is_err()
    );
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
    let entry = callee
        .transfer_call_fact(&caller, &callee, &description, true)
        .unwrap()
        .transfer_call_fact(&caller, &callee, &description, false)
        .unwrap();
    assert_eq!(entry.observe(&block, "reference"), Ok(1));
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
