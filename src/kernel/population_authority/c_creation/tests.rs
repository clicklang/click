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
    assert_eq!(
        resumed.population_effects.creation,
        succeeded.population_effects.creation
    );

    let returned_call = execute_c_statement_paths(
        &succeeded,
        &c_call("helper", vec![c_variable("p")]),
        &PureFactContext::new(),
        &CExecutionEnvironment::new().with_function(helper),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("execute real helper call");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after_call),
            ..
        },
    ] = returned_call.as_slice()
    else {
        panic!("helper returns normally: {returned_call:?}");
    };
    assert!(after_call.population_storage_created_here(created));

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
            events = events.pending_creation(PointerBlock::Symbolic(Variable(id)));
        }
        let selected = PointerBlock::Heap(size / 2);
        let pending_block = PointerBlock::Symbolic(Variable(10_000 + size));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.created_here(&selected));
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
