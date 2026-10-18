use super::*;
use crate::kernel::loans::LoanRefusal;

fn pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn caller(pointer: &Pointer) -> CState {
    caller_with_owned_end(pointer, 1, 4)
}

fn caller_with_owned_end(pointer: &Pointer, owned_end: u32, bytes: u32) -> CState {
    let range = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(owned_end),
    );
    CState::new()
        .with_population_creation_tracking()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), bytes)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own(CResource::Memory(range))),
        )
}

fn reader_with_output(name: &str, output_start: u32, output_end: u32) -> CFunction {
    let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let output = CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(output_start),
        c_int32_literal(output_end),
    );
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(input)],
        vec![CResourceSpec::viewed_memory(output)],
    )
}

fn reader_for_input(name: &str, input_end: u32) -> CFunction {
    let input = CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(input_end),
    );
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
}

fn reader_with_mutable_range(name: &str, mutable_start: u32, mutable_end: u32) -> CFunction {
    let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(mutable_start),
            c_int32_literal(mutable_end),
        )],
        Vec::new(),
        true,
    )
}

fn reader(name: &str, duplicate_view: bool) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let mut requires = vec![CResourceSpec::viewed_memory(segment.clone())];
    if duplicate_view {
        requires.push(CResourceSpec::viewed_memory(segment));
    }
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(requires, Vec::new())
}

fn composite_reader(name: &str) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let required = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::View,
        "cell".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        Vec::new(),
    );
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
}

fn early_reader(name: &str) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    c_function(
        CType::Void,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::If {
            condition: c_int32_literal(1),
            then_branch: Box::new(c_return(c_void_value())),
            else_branch: Box::new(CStatement::Skip),
        },
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new())
}

/// `resource guarded_item(item) { if item != 0 { owns item[0..1]; } }`
/// consumed by a function whose body reads nothing.
fn conditional_owner(name: &str) -> (CFunction, CExecutionEnvironment) {
    let definition = CCompositeResourceDefinition::new(
        "guarded_item",
        vec![c_parameter("item", CType::Int32Pointer)],
        Some(SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("item")),
            operator: CComparisonOperator::NotEqual,
            right: SpecExpression::Value(CValue::pointer(Pointer::null())),
        }),
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("item"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        Vec::new(),
    );
    let function = c_function(
        CType::Int32,
        name,
        vec![c_parameter("item", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_resource_summary(
        vec![CResourceSpec::composite(
            CResourceAccessMode::Own,
            "guarded_item".to_string(),
            vec![c_variable("item")],
            vec![CType::Int32Pointer],
        )],
        Vec::new(),
    )
    .with_composite_resource_definitions(vec![definition]);
    let environment = environment(&function);
    (function, environment)
}

fn environment(function: &CFunction) -> CExecutionEnvironment {
    CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
        pointer_result: None,
        function: function.clone(),
        loop_semantics: CLoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
    })
}

#[test]
fn independent_verification_uses_the_call_transfer_boundary() {
    let pointer = pointer();
    let function = reader_for_input("candidate_verified_reader", 1);
    let state = caller(&pointer);
    let mut budget = ExecutionBudget::new();
    let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
    let paths = execute_c_function_verification_paths(
        &state,
        &function,
        &[c_pointer_value(pointer)],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut budget,
        &mut variables,
        true,
        false,
    )
    .expect("verification should execute through the transfer boundary");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
}

#[test]
fn candidate_reader_escrows_owner_until_return() {
    let pointer = pointer();
    let function = reader("candidate_reader", false);
    let caller = caller(&pointer);
    let argument_values = vec![CValue::pointer(pointer.clone())];
    let callee = bind_c_function_arguments(&caller, &function, &argument_values)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(
        !transfer.caller_resources_after_requirements.satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new()
        )
    );
    assert!(transfer.callee_resources.satisfies_fact(
        &CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_function_entry_preserves_outer_loan_authority() {
    let pointer = pointer();
    let function = c_function(
        CType::Void,
        "candidate_empty_resource_entry",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_void_value()),
    );
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(participant));
    let callee = bind_c_function_arguments(&caller_state, &function, &[CValue::pointer(pointer)])
        .expect("the function argument should bind");

    assert_eq!(callee.loan_ledger(), Some(&ledger));
    assert_eq!(callee.loan_participant(), Some(participant));
    assert!(callee.loan_bindings_are_consistent());
}

#[test]
fn candidate_composite_call_lends_primitive_body_and_recovers_head() {
    let pointer = pointer();
    let head = CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
    let caller = CState::new()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
    let function = composite_reader("candidate_composite_reader");
    let callee = bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
        .expect("composite reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("composite transfer should run")
    .expect("composite transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("composite transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(plan.ledger.has_active_memory_loans());
    let body_range = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&body_range),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(transfer.callee_resources.satisfies_fact(
        &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())],),
        &PureFactContext::new(),
    ));
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, evidence) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("composite return should recover");
    assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
    assert!(evidence.is_some());
}

/// A composite view lent twice in a row: the first return must leave
/// the caller exactly the recovered head, so the second lend finds one
/// owner and no exposed body piece beside it.
fn composite_reader_with_definition(
    name: &str,
    definition: CCompositeResourceDefinition,
) -> CFunction {
    let required = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::View,
        "cell".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
}

fn fact_bearing_cell_definition() -> CCompositeResourceDefinition {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
    )
}

fn plan_composite_lend(function: &CFunction) -> Result<(), CRuntimeError> {
    let pointer = pointer();
    let head = CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
    let caller = CState::new()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
    let callee = bind_c_function_arguments(&caller, function, &[CValue::pointer(pointer)])
        .expect("composite reader arguments should bind");
    prepare_function_resource_transfer(
        &caller,
        &callee,
        function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("composite transfer should run")
    .map(|_| ())
}

/// Recovery restores the exact escrowed head, so a body fact over the
/// body's own cells is re-asserted as folded: such a composite lends.
#[test]
fn candidate_composite_with_body_facts_is_lendable() {
    let function = composite_reader_with_definition(
        "candidate_fact_bearing_reader",
        fact_bearing_cell_definition(),
    );
    plan_composite_lend(&function).expect("a fact over the body's own cells is loan-stable");
}

/// A fact that claims liveness of storage outside the body, or one that
/// reads a population count, is not stabilized by the loan.
#[test]
fn candidate_composite_with_unstable_facts_is_refused() {
    let liveness = composite_reader_with_definition(
        "candidate_liveness_fact_reader",
        fact_bearing_cell_definition().with_liveness_facts(true),
    );
    let error = plan_composite_lend(&liveness).expect_err("a liveness fact is refused");
    assert!(
        matches!(&error, CRuntimeError::FunctionContract(message) if message.contains("allocation-liveness")),
        "{error}"
    );
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let counted = composite_reader_with_definition(
        "candidate_counted_fact_reader",
        CCompositeResourceDefinition::authority_control(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![CResourceSpec::owned_memory(segment)],
            vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
        ),
    );
    assert!(plan_composite_lend(&counted).is_err());
}

// The owned-interface-to-viewed-implementation adapter (docs/internals/stable-views.md):
// the callee's clause names one composite, the caller owns another whose
// checked frontier covers it.

fn cell_definition(end: u32, facts: Vec<SpecProposition>) -> CCompositeResourceDefinition {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(end));
    CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        facts,
    )
}

fn wide_definition(end: u32) -> CCompositeResourceDefinition {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(end));
    CCompositeResourceDefinition::new(
        "wide",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        Vec::new(),
    )
}

/// A reader that views `cell(p)` and knows both definitions.
fn adapter_reader(
    name: &str,
    cell: CCompositeResourceDefinition,
    wide: CCompositeResourceDefinition,
) -> CFunction {
    let required = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::View,
        "cell".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![cell, wide])
}

/// The caller owns `wide(p)` over an eight-byte block and nothing else.
fn adapter_caller(pointer: &Pointer) -> CState {
    let second = Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(4),
    };
    CState::new()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 8)
                .store(pointer.clone(), int32(7))
                .store(second, int32(9)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_composite("wide".into(), vec![CValue::pointer(pointer.clone())]),
        ))
}

fn plan_adapter_lend(
    function: &CFunction,
) -> (CState, Result<CFunctionResourceTransfer, CRuntimeError>) {
    let pointer = pointer();
    let caller = adapter_caller(&pointer);
    let callee = bind_c_function_arguments(&caller, function, &[CValue::pointer(pointer.clone())])
        .expect("adapter reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("adapter transfer should run");
    (caller, transfer)
}

/// The caller owns `wide(p)` over `p[0..2]`; the callee views `cell(p)`
/// over `p[0..1]`. The lend escrows the owner the caller actually holds,
/// `views cell(p)` joins that loan's permitted descriptions, and recovery
/// restores `wide(p)` exactly.
#[test]
fn candidate_composite_view_is_backed_by_a_covering_owned_composite() {
    let function = adapter_reader(
        "candidate_adapter_reader",
        cell_definition(1, Vec::new()),
        wide_definition(2),
    );
    let pointer = pointer();
    let (caller, transfer) = plan_adapter_lend(&function);
    let transfer = transfer.expect("a covering owner backs the viewed composite");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the adapter lend records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(transfer.callee_resources.satisfies_fact(
        &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())]),
        &PureFactContext::new(),
    ));
    // The whole escrowed frontier is protected, not just the adapted
    // clause's own bytes.
    for end in [1, 2] {
        let range = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(end),
        );
        assert_eq!(
            plan.ledger.permits_memory_access(&range),
            Err(LoanRefusal::ActiveDependency)
        );
    }
    let callee = bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
        .expect("adapter reader arguments should bind");
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("the adapter lend should recover");
    let head = CResourceFact::own_composite("wide".into(), vec![CValue::pointer(pointer)]);
    assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
    assert_eq!(resources.facts(), [head]);
}

/// The owner's body has to cover every piece of the viewed composite's
/// checked frontier. Half of it is not backing.
#[test]
fn candidate_composite_view_over_an_uncovered_owner_is_refused() {
    let function = adapter_reader(
        "candidate_uncovered_adapter_reader",
        cell_definition(2, Vec::new()),
        wide_definition(1),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let error = transfer.expect_err("an owner that covers half the frontier is not backing");
    let CRuntimeError::LoanRefusal(diagnostic) = &error else {
        panic!("{error}");
    };
    assert_eq!(
        diagnostic.category(),
        crate::kernel::loans::LoanRefusalCategory::Missing
    );
    assert_eq!(
        diagnostic.subject().resource_fact(),
        Some(&CResourceFact::view_composite(
            "cell".into(),
            vec![CValue::pointer(pointer())]
        ))
    );
}

/// The viewed composite's facts are what `observe` publishes inside the
/// callee, so the caller has to have established them. A fact the owner's
/// frontier does not give is a refusal, not an assumption.
#[test]
fn candidate_composite_view_with_an_unestablished_fact_is_refused() {
    let unestablished = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_load(c_variable("p"))),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let function = adapter_reader(
        "candidate_unestablished_fact_adapter_reader",
        cell_definition(1, vec![unestablished]),
        wide_definition(2),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let error = transfer.expect_err("an unestablished body fact is refused");
    // Assembling the view is a fold, so the refusal names the instance and
    // the body fact it could not establish rather than a missing loan.
    let CRuntimeError::UnestablishedAssemblyFact { assembled, .. } = &error else {
        panic!("{error}");
    };
    assert_eq!(
        assembled.as_ref(),
        &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer())])
    );
    // The same adapter with a fact the call already establishes is
    // accepted, so the refusal above is the fact check and not the shape.
    let established = adapter_reader(
        "candidate_established_fact_adapter_reader",
        cell_definition(
            1,
            vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
        ),
        wide_definition(2),
    );
    plan_adapter_lend(&established)
        .1
        .expect("an established body fact backs the adapter");
}

/// With no owned composite to escrow, the planner materializes the viewed
/// composite out of exactly the owned frontier the caller holds, and
/// recovery hands those facts back: the caller's packaging is the same
/// after the call as before it, and the unlent remainder stays writable.
#[test]
fn candidate_composite_view_is_materialized_from_the_caller_frontier() {
    let pointer = pointer();
    let function = composite_reader("candidate_materialized_adapter_reader");
    let caller = caller_with_owned_end(&pointer, 2, 8);
    let callee = bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
        .expect("composite reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("materialized transfer should run")
    .expect("the caller's own frontier backs the viewed composite");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the materialized lend records a loan plan");
    let lent = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let kept = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&lent),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(plan.ledger.permits_memory_access(&kept), Ok(()));
    assert!(transfer.callee_resources.satisfies_fact(
        &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())]),
        &PureFactContext::new(),
    ));
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("the materialized lend should recover");
    // Recovery hands back the frontier the head was materialized from,
    // never a `cell(p)` head the caller never held. (`return_resources`
    // is empty here, so what is left is exactly the recovered escrow.)
    assert_eq!(
        resources.facts(),
        [CResourceFact::own(CResource::Memory(lent))]
    );
}

/// A callee that views `p[0..1]` and, in the same contract, produces a
/// composite whose body is that same range. Whatever the caller lent, it
/// gets back: composing the produced head beside it would leave the caller
/// owning `p[0..1]` twice, once directly and once inside `zz_box3(p)`.
fn view_and_produce_reader(name: &str) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let produced = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::Own,
        "zz_box3".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Produce,
        CResourceSnapshot::Post,
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "zz_box3",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment.clone())],
        Vec::new(),
    );
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], vec![produced])
    .with_composite_resource_definitions(vec![definition])
}

#[test]
fn produced_composite_over_a_viewed_owner_is_refused() {
    let pointer = pointer();
    let function = view_and_produce_reader("view_and_produce");
    let environment =
        CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            loop_semantics: CLoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let paths = execute_c_function_call_paths(
        &caller(&pointer),
        &function,
        &[c_pointer_value(pointer)],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("the call should execute");
    assert!(
        paths.iter().all(|path| matches!(
            &path.outcome,
            CFunctionOutcome::RuntimeError(error) if produced_composite_overlap(error)
        )),
        "{:?}",
        paths.iter().map(|path| &path.outcome).collect::<Vec<_>>()
    );
}

fn produced_composite_overlap(error: &CRuntimeError) -> bool {
    matches!(
        error,
        CRuntimeError::ProducedCompositeOverlapsHeldResource { .. }
    )
}

#[test]
fn candidate_composite_reader_can_be_called_twice() {
    let pointer = pointer();
    let head = CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
    let caller = CState::new()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
    let function = composite_reader("candidate_composite_reader_twice");
    let first = execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("first composite call should execute");
    let [
        CFunctionPath {
            outcome: CFunctionOutcome::Return {
                state: after_first, ..
            },
            ..
        },
    ] = first.as_slice()
    else {
        panic!("first composite call should return: {first:?}");
    };
    assert_eq!(after_first.resources().facts(), std::slice::from_ref(&head));
    let second = execute_c_function_call_paths(
        after_first,
        &function,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("second composite call should execute");
    assert!(
        matches!(
            second.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ),
        "{second:?}"
    );
}

#[test]
fn candidate_reader_recovers_owner_for_following_write() {
    let pointer = pointer();
    let function = reader("candidate_reader_return", false);
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant));
    let paths = execute_c_function_call_paths(
        &caller_state,
        &function,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate call should execute");
    let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!("candidate reader should return: {:?}", paths[0].outcome);
    };
    assert_eq!(paths[0].loan_evidence.len(), 1);
    let evidence_items = paths[0].loan_evidence.to_vec();
    let evidence = &evidence_items[0];
    let caller_ledger = caller_state
        .loan_ledger()
        .cloned()
        .expect("candidate execution publishes its caller ledger");
    evidence
        .recheck(
            &caller_ledger,
            caller_state.loan_participant(),
            &evidence.entry.ledger,
            Some(evidence.entry.callee_participant()),
        )
        .expect("retained candidate evidence rechecks");
    assert_eq!(state.loan_ledger(), Some(&evidence.recovered_ledger));
    assert!(state.resources().satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_direct_reader_recovers_owner_for_following_write() {
    let pointer = pointer();
    let function = reader("candidate_direct_reader", false);
    let paths = execute_c_function_paths(
        &caller(&pointer),
        &function,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate direct call should execute");
    let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!(
            "candidate direct reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert!(state.resources().satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_evidence_rejects_definitionally_equal_resources_with_new_identity() {
    let pointer = pointer();
    let function = reader("candidate_identity_guard", false);
    let caller_ledger = LoanLedger::new();
    let caller_participant = caller_ledger
        .fresh_participant()
        .expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(caller_ledger.clone()))
        .with_loan_participant(Some(caller_participant));
    let paths = execute_c_function_call_paths(
        &caller_state,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate call should execute");
    let evidence_items = paths[0].loan_evidence.to_vec();
    let evidence = &evidence_items[0];
    let different_participant = caller_ledger
        .fresh_participant()
        .expect("fresh participant identity");
    assert_eq!(
        evidence
            .recheck(
                &caller_ledger,
                Some(different_participant),
                &evidence.entry.ledger,
                Some(evidence.entry.callee_participant()),
            )
            .expect_err("a different caller participant must be refused"),
        LoanRefusal::WrongHolder
    );
    assert_eq!(
        evidence
            .recheck(
                &LoanLedger::new(),
                Some(caller_participant),
                &evidence.entry.ledger,
                Some(evidence.entry.callee_participant()),
            )
            .expect_err("an unrelated predecessor ledger must be refused"),
        LoanRefusal::StalePredecessor
    );
}

#[test]
fn candidate_nested_body_call_retains_inner_and_outer_evidence() {
    let pointer = pointer();
    let inner = reader("candidate_nested_inner", false);
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let outer = c_function(
        CType::Int32,
        "candidate_nested_outer",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::seq(
            Arc::new(c_declare("result", CType::Int32)),
            Arc::new(CStatement::seq(
                Arc::new(c_call_assign("result", inner.name(), vec![c_variable("p")])),
                Arc::new(c_return(c_variable("result"))),
            )),
        ),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new());
    let environment = environment(&outer).with_function(inner);
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant));
    let paths = execute_c_function_call_paths(
        &caller_state,
        &outer,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("nested candidate call should execute");
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].loan_evidence.len(), 2);
    let evidence = paths[0].loan_evidence.to_vec();
    assert_eq!(
        evidence[0].entry.caller_ledger(),
        &evidence[1].entry.ledger,
        "inner evidence starts at the outer callee ledger"
    );
}

/// Implicit local authority backs a checked loan without an owned escrow.
/// A synchronous call closes it before returning to its caller.
#[test]
fn candidate_local_array_view_uses_a_checked_loan_and_recovers() {
    let pointer = pointer();
    let function = reader("candidate_local_reader", false);
    let caller = CState::new().with_memory(
        CMemory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate local view call should execute");
    assert_eq!(
        paths[0].loan_evidence.len(),
        1,
        "the local view must have a checked entry and discharge"
    );
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { state, .. },
            ..
        }] if state.loan_ledger().is_none_or(|ledger| !ledger.has_active_memory_loans())
    ));
}

/// The activation-local bounds rule still applies, and it decides the
/// call before the callee reads anything: a local view past the end of
/// its block names storage the block does not have, so the call is
/// refused for the missing resource rather than for a read of whatever
/// lies beyond the block.
#[test]
fn candidate_local_array_view_out_of_bounds_is_refused() {
    let pointer = pointer();
    let function = reader_for_input("candidate_local_wide_reader", 4);
    let caller = CState::new().with_memory(
        CMemory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate out-of-bounds local view should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if resource.is_view()
        ),
        "the bounds rule names the unbacked view, not a later read: {paths:?}"
    );
}

/// A conditional composite whose guard the assumptions decide false has
/// an empty body, so the empty context satisfies it: the planner must
/// discharge `owns guarded_item(null)` definitionally instead of
/// demanding an owned entry the caller was never meant to hold.
#[test]
fn candidate_conditional_composite_with_a_false_guard_needs_no_owned_entry() {
    let (function, environment) = conditional_owner("candidate_guarded_free");
    let paths = execute_c_function_call_paths(
        &CState::new(),
        &function,
        &[c_pointer_value(Pointer::null())],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("a false composite guard should execute");
    assert!(
        matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ),
        "an empty body is satisfied by the empty context: {paths:?}"
    );
}

/// The same requirement with an undecided guard keeps its entry: only a
/// guard the assumptions decide collapses the body, so a symbolic
/// argument still needs the caller to supply the composite.
#[test]
fn candidate_conditional_composite_with_an_undecided_guard_still_needs_its_entry() {
    let (function, environment) = conditional_owner("candidate_guarded_symbolic_free");
    let symbolic = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(910_101)), 4),
    };
    let paths = execute_c_function_call_paths(
        &CState::new(),
        &function,
        &[c_pointer_value(symbolic)],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("an undecided composite guard should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if matches!(
                resource.resource(),
                CResource::Composite { name, .. } if name == "guarded_item"
            )
        ),
        "an undecided guard is not an empty body: {paths:?}"
    );
}

/// Two clauses naming one token are a single demand for their combined
/// count. The caller holds one unit, so the refusal has to name quantity
/// two: naming one unit would name a fact the caller does hold.
#[test]
fn candidate_repeated_token_requirement_reports_the_demanded_quantity() {
    let requirement = |parameter| {
        CResourceSpec::token(
            CResourceAccessMode::Own,
            "can_complete".to_string(),
            vec![c_variable(parameter)],
            vec![CType::Int32],
        )
    };
    let function = c_function(
        CType::Int32,
        "candidate_consume_two",
        vec![
            c_parameter("first", CType::Int32),
            c_parameter("second", CType::Int32),
        ],
        c_return(c_int32_literal(0)),
    )
    .with_resource_summary(
        vec![requirement("first"), requirement("second")],
        Vec::new(),
    );
    let token = CValue::Int32(Bitvector32Term::Constant(5));
    let caller = CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own_token("can_complete".to_string(), vec![token.clone()]),
    ));
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(token.clone()), CExpression::Value(token)],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("a doubled token requirement should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if resource.owned_quantity_term() == Some(&Bitvector32Term::Constant(2))
        ),
        "the refusal names the whole demand: {paths:?}"
    );
}

#[test]
fn candidate_inline_reader_uses_the_callers_checked_resources() {
    let pointer = pointer();
    let function = reader("candidate_inline_reader", false).with_inline_body();
    let paths = execute_c_function_call_paths(
        &caller(&pointer),
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate inline call should execute");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
}

#[test]
fn candidate_unresolved_return_obligation_refuses_recovery() {
    let pointer = pointer();
    let function = reader("candidate_unresolved_return", false);
    let caller = caller(&pointer);
    let arguments = vec![CValue::pointer(pointer.clone())];
    let callee = bind_c_function_arguments(&caller, &function, &arguments)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let callee = callee_state_with_resource_transfer(callee, &transfer);
    let unresolved = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ))
    .with_context("callee postcondition");
    let (outcome, _, _) = function_outcome_from_body_with_resource_transfer(
        &caller,
        &function,
        CStatementOutcome::Return {
            value: int32(7),
            state: Box::new(callee),
        },
        vec![unresolved.clone()],
        &PureFactContext::new(),
        &transfer,
        &arguments,
        true,
        &mut ExecutionBudget::new(),
    )
    .expect("candidate return transition should complete");
    assert!(matches!(
        outcome,
        CFunctionOutcome::RuntimeError(CRuntimeError::PendingCallObligations(pending))
            if pending.as_ref() == [unresolved]
    ));
}

#[test]
fn candidate_rejects_malformed_ledger_participant_pairs() {
    let pointer = pointer();
    let function = reader("candidate_pair_mismatch", false);
    let assumptions = PureFactContext::new();
    let mut budget = ExecutionBudget::new();
    let caller_with_ledger = caller(&pointer).with_loan_ledger(Some(LoanLedger::new()));
    let callee = bind_c_function_arguments(
        &caller_with_ledger,
        &function,
        &[CValue::pointer(pointer.clone())],
    )
    .expect("reader argument should bind");
    let error = prepare_function_resource_transfer(
        &caller_with_ledger,
        &callee,
        &function,
        &assumptions,
        &mut budget,
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("pair validation should not hit the execution budget")
    .expect_err("ledger-only caller must be refused");
    assert!(matches!(
        error,
        CRuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));

    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("participant");
    let caller_with_participant = caller(&pointer).with_loan_participant(Some(participant));
    let callee = bind_c_function_arguments(
        &caller_with_participant,
        &function,
        &[CValue::pointer(pointer)],
    )
    .expect("reader argument should bind");
    let error = prepare_function_resource_transfer(
        &caller_with_participant,
        &callee,
        &function,
        &assumptions,
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("pair validation should not hit the execution budget")
    .expect_err("participant-only caller must be refused");
    assert!(matches!(
        error,
        CRuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));
}

#[test]
fn candidate_rejects_wrong_callee_participant_on_recovery() {
    let pointer = pointer();
    let function = reader("candidate_wrong_participant", false);
    let caller = caller(&pointer);
    let arguments = vec![CValue::pointer(pointer.clone())];
    let callee = bind_c_function_arguments(&caller, &function, &arguments)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    let wrong_participant = plan.caller_participant();
    let callee = callee_state_with_resource_transfer(callee, &transfer)
        .with_loan_participant(Some(wrong_participant));
    let missing_ledger = callee.clone().with_loan_ledger(None);
    let error = recover_candidate_stable_view_resources(
        &caller,
        &missing_ledger,
        &transfer,
        transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect_err("recovery without a ledger must be refused");
    assert!(matches!(
        error,
        CRuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
    ));
    let error = recover_candidate_stable_view_resources(
        &caller,
        &callee,
        &transfer,
        transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect_err("recovery must refuse the wrong callee participant");
    assert!(matches!(
        error,
        CRuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::WrongHolder
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
    ));
}

#[test]
fn candidate_joint_planner_reuses_one_escrow_for_two_aliases() {
    let pointer = pointer();
    let function = reader("candidate_aliases", true);
    let caller = caller(&pointer);
    let callee = bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 2);
    assert_eq!(
        plan.stable_views()[0].loan,
        plan.stable_views()[1].loan,
        "aliases share one escrow"
    );
}

#[test]
fn candidate_nested_reader_reborrows_and_restores_outer_view_binding() {
    let pointer = pointer();
    let function = reader("candidate_nested_reader", false);
    let caller = caller(&pointer);
    let outer_template =
        bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
            .expect("outer reader arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);
    let inner_template = bind_c_function_arguments(
        &outer_callee,
        &function,
        &[CValue::pointer(pointer.clone())],
    )
    .expect("inner reader arguments should bind");
    let inner_transfer = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("inner transfer should run")
    .expect("inner transfer should be accepted");
    let inner_plan = inner_transfer
        .stable_view_plan
        .as_ref()
        .expect("nested transfer should use the loan plan");
    let outer_plan = outer_transfer
        .stable_view_plan
        .as_ref()
        .expect("outer transfer should use the loan plan");
    assert_ne!(
        inner_plan.stable_views()[0].loan,
        outer_plan.stable_views()[0].loan,
        "nested reader gets a child loan"
    );
    let inner_callee = callee_state_with_resource_transfer(inner_template, &inner_transfer);
    let (resources, ledger, participant, bindings, _) = recover_candidate_stable_view_resources(
        &outer_callee,
        &inner_callee,
        &inner_transfer,
        inner_transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("nested reader recovery should run");
    assert_eq!(ledger, outer_callee.loan_ledger().cloned());
    assert_eq!(participant, outer_callee.loan_participant());
    assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
    assert!(resources.satisfies_fact(
        &CResourceFact::view_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_nested_reader_body_call_reborrows_and_recovers_owner() {
    let pointer = pointer();
    let inner = reader("candidate_nested_body_inner", false);
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let outer = c_function(
        CType::Int32,
        "candidate_nested_body_outer",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_call_assign("result", inner.name(), vec![c_variable("p")]),
            c_return(c_variable("result")),
        ),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new());
    let environment = CExecutionEnvironment::new()
        .with_function(inner.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            pointer_result: None,
            function: inner,
            loop_semantics: CLoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });

    let paths = execute_c_function_paths(
        &caller(&pointer),
        &outer,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("nested candidate reader should execute through the real body call");
    let CFunctionOutcome::Return { value, state } = &paths[0].outcome else {
        panic!(
            "nested candidate reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert_eq!(value, &int32(7));
    assert!(state.resources().satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_nested_call_preserves_outer_view_for_wider_output() {
    let pointer = pointer();
    let outer_function = reader_for_input("candidate_outer_view", 2);
    let caller = caller_with_owned_end(&pointer, 2, 8);
    let outer_template = bind_c_function_arguments(
        &caller,
        &outer_function,
        &[CValue::pointer(pointer.clone())],
    )
    .expect("outer arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &outer_function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);

    let inner_function = reader_with_output("candidate_outer_output", 0, 2);
    let inner_template = bind_c_function_arguments(
        &outer_callee,
        &inner_function,
        &[CValue::pointer(pointer.clone())],
    )
    .expect("inner arguments should bind");
    let inner_transfer = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &inner_function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("inner transfer should run")
    .expect("inner transfer should be accepted");
    let output = CResourceFact::view_memory(CMemoryRange::new(
        pointer,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    let (resources, ledger, participant, bindings, _loan_evidence) =
        recover_candidate_stable_view_resources(
            &outer_callee,
            &callee_state_with_resource_transfer(inner_template, &inner_transfer),
            &inner_transfer,
            ResourceContext::new().unchecked_with_fact(output.clone()),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect("outer view should authorize the wider returned view");
    assert!(resources.satisfies_fact(&output, &PureFactContext::new()));
    assert_eq!(ledger, outer_callee.loan_ledger().cloned());
    assert_eq!(participant, outer_callee.loan_participant());
    assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
}

fn assert_unbacked_output_rejected(output_start: u32, output_end: u32, name: &str) {
    let pointer = pointer();
    let function = reader_with_output(name, output_start, output_end);
    let paths = execute_c_function_call_paths(
        &caller_with_owned_end(&pointer, 3, 12),
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate output call should execute to a diagnostic path");
    assert!(
        matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::UnbackedReturnedView { .. }),
                ..
            }]
        ),
        "unexpected output result: {paths:?}"
    );
}

#[test]
fn candidate_rejects_new_output_view() {
    assert_unbacked_output_rejected(2, 3, "candidate_new_output");
}

#[test]
fn candidate_rejects_wider_output_without_outer_binding() {
    assert_unbacked_output_rejected(0, 2, "candidate_wider_output");
}

/// Build a call whose return context carries `returned` as an extra view
/// beside the caller's retained owner, either as a checked projection of
/// that exact owned occurrence or as a bare equal fact.
fn recover_with_extra_returned_view(
    projected_from_owner: bool,
) -> Result<ResourceContext, CRuntimeError> {
    let pointer = pointer();
    let function = reader("candidate_returned_projection", false);
    let caller = caller_with_owned_end(&pointer, 3, 12);
    let callee_template =
        bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
            .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let owner = CResourceFact::own_memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
    ));
    let returned = CResourceFact::view_memory(CMemoryRange::new(
        pointer,
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
    ));
    let base = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (support_occurrence, _) = base
        .unique_owned_occurrence_for_fact(&owner)
        .expect("the retained owner has one occurrence");
    let return_resources = if projected_from_owner {
        base.unchecked_with_supported_facts_from_occurrence_with_memory(
            support_occurrence,
            &owner,
            vec![returned],
            caller.memory(),
        )
    } else {
        base.unchecked_with_fact(returned)
    };
    recover_candidate_stable_view_resources(
        &caller,
        &callee_state_with_resource_transfer(callee_template, &transfer),
        &transfer,
        return_resources,
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .map(|(resources, ..)| resources)
}

#[test]
fn candidate_accepts_a_returned_view_projected_from_a_returned_owner() {
    let resources = recover_with_extra_returned_view(true)
        .expect("a checked projection of the returned owner has provenance");
    let projected = CResourceFact::view_memory(CMemoryRange::new(
        pointer(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
    ));
    assert!(resources.satisfies_fact(&projected, &PureFactContext::new()));
}

#[test]
fn candidate_rejects_a_returned_view_that_only_an_equal_owner_satisfies() {
    let error = recover_with_extra_returned_view(false)
        .expect_err("fact equality against an owner is not provenance");
    assert!(
        matches!(&error, CRuntimeError::UnbackedReturnedView { .. }),
        "unexpected refusal: {error}"
    );
}

/// A view of read-only storage is intrinsic read authority rather than a
/// lent capability: `install_borrowed_contract_inputs` gives such a
/// contract input view no borrowed root and `intrinsic_read_views`
/// supplies such a requirement with no ledger transition, both by this
/// block test, so a call that merely carries one across its boundary has
/// provenance for it. Everything else about the two calls below is the
/// same; only the carried block's mutability differs.
fn recover_with_a_carried_view_of_another_block(
    read_only: bool,
) -> Result<ResourceContext, CRuntimeError> {
    let pointer = pointer();
    let other = Pointer {
        block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = reader("candidate_carried_view", false);
    let owned_caller = caller_with_owned_end(&pointer, 3, 12);
    let caller =
        owned_caller
            .clone()
            .with_memory(owned_caller.memory().clone().with_block_or_read_only(
                other.block.clone(),
                8,
                read_only,
            ));
    let callee_template =
        bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer)])
            .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let carried = CResourceFact::view_memory(CMemoryRange::new(
        other,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    let return_resources = transfer
        .caller_resources_after_requirements
        .clone()
        .unchecked_with_fact(carried);
    recover_candidate_stable_view_resources(
        &caller,
        &callee_state_with_resource_transfer(callee_template, &transfer),
        &transfer,
        return_resources,
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .map(|(resources, ..)| resources)
}

#[test]
fn candidate_accepts_a_carried_view_of_read_only_storage() {
    let resources = recover_with_a_carried_view_of_another_block(true)
        .expect("a view of read-only storage is intrinsic read authority");
    let carried = CResourceFact::view_memory(CMemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    assert!(resources.satisfies_fact(&carried, &PureFactContext::new()));
}

#[test]
fn candidate_rejects_a_carried_view_of_mutable_storage() {
    let error = recover_with_a_carried_view_of_another_block(false)
        .expect_err("a view of mutable storage the caller never lent has no provenance");
    // The refusal carries the carried view itself, so the surface can
    // name it rather than print a kernel dump of it.
    let carried = CResourceFact::view_memory(CMemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    assert!(
        matches!(&error, CRuntimeError::UnbackedReturnedView { view } if **view == carried),
        "unexpected refusal: {error}"
    );
}

fn symbolic_bounded_range(
    start: Bitvector32Term,
    end: Bitvector32Term,
    element_width: u32,
) -> CMemoryRange {
    CMemoryRange::new_with_element_width(
        Pointer {
            block: PointerBlock::Concrete("candidate:separation".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        start,
        end,
        element_width,
    )
}

fn constant_bounded_range(start: i32, end: i32, element_width: u32) -> CMemoryRange {
    symbolic_bounded_range(
        Bitvector32Term::Constant(start as u32),
        Bitvector32Term::Constant(end as u32),
        element_width,
    )
}

/// A range that starts below its base meets the ranges it really meets.
/// Zero-extended, `a[-1..2]`'s start scaled to `17179869180`, so every
/// nonnegative range ended at or before it and was called `Disjoint` —
/// which is final, because only a pair this leaves undecided reaches the
/// arithmetic oracle, so it suppressed the refusal an overlapping effect
/// and view owe each other.
#[test]
fn candidate_sees_a_range_that_starts_below_its_base() {
    let assumptions = PureFactContext::new();
    let below = constant_bounded_range(-1, 2, 4);
    for other in [
        constant_bounded_range(0, 1, 4),
        constant_bounded_range(-1, 0, 4),
        constant_bounded_range(1, 2, 4),
        // Differing element widths meet in bytes: `a[-1..2]` covers
        // bytes -4..8 and this covers bytes 0..4.
        constant_bounded_range(0, 4, 1),
    ] {
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&below, &other, &assumptions),
            CandidateMemoryRangeRelation::Overlap
        );
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&other, &below, &assumptions),
            CandidateMemoryRangeRelation::Overlap
        );
    }
}

/// The other polarity: ranges that really do miss each other, on both
/// sides of the base and both wholly below it, stay `Disjoint`.
#[test]
fn candidate_keeps_separate_ranges_below_a_base_separate() {
    let assumptions = PureFactContext::new();
    let below = constant_bounded_range(-4, -1, 4);
    for other in [
        constant_bounded_range(0, 2, 4),
        constant_bounded_range(-1, 0, 4),
        constant_bounded_range(-8, -4, 4),
    ] {
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&below, &other, &assumptions),
            CandidateMemoryRangeRelation::Disjoint
        );
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&other, &below, &assumptions),
            CandidateMemoryRangeRelation::Disjoint
        );
    }
    assert_eq!(
        candidate_memory_ranges_relation_by_bounds(
            &below,
            &constant_bounded_range(-2, 1, 4),
            &assumptions
        ),
        CandidateMemoryRangeRelation::Overlap
    );
}

/// `p[0..n - 1]` and `p[n - 1..n]` are separate for every `n`, and the
/// kernel's own arithmetic decides it. Nothing about the endpoints is
/// concrete, so the bounds comparison alone reports unproved separation.
#[test]
fn candidate_proves_adjacent_symbolic_ranges_separate() {
    let count = Bitvector32Term::Variable(Variable(910));
    let boundary = Bitvector32Term::add(count.clone(), Bitvector32Term::Constant(u32::MAX));
    let viewed = symbolic_bounded_range(Bitvector32Term::Constant(0), boundary.clone(), 4);
    let mutable = symbolic_bounded_range(boundary, count, 4);
    assert_eq!(
        candidate_memory_ranges_relation_by_bounds(&mutable, &viewed, &PureFactContext::new()),
        CandidateMemoryRangeRelation::SeparationUnproved
    );
    assert_eq!(
        candidate_memory_ranges_relation(&mutable, &viewed, &PureFactContext::new()),
        CandidateMemoryRangeRelation::Disjoint
    );
}

/// The arithmetic oracle decides separation, it does not assume it: two
/// unrelated symbolic ranges in one block stay unproved, and a proven
/// overlap is never reinterpreted.
#[test]
fn candidate_leaves_unrelated_symbolic_ranges_unproved() {
    let left = symbolic_bounded_range(
        Bitvector32Term::Variable(Variable(911)),
        Bitvector32Term::Variable(Variable(912)),
        4,
    );
    let right = symbolic_bounded_range(
        Bitvector32Term::Variable(Variable(913)),
        Bitvector32Term::Variable(Variable(914)),
        4,
    );
    assert_eq!(
        candidate_memory_ranges_relation(&left, &right, &PureFactContext::new()),
        CandidateMemoryRangeRelation::SeparationUnproved
    );
    let overlapping = symbolic_bounded_range(
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
        4,
    );
    let inner = symbolic_bounded_range(
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
        4,
    );
    assert_eq!(
        candidate_memory_ranges_relation(&overlapping, &inner, &PureFactContext::new()),
        CandidateMemoryRangeRelation::Overlap
    );
}

fn assert_mutable_view_effect_result(
    mutable_start: u32,
    mutable_end: u32,
    name: &str,
) -> Vec<CFunctionPath> {
    let pointer = pointer();
    let function = reader_with_mutable_range(name, mutable_start, mutable_end);
    execute_c_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate mutable call should execute")
}

#[test]
fn candidate_rejects_mutable_effect_overlapping_view() {
    let paths = assert_mutable_view_effect_result(0, 1, "candidate_overlap_effect");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
            && diagnostic.subject().memory_range().is_some()
    ));
}

/// A mutable effect on the same symbolic base as the lent view, at the
/// same constant offsets, is a proven overlap even though the base
/// offset is unknown: the symbolic view is retained outside the
/// concrete index and compared by offset arithmetic.
#[test]
fn candidate_rejects_symbolic_same_base_overlapping_effect() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let function = reader_with_mutable_range("candidate_symbolic_overlap_effect", 0, 1);
    let paths = execute_c_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate symbolic overlap should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

/// A mutable effect through a second pointer whose relation to the lent
/// view is unknown is neither a proven overlap nor a proven separation;
/// the call is refused as unproved rather than assumed disjoint.
#[test]
fn candidate_rejects_unproved_mutable_effect_separation() {
    let viewed = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let mutated = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(701)),
    };
    let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let function = c_function(
        CType::Int32,
        "candidate_unknown_effect",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
            c_variable("q"),
            c_int32_literal(0),
            c_int32_literal(1),
        )],
        Vec::new(),
        true,
    );
    let paths = execute_c_function_call_paths(
        &caller_with_owned_end(&viewed, 2, 8),
        &function,
        &[
            CExpression::Value(CValue::pointer(viewed)),
            CExpression::Value(CValue::pointer(mutated)),
        ],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate unknown separation should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::SeparationUnproved
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::SeparationUnproved
    ));
}

/// A contract that views one parameter and owns another, with the whole
/// write footprint derived from that ownership. Each requirement is
/// served by a different owned occurrence of the caller's partition.
fn viewer_and_writer(name: &str) -> CFunction {
    let viewed = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let owned = CMemorySegment::new(c_variable("q"), c_int32_literal(0), c_int32_literal(1));
    c_function(
        CType::Int32,
        name,
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![
            CResourceSpec::viewed_memory(viewed),
            CResourceSpec::owned_memory(owned),
        ],
        Vec::new(),
    )
    .with_resource_derived_mutable_frame()
}

/// The partition read at a call. The effect is reserved out of one owned
/// occurrence and the view is lent from another, and the two symbolic
/// ranges share a block with an unknown offset relation, so the
/// arithmetic oracle can order neither. A valid resource context is a
/// partition, so distinct owned occurrences are bytewise disjoint by
/// construction and the call is accepted on that provenance alone. This
/// is, in miniature, the shape of a rotation callback that reads its
/// argument's child augmentation.
#[test]
fn candidate_allows_a_mutable_effect_reserved_from_another_owned_occurrence() {
    let viewed = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let mutated = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(701)),
    };
    let owned_range = |pointer: &Pointer| {
        CResourceFact::own(CResource::Memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )))
    };
    let caller = CState::new()
        .with_population_creation_tracking()
        .with_memory(
            CMemory::new()
                .with_block(viewed.block.clone(), 8)
                .store(viewed.clone(), int32(7)),
        )
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(owned_range(&viewed))
                .unchecked_with_fact(owned_range(&mutated)),
        );
    let function = viewer_and_writer("candidate_separate_occurrence_effect");
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[
            CExpression::Value(CValue::pointer(viewed.clone())),
            CExpression::Value(CValue::pointer(mutated.clone())),
        ],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate separate-occurrence effect call should execute");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
    let [
        CFunctionPath {
            outcome: CFunctionOutcome::Return { state: after, .. },
            ..
        },
    ] = paths.as_slice()
    else {
        unreachable!("the return path was checked above")
    };
    let kept = CallKeptRanges::recorded_on(after.memory())
        .expect("the call records its protected caller frame");
    assert!(
        kept.holds_access(&viewed, 4, &PureFactContext::new()),
        "the owner escrowed for the stable view preserves the read cell"
    );
    assert!(
        !kept.holds_access(&mutated, 4, &PureFactContext::new()),
        "ownership lent for mutation does not preserve its previous value"
    );
}

/// The same-occurrence case is not weakened. Here one caller occurrence
/// has to serve both requirements: the exclusive reservation takes the
/// owned bytes out of it first, and the overlapping view it would also
/// have to back is no longer there. Provenance settles nothing, because
/// the effect and the view would be the same partition element, and the
/// call is refused rather than accepted on a support comparison.
#[test]
fn candidate_rejects_a_mutable_effect_overlapping_a_view_from_its_own_occurrence() {
    let pointer = pointer();
    let viewed = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(2));
    let owned = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let function = c_function(
        CType::Int32,
        "candidate_same_occurrence_overlap_effect",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![
            CResourceSpec::viewed_memory(viewed),
            CResourceSpec::owned_memory(owned),
        ],
        Vec::new(),
    )
    .with_resource_derived_mutable_frame();
    let paths = execute_c_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate same-occurrence overlap should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

#[test]
fn candidate_allows_provably_disjoint_mutable_effect() {
    let paths = assert_mutable_view_effect_result(1, 2, "candidate_disjoint_effect");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
}

/// A composite reader whose contract also declares a mutable footprint.
/// The requirement is `views cell(p)`, which carries no memory range of
/// its own; the bytes it protects are the definition's checked frontier.
fn composite_reader_with_mutable_range(
    name: &str,
    mutable_start: u32,
    mutable_end: u32,
) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let required = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::View,
        "cell".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        Vec::new(),
    );
    c_function(
        CType::Int32,
        name,
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(mutable_start),
            c_int32_literal(mutable_end),
        )],
        Vec::new(),
        true,
    )
}

fn composite_mutable_effect_paths(
    mutable_start: u32,
    mutable_end: u32,
    name: &str,
) -> Vec<CFunctionPath> {
    let pointer = pointer();
    let head = CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
    let caller = CState::new()
        .with_population_creation_tracking()
        .with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 8)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
    let function = composite_reader_with_mutable_range(name, mutable_start, mutable_end);
    execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate composite mutable call should execute")
}

/// F6. The head of a composite view has no memory range, so comparing the
/// declared effects against requirement ranges alone saw nothing here.
/// The checked one-level frontier is what the loan protects, and an
/// effect over one of its pieces is a proven overlap.
#[test]
fn candidate_rejects_mutable_effect_overlapping_a_composite_view_piece() {
    let paths = composite_mutable_effect_paths(0, 1, "candidate_composite_overlap_effect");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
            && diagnostic.subject().memory_range().is_some()
    ));
}

/// The same frontier keeps the supported partition usable: a composite
/// body of `p[0..1]` beside an effect on `p[1..2]` is provably disjoint.
#[test]
fn candidate_allows_a_mutable_effect_disjoint_from_a_composite_view_piece() {
    let paths = composite_mutable_effect_paths(1, 2, "candidate_composite_disjoint_effect");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }]
    ));
}

/// F6. A local view has no caller-owned occurrence, so effect separation
/// must check its actual bytes rather than treating it as a distinct owner.
#[test]
fn candidate_rejects_mutable_effect_overlapping_a_local_view() {
    let pointer = pointer();
    let function = reader_with_mutable_range("candidate_intrinsic_overlap_effect", 0, 1);
    let caller = CState::new().with_memory(
        CMemory::new()
            .with_block(pointer.block.clone(), 8)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate intrinsic view effect call should execute");
    assert!(matches!(
        paths.as_slice(),
        [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

#[test]
fn candidate_nested_reader_rejects_stale_outer_binding() {
    let pointer = pointer();
    let function = reader("candidate_stale_nested_reader", false);
    let caller = caller(&pointer);
    let outer_template =
        bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
            .expect("outer reader arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer)
        .with_loan_view_bindings(LoanViewBindings::default());
    let inner_template =
        bind_c_function_arguments(&outer_callee, &function, &[CValue::pointer(pointer)])
            .expect("inner reader arguments should bind");
    let result = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("stale binding check should run");
    assert!(matches!(
        result,
        Err(CRuntimeError::LoanRefusal(diagnostic))
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));
}

#[test]
fn candidate_early_return_closes_call_scope() {
    let pointer = pointer();
    let function = early_reader("candidate_early_reader");
    let paths = execute_c_function_call_paths(
        &caller(&pointer),
        &function,
        &[CExpression::Value(CValue::pointer(pointer.clone()))],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate early return should execute");
    let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!(
            "candidate early reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert!(state.resources().satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_wrong_scope_close_is_refused() {
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner participant");
    let reader = ledger.fresh_participant().expect("reader participant");
    let escrow = CResourceFact::own(CResource::Token {
        name: "candidate_scope".to_string(),
        arguments: Vec::new().into(),
    });
    let support = ResourceContext::new()
        .unchecked_with_fact(escrow.clone())
        .unique_owned_occurrence_for_fact(&escrow)
        .expect("token backing")
        .0;
    let opening = ledger
        .lend(owner, reader, support, escrow)
        .expect("loan opening");
    let ledger = ledger.apply(&opening.transition).expect("loan apply");
    let refusal = ledger
        .end(opening.scope, reader)
        .expect_err("a non-owner cannot close the scope");
    assert_eq!(
        refusal
            .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
            .category(),
        crate::kernel::LoanRefusalCategory::WrongHolder
    );
    let wrong_scope = super::super::loans::LoanScopeId::for_test(
        opening.scope.arena_for_test(),
        opening.scope.ordinal_for_test().saturating_add(1),
    );
    let refusal = ledger
        .end(wrong_scope, owner)
        .expect_err("an unknown scope cannot be closed");
    assert_eq!(
        refusal
            .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
            .category(),
        crate::kernel::LoanRefusalCategory::WrongScope
    );
}

/// An empty-bodied token population: the caller holds one representative
/// unit and the declared cardinality lives in the tracked population, so
/// `n of slot(p)` is never one owned entry the reservation can select.
fn token_population_reader(name: &str, population: &str) -> CFunction {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
    let unit = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::Own,
        population.into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
        CResourceTransferRole::Consume,
        CResourceSnapshot::Entry,
    )
    .expect("a unit population term");
    let counted = CResourceSpec::quantified(
        c_variable("n"),
        unit,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Entry,
    )
    .expect("a counted population requirement");
    c_function(
        CType::Int32,
        name,
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("n", CType::Int32),
        ],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(segment), counted],
        Vec::new(),
    )
    .with_composite_resource_definitions(vec![
        CCompositeResourceDefinition::new(
            population,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            Vec::new(),
            Vec::new(),
        )
        .with_authorized(true),
    ])
}

/// A declared quantity must be known nonnegative before any resource
/// route looks at it; that check is unrelated to the planner gap.
fn nonnegative_quantity(quantity: Variable) -> PureFactContext {
    PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Variable(quantity)),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    )
}

fn token_population_unit(population: &str, pointer: &Pointer) -> CResourceFact {
    CResourceFact::own_composite(population.into(), vec![CValue::pointer(pointer.clone())])
}

/// The planner's exclusive reservation has no "N units out of a
/// population whose count is at least N" step, and a token population
/// protects no memory, so nothing about the loan ledger could supply one.
/// Such a requirement is planned beside a view the same call lends.
#[test]
fn candidate_symbolic_token_population_consume_plans_beside_a_lent_view() {
    let pointer = pointer();
    let function = token_population_reader("candidate_population_reader", "slot");
    let unit = token_population_unit("slot", &pointer);
    let base = caller(&pointer);
    let caller = base
        .clone()
        .with_resource_context(base.resources().clone().unchecked_with_fact(unit.clone()));
    let arguments = vec![
        CValue::pointer(pointer.clone()),
        CValue::Int32(Bitvector32Term::Variable(Variable(4242))),
    ];
    let assumptions = nonnegative_quantity(Variable(4242));
    let callee = bind_c_function_arguments(&caller, &function, &arguments)
        .expect("population reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &assumptions,
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("population transfer should run")
    .expect("a symbolic population quantity should not refuse the plan");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the view clause still records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    let viewed = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&viewed),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(
        transfer
            .callee_resources
            .satisfies_fact(&CResourceFact::view_memory(viewed), &PureFactContext::new())
    );
}

/// Both execution judgments step a sequence with one driver. A sequence
/// whose first statement leaves abnormally carries that statement's loan
/// evidence out with it under either judgment; the concrete driver once
/// rebuilt the path without it. Here a lending call runs first, so the
/// evidence is what leaves.
#[test]
fn an_abnormal_sequence_exit_keeps_its_loan_evidence_under_both_judgments() {
    let pointer = pointer();
    let function = reader("sequence_exit_reader", false);
    let call = c_call(
        "sequence_exit_reader",
        vec![CExpression::Value(CValue::pointer(pointer.clone()))],
    );
    let exits = [
        ("break", c_break()),
        ("return", c_return(c_int32_literal(0))),
        ("throw", CStatement::Throw(c_int32_literal(1))),
        ("runtime error", c_assign("undeclared", c_int32_literal(1))),
    ];
    for (name, exit) in exits {
        let statement = c_seq(
            c_seq(call.clone(), exit),
            c_assign("unreached", c_int32_literal(2)),
        );
        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("caller participant");
        let state = caller(&pointer)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let environment = environment(&function).with_function(function.clone());
        let executes = crate::kernel::eval::execute_c_statement_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            CExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .expect("the sequence executes");
        let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
        let verifies = crate::kernel::loops::execute_c_statement_verification_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            CExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
            &mut variables,
        )
        .expect("the sequence verifies");
        assert_eq!(executes.len(), 1, "{name}: {executes:?}");
        assert!(
            !matches!(executes[0].outcome, CStatementOutcome::Normal(_)),
            "{name}: the sequence leaves abnormally"
        );
        assert_eq!(
            executes[0].loan_evidence.len(),
            1,
            "{name}: the concrete path keeps the call's evidence"
        );
        assert!(
            verifies
                .iter()
                .any(|path| path.outcome == executes[0].outcome
                    && path.loan_evidence.len() == executes[0].loan_evidence.len()),
            "{name}: the concrete path is a verification path carrying its evidence"
        );
    }
}

#[test]
fn refused_composite_assembly_retains_the_failed_source_clause() {
    let always = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_int32_literal(0)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let missing = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_load(c_variable("p"))),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let definition = cell_definition(1, vec![always.clone(), always, missing])
        .with_fact_source_indices(vec![0, 0, 1])
        .with_fact_source_spellings(vec!["0 == 0".into(), "*p == 0".into()]);
    let function = adapter_reader(
        "source_clause_adapter_reader",
        definition,
        wide_definition(2),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let CRuntimeError::UnestablishedAssemblyFact {
        fact,
        source: Some(source),
        ..
    } = transfer.unwrap_err()
    else {
        panic!("the failed body fact must retain its source");
    };
    assert_eq!(
        *fact,
        Proposition::ConditionIs(ConditionTerm::Constant(false), true)
    );
    assert_eq!(source.spelling, "*p == 0");
    assert_eq!(
        source.bindings,
        vec![("p".into(), CValue::pointer(pointer()))]
    );
}
