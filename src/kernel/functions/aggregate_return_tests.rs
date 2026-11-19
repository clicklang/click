//! Copy-return compatibility and checked construction-destination oracles.
//! C++ source admission is tested separately from these shared operations.
use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn node_layout() -> AggregateLayout {
    AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("self", 0, ProgramType::Int32Pointer),
            AggregateField::new("value", 8, ProgramType::Int32),
        ],
    )
}

fn copy_function() -> ProgramFunction {
    program_function(
        ProgramType::VoidPointer,
        "copy_result",
        vec![program_parameter("source", ProgramType::VoidPointer)],
        program_return(crate::kernel::program_expression::variable("source")),
    )
    .with_return_aggregate_layout(node_layout())
}

fn pointer(value: &ProgramValue) -> Address {
    let ProgramValue::Pointer(value) = value else {
        panic!("expected an aggregate storage pointer");
    };
    value.address().clone()
}

fn allocate_destination(state: &ExecutionState, name: &str) -> ExecutionState {
    let paths = crate::kernel::eval::execute_execution_statement_paths(
        state,
        &program_allocate_aggregate_destination(name, node_layout()),
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("checked destination allocation");
    let [path] = paths.as_slice() else {
        panic!("one allocation outcome expected");
    };
    assert!(path.obligations.is_empty());
    let StatementOutcome::Normal(state) = &path.outcome else {
        panic!("destination allocation failed: {:?}", path.outcome);
    };
    state.as_ref().clone()
}

// Unlike legacy constructor declarations, allocation grants write authority
// without manufacturing readable placeholders. The second allocation must
// not reuse the first object's identity when the source name is repeated.
#[test]
fn raw_construction_allocation_owns_storage_without_initializing_values() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = allocate_destination(
        &ExecutionState::new().with_population_creation_tracking(),
        "node",
    );
    let destination = state.locals.slot("node").unwrap().clone();
    assert!(state.memory.has_block(&destination.base));
    assert!(!state.memory.has_initialized_bytes_at(&destination, 16));
    assert!(state.memory.known_value(&destination).is_none());
    assert!(
        crate::kernel::eval::memory_write_storage_outcome(
            &state,
            &destination,
            16,
            &PureFactContext::new(),
        )
        .is_none()
    );
    assert!(aggregate_copy_reads_uninitialized(
        &state.memory,
        &destination,
        &node_layout()
    ));
    let again = allocate_destination(&state, "node");
    assert_ne!(again.locals.slot("node").unwrap(), &destination);
    assert!(!again.memory.has_block(&destination.base));
    assert!(again.memory.is_ended_local_block(&destination.base));
}

fn destination_procedure(name: &str, body: ProgramStatement) -> ProgramFunction {
    let storage = ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("destination"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    ));
    program_function(
        ProgramType::Void,
        name,
        vec![
            program_parameter("destination", ProgramType::Int32Pointer),
            program_parameter("input", ProgramType::Int32),
        ],
        program_seq(body, program_return(program_void_value())),
    )
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

fn construction_function(name: &str, body: ProgramStatement) -> ProgramFunction {
    let storage = ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable(CONTRACT_RESULT),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    ));
    program_function(
        ProgramType::VoidPointer,
        name,
        vec![program_parameter("input", ProgramType::Int32)],
        body,
    )
    .with_construction_return(node_layout())
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

fn node_construction_body() -> ProgramStatement {
    let destination = crate::kernel::program_expression::variable(CONTRACT_RESULT);
    let field = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::pointer_offset_bytes(destination.clone(), 8),
        ProgramType::Int32Pointer,
    );
    program_seq(
        program_typed_store(
            destination.clone(),
            field.clone(),
            ProgramType::Int32Pointer,
        ),
        program_seq(
            program_typed_store(
                field,
                crate::kernel::program_expression::variable("input"),
                ProgramType::Int32,
            ),
            program_return(destination),
        ),
    )
}

// A result address alone grants no storage, layout match, or ownership, and
// returning it is not enough to establish that the object was initialized.
#[test]
fn construction_return_rejects_missing_binding_authority_and_partial_values() {
    let _session = crate::kernel::VerificationSession::enter();
    let raw = allocate_destination(
        &ExecutionState::new().with_population_creation_tracking(),
        "node",
    );
    let destination = raw.locals.slot("node").unwrap().clone();
    let selected = raw
        .clone()
        .with_aggregate_return_destination(destination.clone(), node_layout());
    let function = construction_function("construct_node", node_construction_body());
    for caller in [
        raw,
        selected
            .clone()
            .with_resource_context(ResourceContext::new()),
        selected.clone().with_aggregate_return_destination(
            destination.clone(),
            AggregateLayout::new(8, 8, vec![]),
        ),
        selected.clone().with_memory(SymbolicMemory::new()),
    ] {
        let paths = execute_program_function_paths_with_contract_resources(
            &caller,
            &function,
            &[crate::kernel::program_expression::int32_literal(37)],
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
            true,
            false,
        )
        .unwrap();
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, FunctionOutcome::RuntimeError(_)))
        );
    }
    let partial = construction_function(
        "partial_node",
        program_seq(
            program_typed_store(
                crate::kernel::program_expression::variable(CONTRACT_RESULT),
                crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable(CONTRACT_RESULT),
                        8,
                    ),
                    ProgramType::Int32Pointer,
                ),
                ProgramType::Int32Pointer,
            ),
            program_return(crate::kernel::program_expression::variable(CONTRACT_RESULT)),
        ),
    );
    let paths = execute_program_function_paths_with_contract_resources(
        &selected,
        &partial,
        &[crate::kernel::program_expression::int32_literal(37)],
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
        true,
        false,
    )
    .unwrap();
    assert!(paths.iter().all(|path| matches!(
        path.outcome,
        FunctionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
    )));
}

#[test]
fn construction_binding_retains_the_full_destination_loan_requirement() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = allocate_destination(&ExecutionState::new(), "node");
    let destination = state.locals.slot("node").unwrap().clone();
    let view = ResourceFact::view_memory(MemoryRange::new_with_element_width(
        destination.clone(),
        0u32.into(),
        8u32.into(),
        1,
    ));
    let (_, occurrences) =
        ResourceContext::new().unchecked_with_facts_and_occurrences([view.clone()]);
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let opening = ledger
        .borrowed_contract_input(holder, occurrences[0].1, view, None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let caller = state
        .with_aggregate_return_destination(destination.clone(), node_layout())
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(holder));
    let function = construction_function("loaned_destination", node_construction_body());
    let mut callee = ExecutionState::new();
    let mut obligations = Vec::new();
    assert!(
        construction_return::bind(
            &caller,
            function.contract_interface(),
            &mut callee,
            Some(&mut obligations),
        )
        .is_some()
    );
    let [obligation] = obligations.as_slice() else {
        panic!("expected the complete destination's write prerequisite");
    };
    assert!(obligation.requires_statement_entry());
    let bytes = node_layout().size_bytes();
    let range = MemoryRange::new_with_element_width(destination, 0u32.into(), bytes.into(), 1);
    assert_eq!(
        obligation.proposition(),
        &ledger.memory_access_requirement(&range).unwrap(),
    );
    assert!(!PureFactContext::new().proves_atomic_without_search(obligation.proposition()));
    assert!(
        construction_return::bind(
            &caller,
            function.contract_interface(),
            &mut ExecutionState::new(),
            None,
        )
        .is_none()
    );
}

#[test]
fn construction_destination_can_alias_an_argument_without_becoming_fresh() {
    let _session = crate::kernel::VerificationSession::enter();
    let result = crate::kernel::program_expression::variable(CONTRACT_RESULT);
    let field = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::pointer_offset_bytes(result.clone(), 8),
        ProgramType::Int32Pointer,
    );
    let storage = ResourceSpec::owned_memory(MemorySegment::new(
        result.clone(),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    ));
    for read_before_write in [false, true] {
        let write = if read_before_write {
            program_typed_store(
                field.clone(),
                crate::kernel::program_expression::typed_load(
                    crate::kernel::program_expression::variable("alias"),
                    ProgramType::Int32,
                ),
                ProgramType::Int32,
            )
        } else {
            program_typed_store(
                crate::kernel::program_expression::variable("alias"),
                crate::kernel::program_expression::int32_literal(7),
                ProgramType::Int32,
            )
        };
        let function = program_function(
            ProgramType::VoidPointer,
            "alias_node",
            vec![program_parameter("alias", ProgramType::Int32Pointer)],
            program_seq(
                write,
                program_seq(
                    program_typed_store(result.clone(), field.clone(), ProgramType::Int32Pointer),
                    program_return(result.clone()),
                ),
            ),
        )
        .with_construction_return(node_layout())
        .with_resource_summary(vec![storage.clone()], vec![storage.clone()]);
        let raw = allocate_destination(
            &ExecutionState::new().with_population_creation_tracking(),
            "node",
        );
        let at = raw.locals.slot("node").unwrap().clone();
        let selected = raw.with_aggregate_return_destination(at.clone(), node_layout());
        let paths = execute_program_function_paths_with_contract_resources(
            &selected,
            &function,
            &[crate::kernel::program_expression::pointer_value(
                at.offset_by_bytes(8),
            )],
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
            true,
            false,
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one alias case");
        };
        if read_before_write {
            assert!(matches!(
                path.outcome,
                FunctionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
            ));
        } else {
            let FunctionOutcome::Return { value, state } = &path.outcome else {
                panic!("alias store construction failed: {:?}", path.outcome);
            };
            assert_eq!(pointer(&value.native()), at);
            assert_eq!(
                state.memory.known_value(&at.offset_by_bytes(8)),
                Some(int32(7))
            );
        }
    }
}

// Full-expression materialization copies pointer values before the temporary
// expires. Only a pointer into separate caller storage remains dereferenceable.
#[test]
fn construction_temporary_retirement_preserves_copies_and_external_backing() {
    for points_to_self in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let result = crate::kernel::program_expression::variable(CONTRACT_RESULT);
        let field = crate::kernel::program_expression::cast(
            crate::kernel::program_expression::pointer_offset_bytes(result.clone(), 8),
            ProgramType::Int32Pointer,
        );
        let owner = ResourceSpec::owned_memory(MemorySegment::new(
            result.clone(),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(4),
        ));
        let factory = program_function(
            ProgramType::VoidPointer,
            "materialize_descriptor",
            vec![program_parameter("backing", ProgramType::Int32Pointer)],
            program_seq(
                program_typed_store(
                    result.clone(),
                    if points_to_self {
                        field.clone()
                    } else {
                        crate::kernel::program_expression::variable("backing")
                    },
                    ProgramType::Int32Pointer,
                ),
                program_seq(
                    program_typed_store(
                        field,
                        crate::kernel::program_expression::int32_literal(37),
                        ProgramType::Int32,
                    ),
                    program_return(result),
                ),
            ),
        )
        .with_construction_return(node_layout())
        .with_resource_summary(vec![owner.clone()], vec![owner]);
        let environment = ExecutionEnvironment::new().with_function((factory).with_inline_body());
        let sequence =
            |statements: Vec<ProgramStatement>| statements.into_iter().reduce(program_seq).unwrap();
        let prefix = sequence(vec![
            program_declare("backing", ProgramType::Int32),
            program_assign(
                "backing",
                crate::kernel::program_expression::int32_literal(23),
            ),
            program_allocate_aggregate_destination("node", node_layout()),
            program_allocate_aggregate_destination("temporary", node_layout()),
            program_call_construct(
                "temporary",
                "materialize_descriptor",
                vec![crate::kernel::program_expression::addr_of("backing")],
            ),
            program_copy_aggregate(
                crate::kernel::program_expression::variable("node"),
                crate::kernel::program_expression::variable("temporary"),
                node_layout(),
            ),
        ]);
        let paths = execute_execution_statement_paths(
            &ExecutionState::new().with_population_creation_tracking(),
            &prefix,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&environment),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one materialization path");
        };
        let StatementOutcome::Normal(state) = &path.outcome else {
            panic!("materialization must finish: {:?}", path.outcome);
        };
        let temporary = state
            .locals
            .aggregate_object_pointer("temporary")
            .unwrap()
            .clone();
        let node = state
            .locals
            .aggregate_object_pointer("node")
            .unwrap()
            .clone();
        let backing = state.locals.slot("backing").unwrap().clone();
        let copied = state.memory.known_value(&node).unwrap();
        let referent = if points_to_self {
            temporary.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        assert_eq!(pointer(&copied), referent);
        let retirement = program_end_automatic_lifetimes(vec!["temporary".into()]);
        let checked = prove_symbolic_program_execution_paths_with_environment(
            state.as_ref().clone(),
            retirement,
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
        let [path] = checked.paths() else {
            panic!("one retirement path");
        };
        let after = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Normal(after),
                ..
            } => after,
            _ => panic!("checked temporary retirement"),
        };
        assert!(after.locals.aggregate_object_pointer("temporary").is_none());
        assert!(after.memory.is_ended_local_block(&temporary.base));
        assert!(!after.memory.has_block(&temporary.base));
        assert!(after.memory.has_block(&node.base));
        assert!(after.memory.has_block(&backing.base));
        assert_eq!(after.memory.known_value(&node), Some(copied));
        assert_eq!(after.memory.known_value(&backing), Some(int32(23)));
        assert!(
            after
                .resources
                .memory_write_range(&node, 16, &PureFactContext::new())
                .is_some()
        );
        assert!(
            after
                .resources
                .memory_write_range(&temporary, 16, &PureFactContext::new())
                .is_none()
        );
        let read = execute_execution_statement_paths(
            after,
            &program_return(crate::kernel::program_expression::typed_load(
                crate::kernel::program_expression::pointer_value(referent),
                ProgramType::Int32,
            )),
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&environment),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(read.len(), 1);
        if points_to_self {
            assert!(matches!(
                read[0].outcome,
                StatementOutcome::UndefinedBehavior(_)
            ));
        } else {
            assert!(
                matches!(&read[0].outcome, StatementOutcome::Return { value, .. } if *value.native() == int32(23))
            );
        }
    }
}

#[test]
fn construction_destination_survives_substitution_and_requires_agreement_at_join() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(873_003);
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_aggregate_return_destination(Address::symbolic(variable), node_layout());
    let mut variables = BTreeSet::new();
    collect_execution_state_bitvector_variables(&state, &mut variables);
    assert!(variables.contains(&variable));
    let proposition = Proposition::ProgramStatementVerifies {
        state: Box::new(state.clone()),
        statement: Box::new(program_skip()),
        outcome: StatementOutcome::Normal(Box::new(state.clone())),
    };
    let at = SymbolicMemory::frame_local_pointer(15, "caller");
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &proposition,
        variable,
        &at,
    );
    let Proposition::ProgramStatementVerifies {
        state: mapped,
        outcome: StatementOutcome::Normal(after),
        ..
    } = mapped
    else {
        panic!("substituted construction transition");
    };
    assert_eq!(mapped.aggregate_destination.as_ref().unwrap().pointer, at);
    assert_eq!(mapped.aggregate_destination, after.aggregate_destination);
    assert!(!state.shares_non_memory_storage_with(&mapped));
    assert!(
        abstract_execution_state_for_interface_join_across(&state, &[&state, &mapped], 0).is_err()
    );
}

// This tests the existing explicit-destination procedure building block,
// without the legacy placeholder-seeding declaration. It does not pass a
// supplied destination off as a by-value aggregate result.
// C++ copy-assignment coverage does not exercise the function return
// materializer. A future destination-return path must not silently change
// this existing copy mode to rebase self-pointers or elide its copies.
#[test]
fn aggregate_copy_return_preserves_self_pointer_through_two_materializations() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = SymbolicMemory::frame_local_pointer(100, "node");
    let self_pointer =
        ProgramValue::typed_pointer(source.offset_by_bytes(8), ProgramType::Int32Pointer);
    let memory = SymbolicMemory::new()
        .with_block(source.base.clone(), 16)
        .store(source.clone(), self_pointer.clone())
        .store(
            source.offset_by_bytes(8),
            ProgramValue::Int32(MachineTerm::constant(37)),
        );
    let mut state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(memory);
    let function = copy_function();
    let first = complete_aggregate_return(
        &mut state,
        &function,
        ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer),
    )
    .expect("first copy result");
    let second = complete_aggregate_return(&mut state, &function, first.clone())
        .expect("second copy result");
    assert_ne!(pointer(&first).base, source.base);
    assert_ne!(pointer(&second).base, pointer(&first).base);
    for result in [&first, &second] {
        let result = pointer(result);
        assert_eq!(
            state.memory.known_value(&result),
            Some(self_pointer.clone())
        );
        assert_ne!(pointer(&self_pointer), result.offset_by_bytes(8));
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(ProgramValue::Int32(MachineTerm::constant(37))),
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
        let source = SymbolicMemory::frame_local_pointer(100, "descriptor");
        let backing = SymbolicMemory::frame_local_pointer(101, "caller_backing");
        let caller = SymbolicMemory::new()
            .with_block(backing.base.clone(), 4)
            .store(
                backing.clone(),
                ProgramValue::Int32(MachineTerm::constant(23)),
            );
        let referent = if points_to_self {
            source.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        let field = ProgramValue::typed_pointer(referent.clone(), ProgramType::Int32Pointer);
        let memory = caller
            .clone()
            .with_block(source.base.clone(), 16)
            .store(source.clone(), field.clone())
            .store(
                source.offset_by_bytes(8),
                ProgramValue::Int32(MachineTerm::constant(23)),
            );
        let mut state = ExecutionState::new()
            .with_population_creation_tracking()
            .with_memory(memory);
        state.locals.set_aggregate_object_at(
            "descriptor".to_string(),
            node_layout(),
            source.clone(),
        );
        let function = copy_function();
        let result = complete_aggregate_return(
            &mut state,
            &function,
            ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer),
        )
        .expect("copy result");
        set_function_result(&mut state, &function, result.clone());
        let memory =
            end_function_body_automatic_lifetimes(&state, &function, &caller, Some(&result))
                .expect("callee retirement");
        assert!(!memory.has_block(&source.base));
        assert!(memory.has_block(&pointer(&result).base));
        assert!(memory.has_block(&backing.base));
        assert_eq!(memory.known_value(&pointer(&result)), Some(field));
        assert_eq!(memory.has_block(&referent.base), !points_to_self);
        assert_eq!(
            memory.known_value(&backing),
            Some(ProgramValue::Int32(MachineTerm::constant(23))),
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
    assert!(matches!(pointer(&first).base, AddressBase::Temporary(_)));
    assert!(matches!(pointer(&second).base, AddressBase::Temporary(_)));
    assert_ne!(pointer(&first).base, pointer(&second).base);
}

// A by-value result must not erase the caller's read history. Check the
// value judgment and its certificate, then refuse it across an actual write.
#[test]
fn aggregate_copy_result_preserves_unrelated_entry_byte_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = SymbolicMemory::local_pointer("input-byte");
    let before = SymbolicMemory::new().with_block(input.base.clone(), 1);
    let read = |memory: &SymbolicMemory| {
        MachineTerm::MemoryLoad(
            ProgramPoint::at(&(crate::kernel::intern_memory(memory.clone()))),
            Box::new(input.clone()),
            LoadKind::UInt8,
        )
    };
    let equality = |memory: &SymbolicMemory| {
        Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(read(memory)),
                right: Box::new(read(&before)),
            },
            true,
        )
    };
    let function = copy_function();
    let mut state = ExecutionState::new().with_memory(before.clone());
    let result = symbolic_contract_result(function.contract_interface(), Variable(870_003));
    set_function_result(&mut state, &function, result);
    let context = PureFactContext::new();
    let proof = crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
        &(context),
        &equality(state.memory()),
    )
    .expect("a returned record leaves the caller's byte unchanged");
    assert!(proof.check(&context));
    assert!(proof.context_premises().is_empty());

    let written = state
        .memory()
        .clone()
        .store(input.clone(), crate::kernel::uint8(7));
    assert!(
        crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
            &(context),
            &equality(&written)
        )
        .is_none()
    );
}

// Return completion must reject before allocating a result or copying any
// prefix. The two body-completion paths must not supply separate, drifting
// checks for this precondition.
#[test]
fn aggregate_copy_return_refuses_partial_initialization_without_changing_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = SymbolicMemory::frame_local_pointer(100, "partial");
    let mut state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            SymbolicMemory::new()
                .with_block(source.base.clone(), 16)
                .store(
                    source.clone(),
                    ProgramValue::typed_pointer(
                        source.offset_by_bytes(8),
                        ProgramType::Int32Pointer,
                    ),
                ),
        );
    let before = state.clone();
    assert_eq!(
        complete_aggregate_return(
            &mut state,
            &copy_function(),
            ProgramValue::typed_pointer(source, ProgramType::VoidPointer),
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
    let source = Address::symbolic(Variable(870_003));
    let mut state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 16));
    let value = ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer);
    assert_eq!(
        complete_aggregate_return(&mut state, &copy_function(), value.clone()),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.clone(),
        ProgramValue::typed_pointer(source.offset_by_bytes(8), ProgramType::Int32Pointer),
    ));
    assert_eq!(
        complete_aggregate_return(&mut state, &copy_function(), value.clone()),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.offset_by_bytes(8),
        ProgramValue::Int32(MachineTerm::constant(37)),
    ));
    assert!(complete_aggregate_return(&mut state, &copy_function(), value).is_ok());
}

#[test]
fn symbolic_construction_storage_is_unreadable_until_written() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address::symbolic(Variable(870_004));
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
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
                raw.clone().store(
                    source.clone(),
                    ProgramValue::Int32(MachineTerm::constant(37)),
                )
            } else {
                raw.clone()
            };
            let state = ExecutionState::new()
                .with_population_creation_tracking()
                .with_memory(memory)
                .with_resource_context(ResourceContext::new().unchecked_with_fact(
                    ResourceFact::own_memory(MemoryRange::new(
                        source.clone(),
                        0u32.into(),
                        1u32.into(),
                    )),
                ));
            let paths = execute_execution_statement_paths(
                &state,
                &program_return(crate::kernel::program_expression::typed_load(
                    crate::kernel::program_expression::pointer_value(source.clone()),
                    ProgramType::Int32,
                )),
                &assumptions,
                ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .expect("raw destination read");
            let [path] = paths.as_slice() else {
                panic!("expected one read path");
            };
            if written {
                assert!(matches!(path.outcome, StatementOutcome::Return { .. }));
            } else {
                assert!(
                    matches!(
                        path.outcome,
                        StatementOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
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
    let source = Address::symbolic(Variable(870_005));
    let alias = Address::symbolic(Variable(870_006));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::address_equal(source.clone(), alias.clone()),
        true,
    );
    for forgotten in [false, true] {
        for written in [false, true] {
            for read in [&source, &alias] {
                let mut memory =
                    SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
                if written {
                    memory = memory.store(alias.clone(), ProgramValue::Int32(37u32.into()));
                }
                if forgotten {
                    memory = memory.with_loop_memory_havoc_preserving_loans(
                        Variable(870_020),
                        &BTreeSet::new(),
                        None,
                        None,
                    );
                }
                let state = ExecutionState::new()
                    .with_population_creation_tracking()
                    .with_memory(memory)
                    .with_resource_context(ResourceContext::new().unchecked_with_fact(
                        ResourceFact::own_memory(MemoryRange::new(
                            source.clone(),
                            0u32.into(),
                            1u32.into(),
                        )),
                    ));
                let paths = execute_execution_statement_paths(
                    &state,
                    &program_return(crate::kernel::program_expression::typed_load(
                        ProgramExpression::Value(ProgramValue::Pointer(
                            Pointer::new(source.clone(), ProgramType::Int32Pointer)
                                .with_address(read.clone()),
                        )),
                        ProgramType::Int32,
                    )),
                    &assumptions,
                    ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
                    &mut ExecutionBudget::default(),
                )
                .expect("aliased destination read");
                assert!(!paths.is_empty());
                for path in paths {
                    if written {
                        assert!(
                            matches!(path.outcome, StatementOutcome::Return { .. }),
                            "{:?}",
                            path.outcome
                        );
                    } else {
                        assert!(
                            matches!(
                                path.outcome,
                                StatementOutcome::UndefinedBehavior(
                                    UndefinedBehavior::UninitializedRead
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
    let source = Address::symbolic(Variable(870_007));
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
    for address in [source.clone(), Address::symbolic(Variable(870_008))] {
        let named = raw
            .clone()
            .materialize_named_cell(address.clone(), ProgramValue::Int32(37u32.into()));
        assert_eq!(named, raw);
        assert!(!named.has_initialized_bytes_at(&address, 4));
    }
}

// Forgetting values preserves writes; a branch that skipped the write still
// prevents the joined destination from counting as completely initialized.
#[test]
fn symbolic_construction_initialization_survives_havoc_and_intersects_at_join() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address::symbolic(Variable(870_009));
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 8);
    let partial = raw
        .clone()
        .store(source.clone(), ProgramValue::Int32(37u32.into()));
    let full = partial
        .clone()
        .store(source.offset_by_bytes(4), ProgramValue::Int32(42u32.into()));
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
fn symbolic_construction_initialization_substitution_preserves_size() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(870_012);
    let source = Address::symbolic(variable);
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
    let destination = SymbolicMemory::frame_local_pointer(20, "container").offset_by_bytes(8);
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_memory(
        &raw,
        variable,
        &destination,
    );
    assert!(mapped.may_read_uninitialized_object(&destination, 4));
    assert!(!mapped.may_read_uninitialized_object(&destination.offset_by_bytes(4), 4));
    assert!(!mapped.may_read_uninitialized_object(
        &SymbolicMemory::frame_local_pointer(20, "container").offset_by_bytes(4),
        4
    ));
    assert!(!mapped.has_initialized_bytes_at(&destination, 4));
}

// Instantiating an object can put a variable only in its byte offset. Both
// whole and incremental collectors must reserve it against fresh witnesses.
#[test]
fn construction_object_offsets_participate_in_fresh_variable_collection() {
    let _session = crate::kernel::VerificationSession::enter();
    let source_variable = Variable(870_013);
    let offset_variable = Variable(870_014);
    let source = Address::symbolic(source_variable);
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
    let destination = Address {
        base: "local:variable-container".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(offset_variable), 4),
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
    let before = crate::kernel::intern_memory(mapped.clone());
    let mut cached = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&before, &mut cached);
    assert_eq!(cached, whole);
    let after = crate::kernel::intern_memory(mapped.store(
        SymbolicMemory::frame_local_pointer(22, "unrelated"),
        ProgramValue::Int32(37u32.into()),
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
    let source = Address::symbolic(Variable(870_015));
    let raw = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
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
    let source = Address::symbolic(Variable(870_017));
    let alias_variable = Variable(870_018);
    let alias = Address::symbolic(alias_variable);
    let written = SymbolicMemory::new()
        .with_uninitialized_block(source.base.clone(), 4)
        .store(alias.clone(), ProgramValue::Int32(37u32.into()));
    let before = crate::kernel::intern_memory(written.clone());
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
        &crate::kernel::intern_memory(forgotten),
        &mut cached,
    );
    assert!(cached.contains(&alias_variable));
    assert_eq!(whole, cached);
}

// A constructor keeps its native void signature. Completion checks the entry
// destination even when the ordinary pointer parameter has been reassigned.
#[test]
fn construction_parameter_completion_checks_original_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    for complete in [false, true] {
        let field = crate::kernel::program_expression::cast(
            crate::kernel::program_expression::pointer_offset_bytes(
                crate::kernel::program_expression::variable("destination"),
                8,
            ),
            ProgramType::Int32Pointer,
        );
        let body = program_seq(
            program_typed_store(
                crate::kernel::program_expression::variable("destination"),
                field.clone(),
                ProgramType::Int32Pointer,
            ),
            if complete {
                program_typed_store(
                    field,
                    crate::kernel::program_expression::variable("input"),
                    ProgramType::Int32,
                )
            } else {
                program_skip()
            },
        );
        let function = destination_procedure("initialize_node", body)
            .with_construction_parameter(0, node_layout());
        let caller = allocate_destination(
            &ExecutionState::new().with_population_creation_tracking(),
            "node",
        );
        let at = caller.locals.slot("node").unwrap().clone();
        let paths = execute_program_function_paths_with_contract_resources(
            &caller,
            &function,
            &[
                crate::kernel::program_expression::pointer_value(at.clone()),
                crate::kernel::program_expression::int32_literal(37),
            ],
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
            true,
            false,
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one constructor path");
        };
        if complete {
            let FunctionOutcome::Return { state, .. } = &path.outcome else {
                panic!("constructor completion failed");
            };
            assert!(
                state.aggregate_destination.is_none(),
                "callee destination cannot replace caller metadata"
            );
            assert!(!aggregate_copy_reads_uninitialized(
                &state.memory,
                &at,
                &node_layout()
            ));
            assert!(
                !state.memory.has_initialized_bytes_at(&at, 16),
                "padding stays unwritten"
            );
        } else {
            assert!(matches!(
                path.outcome,
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(_))
            ));
        }
    }
    // Reassigning the parameter to an unrelated initialized object does not
    // complete the original destination.
    let function = program_function(
        ProgramType::Void,
        "redirect_constructor",
        vec![
            program_parameter("destination", ProgramType::Int32Pointer),
            program_parameter("other", ProgramType::Int32Pointer),
        ],
        program_seq(
            program_assign(
                "destination",
                crate::kernel::program_expression::variable("other"),
            ),
            program_return(program_void_value()),
        ),
    )
    .with_construction_parameter(0, node_layout());
    let caller = allocate_destination(
        &allocate_destination(
            &ExecutionState::new().with_population_creation_tracking(),
            "node",
        ),
        "other",
    );
    let at = caller.locals.slot("node").unwrap().clone();
    let other = caller.locals.slot("other").unwrap().clone();
    let memory = caller.memory.clone().with_initialized_object(&other, 16);
    let caller = caller.with_memory(memory);
    let paths = execute_program_function_paths_with_contract_resources(
        &caller,
        &function,
        &[
            crate::kernel::program_expression::pointer_value(at),
            crate::kernel::program_expression::pointer_value(other),
        ],
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
        true,
        false,
    )
    .unwrap();
    assert!(paths.iter().all(|path| matches!(
        path.outcome,
        FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(_))
    )));
}

#[test]
fn raw_object_footprint_does_not_resize_or_initialize_parent_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let at = Address::symbolic(Variable(873_031));
    let memory = SymbolicMemory::new()
        .with_block(at.base.clone(), 32)
        .with_uninitialized_object(at.offset_by_bytes(8), 8);
    assert_eq!(memory.block_size(&at.base), Some(&32u32.into()));
    assert!(memory.may_read_uninitialized_object(&at.offset_by_bytes(8), 8));
    assert!(!memory.may_read_uninitialized_object(&at, 8));
    assert!(!memory.may_read_uninitialized_object(&at.offset_by_bytes(16), 8));
    assert!(!memory.has_initialized_bytes_at(&at.offset_by_bytes(8), 8));
}

// The admitted value-only constructor profile must yield the same observable
// descriptor after zero, one or several explicit trivial result copies.
#[test]
fn value_only_constructor_preserves_descriptor_across_result_copy_chains() {
    let layout = AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("data", 0, ProgramType::Int32Pointer),
            AggregateField::new("extent", 8, ProgramType::UInt64),
        ],
    );
    let destination = crate::kernel::program_expression::variable("destination");
    let owner = ResourceSpec::owned_memory(
        MemorySegment::new(
            destination.clone(),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(16),
        )
        .with_element_width(1),
    );
    let constructor = program_function(
        ProgramType::Void,
        "construct_descriptor",
        vec![
            program_parameter("destination", ProgramType::Int32Pointer),
            program_parameter("backing", ProgramType::Int32Pointer),
            program_parameter("extent", ProgramType::UInt64),
        ],
        program_seq(
            program_typed_store(
                destination.clone(),
                crate::kernel::program_expression::variable("backing"),
                ProgramType::Int32Pointer,
            ),
            program_seq(
                program_typed_store(
                    crate::kernel::program_expression::pointer_offset_bytes(destination, 8),
                    crate::kernel::program_expression::variable("extent"),
                    ProgramType::UInt64,
                ),
                program_return(program_void_value()),
            ),
        ),
    )
    .with_construction_parameter(0, layout.clone())
    .with_resource_summary(vec![owner.clone()], vec![owner]);
    let environment = ExecutionEnvironment::new().with_function((constructor).with_inline_body());
    for copies in [0, 1, 3] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut statements = vec![
            program_declare("backing", ProgramType::Int32),
            program_assign(
                "backing",
                crate::kernel::program_expression::int32_literal(23),
            ),
            program_allocate_aggregate_destination("result", layout.clone()),
        ];
        let names = (0..copies)
            .map(|index| format!("temporary_{index}"))
            .collect::<Vec<_>>();
        for name in &names {
            statements.push(program_allocate_aggregate_destination(name, layout.clone()));
        }
        let first = names.first().map_or("result", String::as_str);
        statements.push(program_call(
            "construct_descriptor",
            vec![
                crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(first),
                    ProgramType::Int32Pointer,
                ),
                crate::kernel::program_expression::addr_of("backing"),
                crate::kernel::program_expression::uint64_literal(37),
            ],
        ));
        for (index, name) in names.iter().enumerate() {
            let target = names.get(index + 1).map_or("result", String::as_str);
            statements.push(program_copy_aggregate(
                crate::kernel::program_expression::variable(target),
                crate::kernel::program_expression::variable(name),
                layout.clone(),
            ));
        }
        if !names.is_empty() {
            statements.push(program_end_automatic_lifetimes(
                names.iter().rev().cloned().map(Into::into).collect(),
            ));
        }
        // Ordinary local storage has implicit authority rather than a range fact.
        // Writing through the saved backing pointer checks that retirement kept it.
        statements.push(program_typed_store(
            crate::kernel::program_expression::addr_of("backing"),
            crate::kernel::program_expression::int32_literal(24),
            ProgramType::Int32,
        ));
        let statement = statements.into_iter().reduce(program_seq).unwrap();
        let checked = prove_symbolic_program_execution_paths_with_environment(
            ExecutionState::new().with_population_creation_tracking(),
            statement,
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
        let [path] = checked.paths() else {
            panic!("one descriptor construction path");
        };
        let state = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Normal(state),
                ..
            } => state,
            Proposition::ProgramStatementVerifies { outcome, .. } => {
                panic!("descriptor construction and copies must complete: {outcome:?}")
            }
            _ => panic!("descriptor construction and copies must produce a statement outcome"),
        };
        let result = state.locals.aggregate_object_pointer("result").unwrap();
        let backing = state.locals.slot("backing").unwrap();
        assert_eq!(
            pointer(&state.memory.known_value(result).unwrap()),
            *backing
        );
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(ProgramValue::UInt64(MachineTerm::uint64_constant(37)))
        );
        assert_eq!(state.memory.known_value(backing), Some(int32(24)));
        assert!(
            state
                .resources
                .memory_write_range(result, 16, &PureFactContext::new())
                .is_some()
        );
        for name in &names {
            assert!(state.locals.aggregate_object_pointer(name).is_none());
        }
    }
}

// A summary can establish initialized storage without naming its pointer field's
// value. Copying that value must use the same typed read as an ordinary load,
// including when the storage holding it ends immediately afterwards.
#[test]
fn copying_unknown_pointer_field_preserves_its_value_after_source_retirement() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut state = allocate_destination(
        &ExecutionState::new().with_population_creation_tracking(),
        "source",
    );
    state = allocate_destination(&state, "target");
    let source = state
        .locals
        .aggregate_object_pointer("source")
        .unwrap()
        .clone();
    let target = state
        .locals
        .aggregate_object_pointer("target")
        .unwrap()
        .clone();
    state.set_memory(state.memory.clone().with_initialized_object(&source, 16));
    let expected = crate::kernel::eval::symbolic_storage_cell_value(
        &state.memory,
        &source,
        ProgramType::Int32Pointer,
        true,
    )
    .unwrap();
    let checked = prove_symbolic_program_execution_paths_with_environment(
        state,
        program_seq(
            program_copy_aggregate(
                crate::kernel::program_expression::variable("target"),
                crate::kernel::program_expression::variable("source"),
                node_layout(),
            ),
            program_end_automatic_lifetimes(vec!["source".into()]),
        ),
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    );
    let [path] = checked.paths() else {
        panic!("one checked copy path");
    };
    let state = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Normal(state),
            ..
        } => state,
        _ => panic!("initialized unknown pointer copy must complete"),
    };
    assert_eq!(state.memory.known_value(&target), Some(expected));
    assert!(state.locals.aggregate_object_pointer("source").is_none());
    assert!(
        state
            .resources
            .memory_write_range(&target, 16, &PureFactContext::new())
            .is_some()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/aggregate_return_tests.rs");
}

#[test]
fn aggregate_return_temporary_copy_requires_its_recorded_size() {
    let layout = node_layout();
    let temporary = Address::verifier_temporary(Variable(870_101));
    let source = Pointer::new(temporary.clone(), ProgramType::UInt8Pointer);
    let assumptions = PureFactContext::new();
    for bytes in [0, 8, 16] {
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(temporary.base.clone(), bytes));
        assert_eq!(
            crate::kernel::eval::missing_aggregate_copy_read_resource(
                &state,
                &source,
                &layout,
                &assumptions
            )
            .is_none(),
            bytes == 16,
        );
    }
    for block in [
        AddressBase::Heap(870_102),
        AddressBase::Symbolic(Variable(870_103)),
    ] {
        let pointer = Address {
            base: block.clone(),
            offset: AddressOffset::Constant(0),
        };
        let source = Pointer::new(pointer, ProgramType::UInt8Pointer);
        let state = ExecutionState::new().with_memory(SymbolicMemory::new().with_block(block, 16));
        assert!(
            crate::kernel::eval::missing_aggregate_copy_read_resource(
                &state,
                &source,
                &layout,
                &assumptions
            )
            .is_some(),
            "external storage still requires a resource"
        );
    }
}

#[test]
fn copying_unknown_uint32_pointer_field_keeps_its_value_and_initialization_check() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = SymbolicMemory::local_pointer("unsigned_pointer_source");
    let target = SymbolicMemory::local_pointer("unsigned_pointer_target");
    let layout = AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("data", 0, ProgramType::UInt32Pointer),
            AggregateField::new("size", 8, ProgramType::UInt64),
        ],
    );
    let memory = SymbolicMemory::new()
        .with_block(source.base.clone(), 16)
        .with_block(target.base.clone(), 16)
        .with_initialized_object(&source, 16);
    let expected = crate::kernel::eval::symbolic_storage_cell_value(
        &memory,
        &source,
        ProgramType::UInt32Pointer,
        true,
    )
    .unwrap();
    let copied = copy_aggregate_fields_checked(memory, &source, &target, &layout)
        .unwrap()
        .without_local_block(&source.base);
    assert_eq!(copied.known_value(&target), Some(expected));
    let uninitialized = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 16);
    assert!(matches!(
        copy_aggregate_fields_checked(uninitialized, &source, &target, &layout),
        Err(UndefinedBehavior::UninitializedRead),
    ));
}

#[test]
fn aggregate_return_storage_is_distinct_from_a_same_frame_source_named_return() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = SymbolicMemory::frame_local_pointer(0, "__return");
    let self_pointer =
        ProgramValue::typed_pointer(source.offset_by_bytes(8), ProgramType::Int32Pointer);
    let caller = SymbolicMemory::new();
    let mut state = ExecutionState::new().with_memory(
        caller
            .clone()
            .with_block(source.base.clone(), 16)
            .store(source.clone(), self_pointer.clone())
            .store(source.offset_by_bytes(8), int32(37)),
    );
    state
        .locals
        .set_aggregate_object_at("__return", node_layout(), source.clone());
    let function = copy_function();
    let first = complete_aggregate_return(
        &mut state,
        &function,
        ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer),
    )
    .unwrap();
    let second = complete_aggregate_return(&mut state, &function, first.clone()).unwrap();
    assert_eq!(
        pointer(&first).base,
        AddressBase::AggregateReturn { frame: 0 }
    );
    assert_eq!(
        pointer(&second).base,
        AddressBase::AggregateReturn { frame: 1 }
    );
    assert_eq!(state.next_local_frame, 2);
    for result in [&first, &second] {
        let destination = pointer(result);
        assert!(destination.base.proven_distinct(&source.base));
        assert_eq!(
            state.memory.known_value(&destination),
            Some(self_pointer.clone())
        );
        assert_eq!(
            state.memory.known_value(&destination.offset_by_bytes(8)),
            Some(int32(37))
        );
    }
    set_function_result(&mut state, &function, second.clone());
    let after =
        end_function_body_automatic_lifetimes(&state, &function, &caller, Some(&second)).unwrap();
    assert!(!after.has_block(&source.base));
    assert!(after.has_block(&pointer(&second).base));
    assert_eq!(after.known_value(&pointer(&second)), Some(self_pointer));
}
