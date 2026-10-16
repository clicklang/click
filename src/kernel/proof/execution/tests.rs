#[test]
fn balanced_unit_sum_domain_requires_all_three_original_domains() {
    use crate::kernel::ConditionTerm;
    let a = Bitvector32Term::Variable(Variable(100));
    let b = Bitvector32Term::Variable(Variable(101));
    let one = Bitvector32Term::Constant(1);
    let guards = [
        ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
        ConditionTerm::signed_add_overflows(a.clone(), one.clone()),
        ConditionTerm::signed_subtract_overflows(b.clone(), one.clone()),
    ];
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(
            Bitvector32Term::add(a.clone(), one.clone()),
            Bitvector32Term::subtract(b.clone(), one.clone()),
        ),
        false,
    );
    for missing in 0..=3 {
        let facts = guards
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != missing)
            .fold(PureFactContext::new(), |facts, (_, condition)| {
                facts.assume_condition(condition.clone(), false)
            });
        assert_eq!(
            super::authority_control_evaluation_condition_proven(&facts, &goal),
            missing == 3
        );
    }
    // Return reverses the two original summands. Commutativity must
    // preserve the check without dropping either child-domain premise.
    let reversed_guards = [
        ConditionTerm::signed_add_overflows(b.clone(), a.clone()),
        guards[1].clone(),
        guards[2].clone(),
    ];
    for missing in 0..=3 {
        let facts = reversed_guards
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != missing)
            .fold(PureFactContext::new(), |facts, (_, condition)| {
                facts.assume_condition(condition.clone(), false)
            });
        assert_eq!(
            super::authority_control_evaluation_condition_proven(&facts, &goal),
            missing == 3
        );
    }
    // The original sum fits, but the increment wraps at MAX, or the
    // predecessor wraps at MIN. Modular equality must not certify either.
    for (left, right) in [(i32::MAX, 0), (0, i32::MIN)] {
        assert!(left.checked_add(right).is_some());
        assert!(
            left.checked_add(1)
                .and_then(|x| right.checked_sub(1).and_then(|y| x.checked_add(y)))
                .is_none()
        );
    }
}

use super::*;
// The proposition search is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. Only these tests reach
// it from inside the kernel.
use crate::kernel::{
    Bitvector32Term, CComparisonOperator, CCompositeResourceDefinition, CMemory,
    CResourceAccessMode, CResourceFact, CResourceSpec, CType, CValue, Pointer, PointerBlock,
    PointerOffsetTerm, SpecExpression, c_function, int32,
};
use crate::surface::planning::proposition_search::PropositionSearch;

/// One arm state holding a checked view rooted in a fresh loan.
fn arm_holding_a_view(name: &str) -> (CState, crate::kernel::loans::LoanViewBinding) {
    let support_fact = CResourceFact::own_token(format!("{name}_support"), Vec::new());
    let viewed = CResourceFact::view_token(format!("{name}_view"), Vec::new());
    let resources = crate::kernel::ResourceContext::new()
        .unchecked_with_facts([support_fact.clone(), viewed.clone()]);
    let support = resources.owned_occurrences_for_fact(&support_fact)[0];
    let occurrence = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, support_fact)
        .expect("the arm's view is backed by a fresh loan");
    let binding = crate::kernel::loans::LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let state = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader))
        .with_resource_context_and_loan_dependencies(resources, [(occurrence, binding.clone())]);
    (state, binding)
}

#[test]
fn frame_exchange_retains_the_exits_exact_stable_view_dependency() {
    let (state, binding) = arm_holding_a_view("loop_exit");
    let body = state.resources();
    let original = body.occurrences_for_fact(&binding.viewed)[0];
    let (exit, inserted) = body
        .clone()
        .without_bound_view_occurrence(original, &binding)
        .unwrap()
        .unchecked_with_facts_and_occurrences([binding.viewed.clone()]);
    let final_occurrence = inserted[0].1;
    let exit = exit.with_loan_dependency(final_occurrence, binding.clone());
    let outside = CResourceFact::own_composite("outside".into(), Vec::new());
    let frame = body.clone().unchecked_with_fact(outside.clone());
    let restored = exit
        .restore_frame_after_exchange(body, &frame, &PureFactContext::new())
        .unwrap();
    assert!(restored.contains_exact_representation(&outside));
    assert_eq!(restored.loan_dependency(final_occurrence), Some(&binding));
    assert!(restored.loan_dependency(original).is_none());
    assert!(restored.view_fact_at_occurrence(original).is_none());
}

fn successor_carrying(binding: &crate::kernel::loans::LoanViewBinding) -> CState {
    let resources =
        crate::kernel::ResourceContext::new().unchecked_with_facts([binding.viewed.clone()]);
    let occurrence = resources.occurrences_for_fact(&binding.viewed)[0];
    // A fresh interface context: the occurrence is new, so only the
    // binding's own content can connect it to an arm's authority.
    CState::new()
        .with_resource_context_and_loan_dependencies(resources, [(occurrence, binding.clone())])
}

#[test]
fn an_interface_successor_may_only_carry_a_loan_an_arm_held() {
    let (left, left_binding) = arm_holding_a_view("left");
    let (right, right_binding) = arm_holding_a_view("right");

    // No claimed authority at all is always inherited.
    assert!(interface_successor_loans_are_inherited(
        &CState::new(),
        [&left, &right]
    ));
    // Either arm's own root is, whichever arm held it.
    assert!(interface_successor_loans_are_inherited(
        &successor_carrying(&left_binding),
        [&left, &right]
    ));
    assert!(interface_successor_loans_are_inherited(
        &successor_carrying(&right_binding),
        [&left, &right]
    ));
    // A root neither arm reached is not admitted by the join.
    let (_, outside) = arm_holding_a_view("outside");
    assert!(!interface_successor_loans_are_inherited(
        &successor_carrying(&outside),
        [&left, &right]
    ));
    // Nor is one arm's root once that arm is not part of the join.
    assert!(!interface_successor_loans_are_inherited(
        &successor_carrying(&right_binding),
        [&left, &left]
    ));
}

fn constructor_partition_fixture(
    width: usize,
) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
    constructor_partition_fixture_with_type(width, CType::Int32)
}

fn constructor_partition_fixture_with_type(
    width: usize,
    payload_type: CType,
) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
        AlgebraicVariantType,
    };
    let variants: Arc<[AlgebraicVariantType]> = (0..width)
        .map(|index| AlgebraicVariantType {
            name: format!("C{index}"),
            fields: vec![AlgebraicValueType::C(payload_type)],
        })
        .collect::<Vec<_>>()
        .into();
    let key = AlgebraicValueType::Algebraic {
        name: "Cases".into(),
        arguments: vec![],
    };
    let value = AlgebraicTerm {
        algebraic_type: AlgebraicType {
            rigid: false,
            name: "Cases".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
        },
        node: AlgebraicTermNode::Variable(Variable(8)),
    };
    let state = CState::new();
    let function = c_function(
        CType::Int32,
        "entry",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(4_000_000)),
        ))),
    );
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(
        core.record_checked_function_entry(&function, &[], &state, PureFactContext::new())
            .is_ok()
    );
    (core, value)
}

#[test]
fn constructor_partition_checks_complete_coverage_and_exact_scopes() {
    for width in [1, 2, 4, 16] {
        let (core, value) = constructor_partition_fixture(width);
        let root = ProofFacts::default();
        let (partition, fields, _) = core
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::CExecutionEnvironment::new(),
                &[],
                None,
                4_000_000,
                65_536,
            )
            .unwrap();
        assert_eq!(fields.len(), width);
        let mut traces = Vec::new();
        for index in 0..width {
            let mut arm = core.clone();
            assert!(arm.record_proof_case_arm(
                partition.clone(),
                index,
                root.with_fact(partition.case_fact(index).unwrap().clone())
            ));
            traces.push(arm.execution_evidence[0].clone());
        }
        assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
            &traces
        ));
        if width > 1 {
            assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
                &traces[1..]
            ));
        }
        let mut wrong = core.clone();
        assert!(!wrong.record_proof_case_arm(partition.clone(), width, root.clone()));
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, root.clone()));
        let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
        let extra = facts.with_fact(Proposition::Predicate {
            name: "unjustified".into(),
            arguments: vec![],
        });
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, extra));
        wrong.state = CState::new().with_local("changed", int32(1)).into();
        // A witness belongs to the exact state its partition was issued
        // against, so the moved frontier cannot take an arm of the old one.
        assert!(!wrong.record_proof_case_arm(partition.clone(), 0, facts));
        // It can issue its own, though: a proof `match` runs at any
        // frontier the proof has reached, not only at an unchanged entry.
        let (moved, _, _) = wrong
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::CExecutionEnvironment::new(),
                &[],
                None,
                4_000_000,
                65_536,
            )
            .expect("a frontier that has moved still issues its partition");
        let moved_facts = root.with_fact(moved.case_fact(0).unwrap().clone());
        assert!(wrong.record_proof_case_arm(moved, 0, moved_facts));
    }
}

#[test]
fn constructor_partition_exclusion_requires_its_exact_contradiction() {
    let (core, mut value) = constructor_partition_fixture(2);
    value.node = crate::kernel::AlgebraicTermNode::Constructor {
        variant: "C0".into(),
        fields: vec![crate::kernel::AlgebraicValue::C(int32(11))],
    };
    let root = ProofFacts::default();
    let (partition, _, _) = core
        .algebraic_case_partition(
            &root,
            &value,
            &crate::kernel::CExecutionEnvironment::new(),
            &[],
            None,
            4_000_000,
            65_536,
        )
        .unwrap();
    let live = partition.case_fact(0).unwrap().clone();
    let dead = partition.case_fact(1).unwrap().clone();
    assert!(
        partition
            .excluding_constructor_case(0, live.clone())
            .is_none()
    );
    assert!(
        partition
            .excluding_constructor_case(1, live.clone())
            .is_none()
    );
    assert!(
        partition
            .excluding_constructor_case(2, dead.clone())
            .is_none()
    );
    let excluded = partition.excluding_constructor_case(1, dead).unwrap();
    assert!(!Arc::ptr_eq(&partition.identity, &excluded.identity));
    let mut old_arm = core.clone();
    let live_facts = partition.facts_for_case(0).unwrap();
    assert!(old_arm.record_proof_case_arm(partition, 0, live_facts));
    assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
        &old_arm.execution_evidence
    ));
    let mut live_arm = core;
    let live_facts = excluded.facts_for_case(0).unwrap();
    assert!(live_arm.record_proof_case_arm(excluded, 0, live_facts));
    assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
        &live_arm.execution_evidence
    ));
    // New exclusion evidence cannot discharge an old partition's missing arm.
    assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
        &[
            old_arm.execution_evidence[0].clone(),
            live_arm.execution_evidence[0].clone(),
        ]
    ));
}

#[test]
fn constructor_partition_witnesses_avoid_source_facts_and_previous_matches() {
    let (core, value) = constructor_partition_fixture(2);
    let occupied = Variable(4_065_536);
    let root = ProofFacts::from_ordered(&[Proposition::Equal(
        crate::kernel::Term::CValue(CValue::Int32(Bitvector32Term::Variable(occupied))),
        crate::kernel::Term::CValue(int32(0)),
    )]);
    let env = crate::kernel::CExecutionEnvironment::new();
    let (partition, fields, next) = core
        .algebraic_case_partition(&root, &value, &env, &[], None, 4_000_000, 65_536)
        .unwrap();
    assert!(fields.iter().flatten().all(|(var, _)| var.0 > occupied.0));
    let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
    let (_, later, _) = core
        .algebraic_case_partition(&facts, &value, &env, &[], None, next, 65_536)
        .unwrap();
    assert!(later.iter().flatten().all(|(var, _)| var.0 >= next));
    assert!(
        core.algebraic_case_partition(&root, &value, &env, &[], None, u64::MAX, 1)
            .is_none()
    );
    assert!(
        core.algebraic_case_partition(&root, &value, &env, &[], None, 0, 0)
            .is_none()
    );
}

/// A frontier that is not a function entry reserves the region's own entry
/// state and everything the kernel has issued since, so a witness can
/// neither name a value the region started with nor one issued inside it.
#[test]
fn constructor_partition_witnesses_avoid_the_region_state_and_issued_variables() {
    let (_, value) = constructor_partition_fixture(2);
    let occupied = Variable(4_000_000);
    let state =
        CState::new().with_local("cursor", CValue::Int32(Bitvector32Term::Variable(occupied)));
    let core = ExecutionProofCore::at_entry(state, ExecutionFrontier::default());
    let root = ProofFacts::default();
    let env = crate::kernel::CExecutionEnvironment::new();
    let (_, fields, _) = core
        .algebraic_case_partition(&root, &value, &env, &[], None, 4_000_000, 65_536)
        .expect("a loop-body frontier issues its partition");
    assert!(fields.iter().flatten().all(|(var, _)| *var != occupied));

    // `next_kernel_variable` is execution-relative, so an execution that
    // has issued 200_000 identities occupies
    // `1_000_000 .. 1_200_000` and a probe starting inside that range
    // must walk out of it. The field used to be set here as if it were an
    // absolute id, which is how the comparison against it stayed vacuous:
    // the partition's own candidates start at 4_000_000, above every
    // identity an execution can issue.
    let mut issued = core.clone();
    issued
        .advance_kernel_variable_mark(200_000)
        .expect("the counter moves forward");
    assert_eq!(issued.issued_kernel_variable_bound(), 1_200_000);
    let (_, fields, _) = issued
        .algebraic_case_partition(&root, &value, &env, &[], None, 1_000_000, 65_536)
        .expect("a partition skips the issued range");
    assert!(fields.iter().flatten().all(|(var, _)| var.0 >= 1_200_000));
    // The same probe at the range the surface actually uses is unaffected:
    // 4_000_000 is above `KERNEL_VARIABLE_CEILING`, so range separation
    // already covers it and the first candidate is taken.
    let (_, fields, _) = issued
        .algebraic_case_partition(&root, &value, &env, &[], None, 4_065_536, 65_536)
        .expect("a partition above the execution range is unconstrained by it");
    assert!(fields.iter().flatten().any(|(var, _)| var.0 == 4_065_536));
}

/// The counter is the kernel's: it moves forward through
/// [`ExecutionProofCore::advance_kernel_variable_mark`] and a rewind is
/// refused rather than silently re-issuing identities a live value carries.
#[test]
fn an_execution_counter_cannot_be_rewound() {
    let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
    assert_eq!(core.kernel_variable_mark(), 0);
    assert_eq!(
        core.issued_kernel_variable_bound(),
        ExecutionBudget::KERNEL_VARIABLE_BASE
    );
    assert!(core.advance_kernel_variable_mark(12).is_ok());
    assert!(core.advance_kernel_variable_mark(12).is_ok());
    assert!(core.advance_kernel_variable_mark(30).is_ok());
    assert_eq!(
        core.advance_kernel_variable_mark(29),
        Err("an execution's fresh-variable counter cannot move backwards")
    );
    assert_eq!(core.kernel_variable_mark(), 30);
    assert_eq!(
        core.issued_kernel_variable_bound(),
        ExecutionBudget::KERNEL_VARIABLE_BASE + 30
    );
}

#[test]
fn constructor_partition_reserves_algebraic_variables_in_opaque_environment_terms() {
    use crate::kernel::{AlgebraicTermNode, CExecutionEnvironment, PureFunctionArgument};
    let (core, mut value) = constructor_partition_fixture(2);
    value.node = AlgebraicTermNode::Variable(Variable(4_065_536));
    let function = c_function(
        CType::Int32,
        "opaque_environment",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Int32(
            Bitvector32Term::ClickFunctionApplication {
                name: "opaque".into(),
                arguments: vec![PureFunctionArgument::Algebraic(value.clone())],
            },
        ))),
    );
    let environment = CExecutionEnvironment::new().with_function(function);
    value.node = AlgebraicTermNode::Variable(Variable(8));
    let (_, fields, _) = core
        .algebraic_case_partition(
            &ProofFacts::default(),
            &value,
            &environment,
            &[],
            None,
            4_000_000,
            65_536,
        )
        .unwrap();
    assert!(fields.iter().flatten().all(|(var, _)| var.0 > 4_065_536));
}

#[test]
fn constructor_partition_freshness_is_indexed_and_output_linear() {
    for size in [16, 64, 256] {
        let (core, value) = constructor_partition_fixture(2);
        let mut facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|index| Proposition::Predicate {
                    name: format!("ambient{index}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let environment = crate::kernel::CExecutionEnvironment::new();
        let builds = MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get);
        let probes = MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get);
        let mut next = 4_000_000;
        for _ in 0..size {
            let (partition, fields, successor) = core
                .algebraic_case_partition(&facts, &value, &environment, &[], None, next, 65_536)
                .unwrap();
            assert_eq!(fields.iter().map(Vec::len).sum::<usize>(), 2);
            facts = facts.with_fact(partition.case_fact(0).unwrap().clone());
            next = successor;
        }
        assert_eq!(
            MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get) - builds,
            1
        );
        assert_eq!(
            MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get) - probes,
            2 * size + 1
        );
    }
}

#[test]
fn cached_body_loadability_preserves_exact_range_and_snapshot_barriers() {
    let before = CMemory::new();
    let at = |block: &str| Pointer {
        block: block.into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let cached = before.clone().with_seeded_cells(
        at("cache"),
        4,
        crate::kernel::CType::Int32,
        0,
        8,
        crate::kernel::intern_c_memory_ref(&before),
    );
    let view = |memory, pointer, width, wide| Proposition::CMemoryLoadable {
        memory,
        base: pointer,
        bytes: Bitvector32Term::Constant(width),
        wide,
    };
    let allowed = [view(before.clone(), at("body"), 8, false)]
        .into_iter()
        .collect();
    let check = |fact| cached_body_loadability(&fact, &before, &allowed, &mut HashMap::new());
    assert!(check(view(cached.clone(), at("body"), 8, false)));
    assert!(!check(view(cached.clone(), at("body"), 12, false)));
    assert!(!check(view(cached.clone(), at("other"), 8, false)));
    assert!(!check(view(cached.clone(), at("body"), 8, true)));
    assert!(!check(view(
        cached.clone().store(at("body"), int32(7)),
        at("body"),
        8,
        false
    )));
    let havoc =
        cached.with_call_memory_havoc(Variable(901_020), &[], &PureFactContext::new(), None);
    assert!(!check(view(havoc, at("body"), 8, false)));
    assert!(!check(Proposition::CMemoryCanStore {
        memory: before.clone(),
        pointer: at("body"),
        byte_width: 8
    }));
}

#[test]
fn instance_rewrite_refusal_retains_rejected_and_allowed_facts() {
    use crate::kernel::{
        CComparisonOperator, ResourceFieldSchema, ResourceFieldType, ResourceInstance,
        SpecExpression,
    };
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::C(crate::kernel::CType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(901_001),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![],
        None,
        false,
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(7)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
    )
    .with_instance_schema(Some(schema));
    let selected = CResourceFact::own(CResource::Instance(instance.clone()));
    let before = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
    let function = c_function(
        crate::kernel::CType::Int32,
        "refusal",
        vec![],
        CStatement::Return(CExpression::Value(int32(0))),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let (after, allowed) = crate::kernel::rewrite_resource_instance(
        &before,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let supported = allowed
        .iter()
        .cloned()
        .fold(facts.clone(), |facts, fact| facts.with_fact(fact));
    assert!(
        CheckedResourceRewrite::check_with_children_diagnostic(
            &function,
            &before,
            &facts,
            &selected,
            &after,
            &supported,
            &CheckedCallEvents::default(),
            None,
            &[]
        )
        .is_ok()
    );
    let rejected = Proposition::Predicate {
        name: "unsupported_fact".into(),
        arguments: vec![],
    };
    let unsupported = supported.with_fact(rejected.clone());
    let error = CheckedResourceRewrite::check_with_children_diagnostic(
        &function,
        &before,
        &facts,
        &selected,
        &after,
        &unsupported,
        &CheckedCallEvents::default(),
        None,
        &[],
    )
    .err()
    .expect("unsupported facts must still be rejected");
    assert_eq!(
        error.message,
        "instance rewrite introduced an unchecked fact"
    );
    let retained = error
        .rejected_fact
        .expect("the comparison must survive the refusal");
    assert_eq!(retained.rejected, rejected);
    assert!(!retained.allowed.is_empty());
    for fact in allowed {
        assert!(retained.allowed.contains(&fact));
    }
}

fn returned_proposition_trace(
    state: &CState,
    facts: &ProofFacts,
) -> (CFunction, Vec<CheckedExecutionEvent>) {
    let statement = CStatement::Return(CExpression::Value(int32(0)));
    let function = c_function(CType::Int32, "test", vec![], statement.clone());
    let events = vec![
        CheckedExecutionEvent::Statement(Theorem::new(Proposition::CStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state.clone()),
            },
        })),
        CheckedExecutionEvent::Context(facts.assumptions().clone()),
    ];
    (function, events)
}

#[test]
fn return_proof_publication_shares_candidate_fact_and_effect_objects() {
    for size in [4, 64, 1024] {
        let facts: ExecutionFacts = (0..size)
            .map(|index| {
                ExecutionPureFact::new(Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::equal(
                        crate::kernel::Bitvector32Term::Variable(crate::kernel::Variable(index)),
                        crate::kernel::Bitvector32Term::Constant(0),
                    ),
                    false,
                ))
            })
            .collect();
        let state = CState::new();
        let effects: ExecutionFacts = [ExecutionPureFact::certified(
            Proposition::CMemoryMutatesOnly {
                before: state.memory().clone(),
                after: state.memory().clone(),
                writes: vec![],
            },
        )]
        .into();
        let candidate = crate::kernel::CFunctionExecutionCandidate {
            data: Arc::new(crate::kernel::CFunctionExecutionCandidateData {
                outcome: Arc::new(CFunctionOutcome::Return {
                    value: int32(0),
                    state: Box::new(state.clone()),
                }),
                facts: facts.clone(),
                effect_facts: effects.clone(),
                effects_public_first: true,
                obligations: Arc::new(vec![]),
                loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
            }),
        };
        let context = CheckedReturnContext::from_candidate(
            CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state),
            },
            &candidate,
        );
        assert_eq!(context.facts.len(), size as usize + 1);
        for (original, retained) in facts.iter().zip(&context.facts) {
            assert!(std::ptr::eq(original, retained));
        }
        assert!(std::ptr::eq(&effects[0], &context.facts[size as usize]));
        assert!(context.facts[size as usize].is_certified());
        drop(candidate);
        drop(facts);
        drop(effects);
        assert_eq!(context.facts.len(), size as usize + 1);
    }
}

fn returned_proposition_context(state: &CState) -> Arc<CheckedReturnContext> {
    Arc::new(CheckedReturnContext {
        origin: CStatementOutcome::Return {
            value: int32(0),
            state: Box::new(state.clone()),
        },
        published: CFunctionOutcome::Return {
            value: int32(0),
            state: Box::new(state.clone()),
        },
        facts: ExecutionFacts::new(),
    })
}

fn returned_proposition_event(
    context: &Arc<CheckedReturnContext>,
    state: &CState,
    base: &ProofFacts,
    roots: &ProofFacts,
    proposition: Proposition,
) -> CheckedExecutionEvent {
    CheckedExecutionEvent::ReturnProposition(CheckedReturnProposition {
        base: base.clone(),
        context: context.clone(),
        proof: super::super::CheckedProposition::new(
            proposition,
            roots.clone(),
            Some(super::super::OutcomeProofCore {
                identity: super::super::OutcomeIdentity::fresh(),
                result: Arc::new(int32(0)),
                state: state.clone().into(),
                store_consequences_available: false,
                is_exceptional: false,
                effect_facts: Arc::new(ExecutionFacts::new()),
            }),
            None,
        ),
    })
}

#[test]
fn return_proposition_rejects_sibling_assumptions_and_other_memory() {
    let fact = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(42)),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let state = CState::new();
    let empty = ProofFacts::default();
    let sibling = empty.clone().with_fact(fact.clone());
    let (function, original) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    for base in [&empty, &sibling] {
        let mut events = original.clone();
        events.push(returned_proposition_event(
            &context,
            &state,
            base,
            &sibling,
            fact.clone(),
        ));
        assert_eq!(
            trace_completion(&function, &events, empty.assumptions(), false).err(),
            Some("return proof assumes an unjustified path fact")
        );
        let mut refused = None;
        assert_eq!(
            trace_completion_from_entry(
                &function,
                &events,
                empty.assumptions(),
                false,
                None,
                &mut refused,
            )
            .err(),
            Some("return proof assumes an unjustified path fact"),
        );
        assert_eq!(refused.as_ref(), Some(&fact));
    }
    let (function, mut events) = returned_proposition_trace(&state, &sibling);
    let mut other_state = state.clone();
    other_state.memory = CMemory::new().with_block("other_snapshot", 4);
    let other_context = returned_proposition_context(&other_state);
    let wrong_snapshot =
        returned_proposition_event(&other_context, &other_state, &sibling, &sibling, fact);
    let CheckedExecutionEvent::ReturnProposition(retained) = &wrong_snapshot else {
        unreachable!()
    };
    assert!(CheckedReturnProposition::check(retained.proof.clone(), &sibling, context,).is_err());
    events.push(wrong_snapshot);
    assert_eq!(
        trace_completion(&function, &events, sibling.assumptions(), false).err(),
        Some("return proof belongs to a different execution path")
    );
}

#[test]
fn return_proposition_checks_resource_compositions_without_granting_ownership() {
    let state = CState::new();
    let base = ProofFacts::default();
    let context = returned_proposition_context(&state);
    for overlaps in [false, true] {
        let pointer = crate::kernel::Pointer::symbolic(Variable(42));
        let fact =
            Proposition::CResourceComposition(ResourceContext::new().unchecked_with_facts([
                CResourceFact::own_memory(crate::kernel::CMemoryRange::new(
                    pointer.clone(),
                    0.into(),
                    1.into(),
                )),
                CResourceFact::own_memory(crate::kernel::CMemoryRange::new(
                    pointer,
                    if overlaps { 0.into() } else { 1.into() },
                    2.into(),
                )),
            ]));
        let roots = base.clone().with_fact(fact.clone());
        let (function, mut events) = returned_proposition_trace(&state, &base);
        events.push(returned_proposition_event(
            &context, &state, &base, &roots, fact,
        ));
        let result = trace_completion(&function, &events, base.assumptions(), false);
        if overlaps {
            assert_eq!(
                result.err(),
                Some("return proof assumes an unjustified path fact")
            );
        } else {
            let (CStatementOutcome::Return { state: after, .. }, _, _) = result.unwrap() else {
                panic!("expected a returned state");
            };
            assert_eq!(after.resources(), state.resources());
        }
    }
}

#[test]
fn return_proposition_accepts_materialized_reads_without_widening_or_value_facts() {
    let pointer = Pointer::symbolic(Variable(42));
    let memory = CMemory::new().store(pointer.clone(), int32(7));
    let state = CState::new().with_memory(memory.clone());
    let empty = ProofFacts::default();
    let (function, original) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    let read = |memory, base, bytes| Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
    };
    let valid = read(
        memory.clone(),
        pointer.clone(),
        Bitvector32Term::Constant(4),
    );
    let bad_value = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(43)),
            Bitvector32Term::Constant(7),
        ),
        true,
    );
    let cases = [
        (valid, true),
        (
            read(
                memory.clone(),
                pointer.clone(),
                Bitvector32Term::Constant(8),
            ),
            false,
        ),
        (
            read(
                memory.clone(),
                Pointer::symbolic(Variable(44)),
                Bitvector32Term::Constant(4),
            ),
            false,
        ),
        (
            read(
                CMemory::new(),
                pointer.clone(),
                Bitvector32Term::Constant(4),
            ),
            false,
        ),
        (
            read(
                memory.without_local_block(&pointer.block),
                pointer,
                Bitvector32Term::Constant(4),
            ),
            false,
        ),
        (bad_value, false),
    ];
    for (fact, accepted) in cases {
        let roots = empty.clone().with_fact(fact.clone());
        let mut events = original.clone();
        events.push(returned_proposition_event(
            &context, &state, &empty, &roots, fact,
        ));
        let result = trace_completion(&function, &events, empty.assumptions(), false);
        assert_eq!(result.is_ok(), accepted);
        if let Ok((CStatementOutcome::Return { state: after, .. }, _, _)) = result {
            assert_eq!(after.resources(), state.resources());
            assert_eq!(after.memory(), state.memory());
        }
    }
}

/// A certified store's loadability fact names the stored cell's own
/// width, so return certification accepts it as that materialized read.
/// A pointer cell is eight bytes; a four-byte fact over it was refused as
/// an unjustified path fact once a post-return `have` imported it.
#[test]
fn return_proposition_accepts_the_store_loadability_of_a_pointer_cell() {
    let pointer = Pointer::symbolic(Variable(42));
    let value = CValue::pointer(Pointer::symbolic(Variable(43)));
    let memory = CMemory::new().store(pointer.clone(), value.clone());
    let state = CState::new().with_memory(memory.clone());
    let empty = ProofFacts::default();
    let store = crate::kernel::ExecutionPureFact::certified_store(
        CMemory::new(),
        memory,
        pointer,
        value,
        None,
    );
    let [fact]: [Proposition; 1] = crate::kernel::certified_store_loadability_facts(&vec![store])
        .try_into()
        .expect("one loadability fact");
    let (function, mut events) = returned_proposition_trace(&state, &empty);
    let context = returned_proposition_context(&state);
    let roots = empty.clone().with_fact(fact.clone());
    events.push(returned_proposition_event(
        &context, &state, &empty, &roots, fact,
    ));
    assert!(trace_completion(&function, &events, empty.assumptions(), false).is_ok());
}

#[test]
fn return_argument_facts_require_an_ordinary_positive_or_viewed_resource() {
    use crate::kernel::{
        CComparisonOperator, SpecExpression, SpecProposition, c_parameter, c_variable,
    };
    let value = CValue::Int32(Bitvector32Term::Variable(Variable(42)));
    let fact = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::signed_less_equal(
            1.into(),
            Bitvector32Term::Variable(Variable(42)),
        ),
        true,
    );
    let definition = CCompositeResourceDefinition::new(
        "positive",
        vec![c_parameter("n", CType::Int32)],
        None,
        false,
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(1)),
            operator: CComparisonOperator::LessEqual,
            right: SpecExpression::CExpression(c_variable("n")),
        }],
    );
    let owned = CResourceFact::own_composite("positive".into(), vec![value.clone()]);
    let viewed = CResourceFact::view_composite("positive".into(), vec![value]);
    let zero = CResourceFact::Own(owned.resource().clone(), Box::new(0.into()));
    for (resource, authorized, accepted) in [
        (Some(owned.clone()), false, true),
        (Some(viewed), false, true),
        (Some(zero), false, false),
        (None, false, false),
        (Some(owned), true, false),
    ] {
        let resources = resource
            .into_iter()
            .fold(ResourceContext::new(), |r, fact| {
                r.unchecked_with_fact(fact)
            });
        let state = CState::new().with_resource_context(resources);
        let empty = ProofFacts::default();
        let roots = empty.with_fact(fact.clone());
        let (function, mut events) = returned_proposition_trace(&state, &empty);
        let function = function.with_composite_resource_definitions(vec![
            definition.clone().with_authorized(authorized),
        ]);
        let context = returned_proposition_context(&state);
        events.push(returned_proposition_event(
            &context,
            &state,
            &empty,
            &roots,
            fact.clone(),
        ));
        let result = trace_completion(&function, &events, empty.assumptions(), false);
        assert_eq!(result.is_ok(), accepted);
        if let Ok((CStatementOutcome::Return { state: after, .. }, _, _)) = result {
            assert_eq!(after.resources(), state.resources());
        }
    }
}

#[test]
fn return_argument_facts_do_not_project_mutable_memory_invariants() {
    use crate::kernel::{
        CComparisonOperator, CMemorySegment, SpecExpression, SpecProposition, c_index,
        c_int32_literal, c_parameter, c_variable,
    };
    let pointer = Pointer::symbolic(Variable(42));
    let held = CResourceFact::own_composite(
        "cell".into(),
        vec![CValue::typed_pointer(pointer.clone(), CType::Int32Pointer)],
    );
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_index(c_variable("p"), c_int32_literal(0))),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
    );
    assert!(
        crate::kernel::functions::evaluate_composite_resource_fact_propositions(
            &held,
            std::slice::from_ref(&definition),
            &CMemory::new(),
            &ResourceContext::new(),
            &PureFactContext::new().require_owned_expression_loads()
        )
        .is_none()
    );
    let state = CState::new()
        .with_memory(CMemory::new().store(pointer, int32(9)))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
    let empty = ProofFacts::default();
    let false_fact = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::equal(9.into(), 7.into()),
        true,
    );
    let roots = empty.with_fact(false_fact.clone());
    let (function, mut events) = returned_proposition_trace(&state, &empty);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let context = returned_proposition_context(&state);
    events.push(returned_proposition_event(
        &context, &state, &empty, &roots, false_fact,
    ));
    assert!(trace_completion(&function, &events, empty.assumptions(), false).is_err());
}

#[test]
fn return_composite_presentations_reject_other_execution_paths() {
    let before = CState::new();
    let selected = CResourceFact::own_composite("empty".into(), vec![]);
    let after = before
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
    let definition =
        CCompositeResourceDefinition::new("empty", vec![], None, false, vec![], vec![]);
    let (function, events) = returned_proposition_trace(&before, &facts);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let checked = CheckedResourceRewrite::check_with_children(
        &function,
        &before,
        &facts,
        &selected,
        &after,
        &facts,
        &CheckedCallEvents::default(),
        None,
    )
    .unwrap();
    let mut rewrite = checked.clone();
    rewrite.return_presentation = Some(Arc::new(CheckedReturnPresentation {
        context: returned_proposition_context(&before),
        selected,
        rewrite: checked,
    }));
    let check_trace = |rewrite| {
        let mut trace = events.clone();
        trace.push(CheckedExecutionEvent::ResourceRewrite(rewrite));
        trace_completion(&function, &trace, facts.assumptions(), false)
    };
    assert!(check_trace(rewrite.clone()).is_ok());
    Arc::make_mut(rewrite.return_presentation.as_mut().unwrap()).context =
        returned_proposition_context(&before.with_memory(CMemory::new().with_block("other", 4)));
    assert_eq!(
        check_trace(rewrite).err(),
        Some("return composite presentation belongs to a different execution path")
    );
}

#[test]
fn return_resource_observations_reject_extra_facts_and_other_snapshots() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance};
    let schema =
        ResourceFieldSchema::new(vec![("model".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let instance = ResourceInstance::new(
        Variable(1),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new("cell", vec![], None, false, vec![], vec![])
        .with_instance_schema(Some(schema));
    let selected = CResourceFact::own(CResource::Instance(instance.clone()));
    let before = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
    let (after, _) = crate::kernel::rewrite_resource_instance(
        &before,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let (function, events) = returned_proposition_trace(&before, &facts);
    let function = function.with_composite_resource_definitions(vec![definition]);
    let observation = Arc::new(ReturnResourceObservation {
        context: returned_proposition_context(&before),
        before: before.clone(),
        after: after.clone(),
    });
    let check = |after_facts: &ProofFacts, observation| {
        CheckedResourceRewrite::check_with_return_observation(
            &function,
            &before,
            &facts,
            &selected,
            &after,
            after_facts,
            &CheckedCallEvents::default(),
            None,
            Some(observation),
            &[],
        )
    };
    let checked = check(&facts, observation.clone()).unwrap();
    let mut valid = events.clone();
    valid.push(CheckedExecutionEvent::ResourceRewrite(checked.clone()));
    assert!(trace_completion(&function, &valid, facts.assumptions(), false).is_ok());
    for extra in [
        Proposition::CMemoryLoadable {
            memory: before.memory().clone(),
            base: Pointer::symbolic(Variable(42)),
            bytes: 4.into(),
            wide: false,
        },
        Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
    ] {
        assert!(check(&facts.with_fact(extra), observation.clone()).is_err());
    }
    let mut changed = (*observation).clone();
    changed.after.memory = changed
        .after
        .memory()
        .clone()
        .store(Pointer::symbolic(Variable(42)), int32(9));
    assert!(check(&facts, Arc::new(changed)).is_err());
    let mut wrong_path = checked;
    let mut other = before.clone();
    other.memory = CMemory::new().with_block("other", 4);
    Arc::make_mut(wrong_path.return_observation.as_mut().unwrap()).context =
        returned_proposition_context(&other);
    let mut invalid = events;
    invalid.push(CheckedExecutionEvent::ResourceRewrite(wrong_path));
    assert_eq!(
        trace_completion(&function, &invalid, facts.assumptions(), false).err(),
        Some("return resource observation belongs to a different execution path"),
    );
}

#[test]
fn return_instance_guard_and_body_cannot_use_sibling_assumptions() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
        AlgebraicValueType, AlgebraicVariantType, CResourceMatchArm, CResourceMatchBody,
        ConditionTerm, ResourceFieldSchema, ResourceFieldType, ResourceInstance, Term, Variable,
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Left".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Right".into(),
            fields: vec![],
        },
    ]
    .into();
    let ty = AlgebraicType {
        name: "Case".into(),
        arguments: vec![],
        rigid: false,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Case".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(43)),
    };
    let schema = ResourceFieldSchema::new(vec![
        ("value".into(), ResourceFieldType::C(CType::Int32)),
        ("model".into(), ResourceFieldType::Algebraic(ty.clone())),
    ])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(1),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into(), AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let word = Bitvector32Term::Variable(Variable(42));
    let guard = ConditionTerm::equal(word.clone(), Bitvector32Term::Constant(0));
    let condition = SpecProposition::Comparison {
        left: SpecExpression::Value(CValue::Int32(word)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(0)),
    };
    for mode in 0..3 {
        let guarded = mode == 0;
        let matched = mode == 2;
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![],
            guarded.then(|| condition.clone()),
            false,
            vec![],
            if guarded || matched {
                vec![]
            } else {
                vec![condition.clone()]
            },
        )
        .with_instance_schema(Some(schema.clone()))
        .with_resource_match_body(matched.then(|| {
            CResourceMatchBody {
                field_index: 1,
                algebraic_type: ty.clone(),
                arms: ["Left", "Right"]
                    .into_iter()
                    .map(|variant| CResourceMatchArm {
                        children: vec![],
                        variant: variant.into(),
                        bindings: vec![],
                        binding_types: vec![],
                        binding_variables: vec![],
                        contains: vec![],
                        facts: vec![],
                    })
                    .collect(),
            }
        }));
        let selected = CResourceFact::own(CResource::Instance(instance.clone()));
        let before = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let case_fact = |variant: &str| {
            Proposition::Equal(
                Term::Algebraic(model.clone()),
                Term::Algebraic(AlgebraicTerm {
                    algebraic_type: ty.clone(),
                    node: AlgebraicTermNode::Constructor {
                        variant: variant.into(),
                        fields: vec![],
                    },
                }),
            )
        };
        let left = ProofFacts::default().with_fact(if matched {
            case_fact("Left")
        } else {
            Proposition::ConditionIs(guard.clone(), true)
        });
        let right = ProofFacts::default().with_fact(if matched {
            case_fact("Right")
        } else {
            Proposition::ConditionIs(guard.clone(), false)
        });
        let (open, _) = crate::kernel::rewrite_resource_instance(
            &before,
            &instance,
            &definition,
            left.assumptions(),
            true,
        )
        .unwrap();
        let statement = CStatement::Return(CExpression::Value(int32(0)));
        let function = c_function(CType::Int32, "test", vec![], statement.clone())
            .with_composite_resource_definitions(vec![definition]);
        let mut core = ExecutionProofCore::at_entry(before, ExecutionFrontier::default());
        let mut trace = PersistentSequence::default();
        trace.push(CheckedExecutionEvent::Statement(Theorem::new(
            Proposition::CStatementVerifies {
                state: Box::new(open.clone()),
                statement: Box::new(statement),
                outcome: CStatementOutcome::Return {
                    value: int32(0),
                    state: Box::new(open),
                },
            },
        )));
        let (path_facts, rewrite_facts) = if guarded {
            (&left, &right)
        } else {
            (&right, &left)
        };
        trace.push(CheckedExecutionEvent::Context(
            path_facts.assumptions().clone(),
        ));
        core.execution_evidence = vec![trace].into();
        core.evidence_completed = true;
        // Even when both guard arms have identical memory, a rewrite checked
        // under a sibling's case cannot certify this path.
        core.record_return_resource_rewrite(&function, 0, rewrite_facts, &selected, rewrite_facts)
            .unwrap();
        let events = core.return_resource_rewrites.get(&0).unwrap().to_vec();
        let expected = if matched {
            "return fold constructor is not justified on this execution path"
        } else if guarded {
            "return fold guard is not justified on this execution path"
        } else {
            "return fold body is not justified on this execution path"
        };
        assert_eq!(
            trace_completion(&function, &events, path_facts.assumptions(), false).err(),
            Some(expected)
        );
    }
}

fn condition_event(state: &CState, condition: &CExpression, value: bool) -> CheckedExecutionEvent {
    CheckedExecutionEvent::Condition(Theorem::new(Proposition::CConditionEvaluates {
        state: Box::new(state.clone()),
        condition: condition.clone(),
        outcome: CConditionOutcome::Value(value),
    }))
}

#[test]
fn checked_call_event_must_name_a_call_introduced_by_its_statement() {
    let assumptions = PureFactContext::new();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = CMemoryRange::new(
        pointer,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let before = CState::new().with_memory(CMemory::new().with_block("arg-memory", 4));
    let after = before
        .clone()
        .with_memory(before.memory().clone().with_call_memory_havoc(
            crate::kernel::Variable(700),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));
    let theorem = Theorem::new(Proposition::CStatementVerifies {
        state: Box::new(before.clone()),
        statement: Box::new(CStatement::Skip),
        outcome: CStatementOutcome::Normal(Box::new(after)),
    });
    let views = statement_call_havoc_views(&theorem);
    let [view] = views.as_slice() else {
        panic!("expected one checked call view");
    };
    let valid = CheckedCallEvent::new(view.clone());
    assert!(
        validate_checked_event_shapes(&[
            CheckedExecutionEvent::Statement(theorem.clone()),
            CheckedExecutionEvent::Context(PureFactContext::new()),
            CheckedExecutionEvent::Call(valid),
        ])
        .is_ok()
    );

    let unrelated = before.memory().clone().with_call_memory_havoc(
        crate::kernel::Variable(701),
        std::slice::from_ref(&range),
        &assumptions,
        None,
    );
    let unrelated = CheckedCallEvent::new(crate::kernel::intern_c_memory(unrelated));
    assert_eq!(
        validate_checked_event_shapes(&[
            CheckedExecutionEvent::Statement(theorem),
            CheckedExecutionEvent::Context(PureFactContext::new()),
            CheckedExecutionEvent::Call(unrelated),
        ]),
        Err("retained checked-call event is not introduced by its preceding statement")
    );
}

#[test]
fn checked_call_authority_is_path_local_across_forks() {
    let ancestor_view = crate::kernel::intern_c_memory(CMemory::new());
    let sibling_view = crate::kernel::intern_c_memory(
        CMemory::new().with_block_without_derivation("local:sibling", 4),
    );
    let mut ancestor = CheckedCallEvents::default();
    ancestor.new_event(ancestor_view);
    let mut left_arm = ancestor.clone();
    let right_arm = ancestor;
    let left_only = left_arm.new_event(sibling_view.clone());

    assert!(left_arm.contains(&left_only));
    assert!(left_arm.contains_view(&left_only, &sibling_view));
    assert!(
        !right_arm.contains(&left_only),
        "a registry shared for indexing must not make a sibling event active",
    );
}

#[test]
fn checked_call_view_lookup_does_not_scan_unrelated_events() {
    for event_count in [1usize, 64, 1024] {
        let mut events = CheckedCallEvents::new();
        let mut selected = None;
        for index in 0..event_count {
            let view = crate::kernel::intern_c_memory(
                CMemory::new().with_block_without_derivation(format!("local:call-{index}"), 4),
            );
            let event = events.new_event(view.clone());
            if index + 1 == event_count {
                selected = Some((event, view));
            }
        }
        let (selected_event, selected_view) = selected.expect("the corpus is nonempty");
        CheckedCallEvents::reset_lookup_candidates_for_test();
        let found = events.events_for_view(&selected_view);
        assert_eq!(found.len(), 1);
        assert!(found[0].same_authority(&selected_event));
        assert_eq!(
            CheckedCallEvents::lookup_candidates_for_test(),
            1,
            "exact-view lookup should visit only its indexed event at size {event_count}",
        );
    }
}

#[test]
fn interface_pointer_congruence_preserves_scope_and_read_obligations() {
    let a = Pointer::symbolic(Variable(95_700));
    let b = Pointer::symbolic(Variable(95_701));
    let c = Pointer::symbolic(Variable(95_702));
    let equal = |a: Pointer, b: Pointer| {
        Proposition::ConditionIs(crate::kernel::ConditionTerm::pointer_equal(a, b), true)
    };
    let parent = ProofFacts::from_ordered(&[equal(a.clone(), b.clone())]);
    let arm = parent.with_fact(equal(b, c.clone()));
    let goal = equal(a.clone(), c.clone());
    assert!(checked_interface_pointer_equality(&arm, &goal));
    assert!(!checked_interface_pointer_equality(&parent, &goal));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &equal(a.offset_by_bytes(8), c.offset_by_bytes(16))
    ));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &Proposition::And(Box::new(goal.clone()), Box::new(goal))
    ));
    assert!(!checked_interface_pointer_equality(
        &arm,
        &Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: a,
            bytes: Bitvector32Term::Constant(8),
            wide: false,
        }
    ));
}

#[test]
fn entry_interface_materialization_retains_source_and_does_not_rebind() {
    let caller = CState::new();
    let function = c_function(
        CType::Int32,
        "entry_interface",
        vec![crate::kernel::c_parameter("n", CType::Int32)],
        CStatement::Return(crate::kernel::c_variable("n")),
    );
    let arguments = [CExpression::Value(int32(7))];
    let bound = crate::kernel::c_function_entry_state(&caller, &function, &arguments).unwrap();
    let mut core = ExecutionProofCore::at_entry(caller.clone(), ExecutionFrontier::default());
    assert!(core.materialize_function_entry().is_err());
    core.record_checked_function_entry(&function, &arguments, &bound, PureFactContext::new())
        .unwrap();
    let mut unrelated = core.clone();
    unrelated.evidence_state = Some(CState::new().with_local("different", int32(1)));
    assert!(unrelated.materialize_function_entry().is_err());
    core.materialize_function_entry().unwrap();
    assert_eq!(&*core.state, &bound);
    assert_eq!(core.reached_state(), &bound);
    assert_eq!(core.current_source(&function), Some(function.body()));
    assert_eq!(core.frontier.execution_start_state.as_ref(), Some(&caller));
    assert!(core.frontier.is_at_function_entry());
    core.materialize_function_entry().unwrap();
    assert_eq!(&*core.state, &bound);
    assert_eq!(core.reached_state(), &bound);
    assert!(core.execution_evidence.iter().all(|trace| trace.is_empty()));
}

#[test]
fn checked_entry_accepts_only_body_annotations_with_identical_entry_metadata() {
    let returned = CStatement::Return(CExpression::Value(CValue::Void));
    let condition = CExpression::Value(int32(1));
    let function = c_function(
        CType::Void,
        "entry_annotations",
        Vec::new(),
        crate::kernel::api::c_while(condition.clone(), Vec::new(), returned.clone()),
    );
    let caller = CState::new();
    let state = crate::kernel::c_function_entry_state(&caller, &function, &[]).unwrap();
    let entry =
        CheckedFunctionEntry::check(&caller, &function, &[], &state, PureFactContext::new())
            .unwrap();
    let annotated = function.clone().with_body(crate::kernel::api::c_while(
        condition.clone(),
        vec![Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(true),
            true,
        )],
        returned.clone(),
    ));
    assert_ne!(annotated, function);
    assert_eq!(entry.trace_entry_state(&annotated, &[]), Some(&state));
    assert!(
        entry
            .trace_entry_state(&annotated, std::slice::from_ref(&condition))
            .is_none()
    );
    for changed in [
        annotated.clone().with_source_body(returned),
        annotated.clone().with_recursion_measure(vec![
            crate::kernel::CRankingComponent::CExpression(condition),
        ]),
        annotated.with_global_variables(vec![crate::kernel::CGlobal::new(
            "g",
            CType::Int32,
            int32(7),
        )]),
    ] {
        assert!(entry.trace_entry_state(&changed, &[]).is_none());
    }
}

#[test]
fn checked_function_entry_rebase_rejects_semantic_memory_and_population_changes() {
    let function = c_function(
        CType::Void,
        "checked_entry",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![
        CCompositeResourceDefinition::authority_control(
            "item",
            Vec::new(),
            None,
            Vec::new(),
            Vec::new(),
        ),
    ]);
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let caller = CState::new()
        .with_memory(
            CMemory::new().store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1))),
        )
        .with_observed_population_family("item");
    let entry_state = crate::kernel::c_function_entry_state(&caller, &function, &[])
        .expect("the empty argument list should bind");
    let checked = CheckedFunctionEntry::check(
        &caller,
        &function,
        &[],
        &entry_state,
        PureFactContext::new(),
    )
    .expect("the exact kernel-computed entry should check");
    let assumptions = PureFactContext::new();

    assert_eq!(
        checked.entry_state_for(&caller, &function, &[], &assumptions),
        Some(entry_state)
    );

    let changed_memory = caller
        .clone()
        .with_memory(CMemory::new().store(pointer, CValue::Int32(Bitvector32Term::Constant(2))));
    assert!(
        checked
            .entry_state_for(&changed_memory, &function, &[], &assumptions)
            .is_none(),
        "a resource rebase must not authorize a changed C memory value"
    );

    let changed_population = caller.with_observed_population_family("other");
    assert!(
        checked
            .entry_state_for(&changed_population, &function, &[], &assumptions)
            .is_none(),
        "a resource rebase must not authorize a changed population observation"
    );
}

#[test]
fn checked_composite_events_reject_forged_resources_facts_memory_and_definitions() {
    let child_spec = CResourceSpec::token(
        CResourceAccessMode::Own,
        "child".to_string(),
        Vec::new(),
        Vec::new(),
    );
    let definition = CCompositeResourceDefinition::new(
        "bundle",
        Vec::new(),
        None,
        false,
        vec![child_spec],
        Vec::new(),
    );
    let function = c_function(
        CType::Void,
        "resource_events",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = CResourceFact::own_composite("bundle".to_string(), Vec::new());
    let child = CResourceFact::own_token("child".to_string(), Vec::new());
    let child_view = CResourceFact::view_token("child".to_string(), Vec::new());
    let before = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();

    let observed = before.clone().with_resource_context(
        before
            .resources()
            .clone()
            .unchecked_with_supported_facts(&selected, [child_view.clone()]),
    );
    let observation = CheckedResourceObservation::check(
        &function,
        &before,
        &facts,
        &selected,
        &observed,
        &facts,
        &PersistentOrderedSet::default(),
        &CheckedCallEvents::default(),
    )
    .expect("the exact one-layer child view should check");

    let untracked_observation = before.clone().with_resource_context(
        before
            .resources()
            .clone()
            .unchecked_with_fact(child_view.clone()),
    );
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &untracked_observation,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation evidence must retain the owned support relation"
    );

    let forged_resource = observed.clone().with_resource_context(
        observed
            .resources()
            .clone()
            .unchecked_with_fact(CResourceFact::view_token("forged".to_string(), Vec::new())),
    );
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &forged_resource,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not invent an unrelated child view"
    );
    let forged_fact = facts.with_fact(Proposition::ConditionIs(
        crate::kernel::ConditionTerm::Constant(false),
        true,
    ));
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &observed,
            &forged_fact,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not invent an unrelated pure fact"
    );
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let changed_memory = observed
        .clone()
        .with_memory(CMemory::new().store(pointer, CValue::Int32(Bitvector32Term::Constant(1))));
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &changed_memory,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not change C memory"
    );

    let unfolded = before
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(child.clone()));
    CheckedResourceRewrite::check(
        &function,
        &before,
        &facts,
        &selected,
        &unfolded,
        &facts,
        &CheckedCallEvents::default(),
    )
    .expect("the exact folded-to-body representation change should check");
    let variable = Bitvector32Term::Variable(Variable(400));
    let strong = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::signed_greater_than(
            variable.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let weak = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::signed_greater_equal(variable, Bitvector32Term::Constant(0)),
        true,
    );
    let premise = facts.with_fact(strong);
    let derivable_delta = premise.with_fact(weak.clone());
    assert!(premise.assumptions().proves(&weak));
    assert!(!premise.assumptions().proves_exact(&weak));
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &premise,
            &selected,
            &observed,
            &derivable_delta,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "observation must not discover an unrecorded implication"
    );

    let changed_definition = c_function(
        CType::Void,
        "resource_events",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
        "bundle",
        Vec::new(),
        None,
        false,
        Vec::new(),
        Vec::new(),
    )]);
    assert!(
        !changed_definition
            .composite_resource_definitions()
            .contains(
                observation
                    .definition()
                    .expect("legacy body observation has a definition")
            ),
        "a retained observation must remain tied to its checked definition"
    );
}

#[test]
fn checked_join_effects_require_exact_arm_deltas_and_summarize_alternatives() {
    let before = CState::new();
    let left_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let right_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(4),
    };
    let left = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(left_pointer.clone(), crate::kernel::int64(1)),
    );
    let right = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(right_pointer.clone(), int32(2)),
    );
    let left_effect = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
        before: before.memory().clone(),
        after: left.memory().clone(),
        writes: vec![(left_pointer.clone(), 8)],
    });
    let right_effect = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
        before: before.memory().clone(),
        after: right.memory().clone(),
        writes: vec![(right_pointer.clone(), 4)],
    });
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let mut left_core = parent.clone();
    left_core.state = left.clone().into();
    left_core.effect_facts.push(left_effect.clone());
    let mut right_core = parent.clone();
    right_core.state = right.clone().into();
    right_core.effect_facts.push(right_effect.clone());

    assert!(!arm_effect_deltas_are_exact(
        &parent,
        [&left_core, &right_core],
        [&[], &[]],
    ));
    let supplied = [
        std::slice::from_ref(&left_effect),
        std::slice::from_ref(&right_effect),
    ];
    assert!(arm_effect_deltas_are_exact(
        &parent,
        [&left_core, &right_core],
        supplied,
    ));

    let joined = crate::kernel::abstract_c_state_for_interface_join_across(
        &left,
        &[&left, &right],
        &BTreeMap::new(),
        0,
    )
    .expect("alternative memories should have one deterministic abstraction")
    .state;
    let facts = ProofFacts::default();
    let summaries = checked_interface_effect_facts(
        &before,
        &joined,
        [&left_core, &right_core],
        [&facts, &facts],
        supplied,
    )
    .expect("the two exact alternative stores should summarize");
    assert!(matches!(
        summaries.to_vec().as_slice(),
        [fact] if matches!(
            fact.proposition(),
            Proposition::CMemoryMutatesOnly { before: effect_before, after, writes }
                if effect_before == before.memory()
                    && after == joined.memory()
                    && writes == &vec![(left_pointer, 8), (right_pointer, 4)]
        )
    ));
}

#[test]
fn checked_interface_effects_reject_uncertified_memory_effects() {
    let before = CState::new();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = before
        .clone()
        .with_memory(before.memory().clone().store(pointer.clone(), int32(1)));
    let effect = ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
        before: before.memory().clone(),
        after: after.memory().clone(),
        writes: vec![(pointer, 4)],
    });
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let mut changed_core = parent.clone();
    changed_core.state = after.clone().into();
    changed_core.effect_facts.push(effect.clone());

    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&changed_core, &parent],
            [&ProofFacts::default(), &ProofFacts::default()],
            [std::slice::from_ref(&effect), &[]],
        ),
        Err("an interface arm contains an uncertified memory effect")
    );
}

#[test]
fn checked_interface_effects_require_memory_diff_coverage() {
    let before = CState::new();
    let changed_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(4),
    };
    let declared_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = before.clone().with_memory(
        before
            .memory()
            .clone()
            .store(changed_pointer.clone(), int32(1)),
    );
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());

    let mutation = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
        before: before.memory().clone(),
        after: after.memory().clone(),
        writes: vec![(declared_pointer.clone(), 4)],
    });
    let mut mutation_core = parent.clone();
    mutation_core.state = after.clone().into();
    mutation_core.effect_facts.push(mutation.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&mutation_core, &parent],
            [&ProofFacts::default(), &ProofFacts::default()],
            [std::slice::from_ref(&mutation), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );

    let summary = ExecutionPureFact::certified(Proposition::CMemoryEffectSummary {
        before: before.memory().clone(),
        after: after.memory().clone(),
        mutable_ranges: vec![CMemoryRange::new(
            declared_pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });
    let mut summary_core = parent.clone();
    summary_core.state = after.clone().into();
    summary_core.effect_facts.push(summary.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &before,
            &after,
            [&summary_core, &parent],
            [&ProofFacts::default(), &ProofFacts::default()],
            [std::slice::from_ref(&summary), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );

    let erased_before =
        CState::new().with_memory(CMemory::new().store(changed_pointer.clone(), int32(1)));
    let erased_after = erased_before.clone().with_memory(
        erased_before
            .memory()
            .clone()
            .without_cell(&changed_pointer),
    );
    let erased_parent =
        ExecutionProofCore::at_entry(erased_before.clone(), ExecutionFrontier::default());
    let erased_summary = ExecutionPureFact::certified(Proposition::CMemoryEffectSummary {
        before: erased_before.memory().clone(),
        after: erased_after.memory().clone(),
        mutable_ranges: vec![CMemoryRange::new(
            declared_pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });
    let mut erased_core = erased_parent.clone();
    erased_core.state = erased_after.clone().into();
    erased_core.effect_facts.push(erased_summary.clone());
    assert_eq!(
        checked_interface_effect_facts(
            &erased_before,
            &erased_after,
            [&erased_core, &erased_parent],
            [&ProofFacts::default(), &ProofFacts::default()],
            [std::slice::from_ref(&erased_summary), &[]],
        ),
        Err("an interface arm memory effect does not cover its memory diff")
    );
}

#[test]
fn conditional_heap_free_is_checked_as_a_guarded_lifetime_join() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CState::new().with_memory(
        CMemory::new()
            .with_heap_allocation_claim(allocation_base.clone(), 16)
            .expect("the allocation claim should be fresh"),
    );
    let freed = before.clone().with_memory(
        before
            .memory()
            .clone()
            .free_heap_block(&allocation_base, &PureFactContext::new())
            .expect("the freed arm should retire the allocation"),
    );
    let retained = before.clone();
    let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
    let free_effect = ExecutionPureFact::certified(Proposition::CHeapAllocationFreed {
        before: before.memory().clone(),
        after: freed.memory().clone(),
        allocation_base: allocation_base.clone(),
        bytes: Bitvector32Term::Constant(16),
    });
    let mut freed_core = parent.clone();
    freed_core.state = freed.clone().into();
    freed_core.effect_facts.push(free_effect.clone());
    let retained_core = parent.clone();
    let siblings = [&freed, &retained];
    let joined = crate::kernel::abstract_c_state_for_interface_join_across(
        &freed,
        &siblings,
        &BTreeMap::new(),
        0,
    )
    .expect("the conditional heap states should abstract")
    .state;
    let facts = ProofFacts::default();
    let summaries = checked_interface_effect_facts(
        &before,
        &joined,
        [&freed_core, &retained_core],
        [&facts, &facts],
        [std::slice::from_ref(&free_effect), &[]],
    )
    .expect("a conditional free should be checked at the branch boundary");
    assert!(summaries.is_empty());

    let function = c_function(
        CType::Void,
        "conditional_heap_free",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    );
    let free_facts = [
        Vec::new(),
        vec![CResourceFact::own_allocation(allocation_base.clone(), 16)],
    ];
    let states = [&freed, &retained];
    assert!(interface_resources_guard_heap_frees(
        &function,
        &free_facts,
        states,
        [&facts, &facts],
        &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
    ));
    assert!(!interface_resources_guard_heap_frees(
        &function,
        &[Vec::new(), Vec::new()],
        states,
        [&facts, &facts],
        &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
    ));
}

#[test]
fn ground_comparison_premises_check_signed_literals_and_both_polarities() {
    use crate::kernel::ConditionTerm;
    for left in [i32::MIN, -1, 0, 1, i32::MAX] {
        for right in [i32::MIN, -1, 0, 1, i32::MAX] {
            let l = Box::new(Bitvector32Term::Constant(left as u32));
            let r = Box::new(Bitvector32Term::Constant(right as u32));
            for (condition, actual) in [
                (
                    ConditionTerm::Bitvector32SignedLessThan(l.clone(), r.clone()),
                    left < right,
                ),
                (
                    ConditionTerm::Bitvector32SignedLessEqual(l.clone(), r.clone()),
                    left <= right,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterThan(l.clone(), r.clone()),
                    left > right,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterEqual(l.clone(), r.clone()),
                    left >= right,
                ),
                (
                    ConditionTerm::Bitvector32Equal(l.clone(), r.clone()),
                    left == right,
                ),
            ] {
                assert!(ground_comparison_premise_holds(&Proposition::ConditionIs(
                    condition.clone(),
                    actual
                )));
                assert!(!ground_comparison_premise_holds(&Proposition::ConditionIs(
                    condition, !actual
                )));
            }
        }
    }
    // Literal sums canonicalize when constructed; a symbolic operand
    // keeps this an actual compound term at the checking boundary.
    let symbolic_expression = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(crate::kernel::Variable(990))),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    assert!(!ground_comparison_premise_holds(&symbolic_expression));
}

#[test]
fn checked_event_premises_require_exact_facts_or_ground_comparisons() {
    use crate::kernel::{ConditionTerm, Variable};
    let theorem = |premise| {
        Theorem::new(Proposition::Implies(
            Box::new(premise),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            )),
        ))
    };
    let required = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Variable(Variable(991))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let stronger = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterThan(
            Box::new(Bitvector32Term::Variable(Variable(991))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let empty = ProofFacts::default();
    assert!(!checked_evidence_premises_hold(
        &theorem(required.clone()),
        &empty
    ));
    assert!(checked_evidence_premises_hold(
        &theorem(required.clone()),
        &empty.with_fact(required.clone())
    ));
    let derived = empty.with_fact(stronger);
    assert!(
        derived.assumptions().proves(&required),
        "the retired fallback would find this proof"
    );
    assert!(!checked_evidence_premises_hold(
        &theorem(required.clone()),
        &derived
    ));
    let unrelated = empty.with_fact(Proposition::ConditionIs(
        ConditionTerm::Variable(Variable(992)),
        true,
    ));
    assert!(!checked_evidence_premises_hold(
        &theorem(required),
        &unrelated
    ));
    for (left, right, accepted) in [(1, 1, true), (0, 1, false)] {
        let premise = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(Bitvector32Term::Constant(left)),
                Box::new(Bitvector32Term::Constant(right)),
            ),
            true,
        );
        assert_eq!(
            checked_evidence_premises_hold(&theorem(premise), &empty),
            accepted
        );
    }
}

#[test]
fn checked_condition_evidence_preserves_the_tail_for_empty_if_arms() {
    let state = CState::new();
    let condition = CExpression::Variable("x".to_string());
    let branch = CStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(CStatement::Skip),
        else_branch: Box::new(CStatement::Skip),
    };
    let tail = CStatement::Return(CExpression::Variable("x".to_string()));
    let source = prepend_checked_evidence_statement(branch, Some(tail.clone()));

    for value in [true, false] {
        let progress = check_evidence_events(
            &[condition_event(&state, &condition, value)],
            state.clone(),
            Some(source.clone()),
        )
        .expect("a checked empty arm should advance directly to the shared tail");
        assert_eq!(progress.state, state);
        assert_eq!(progress.remaining, Some(tail.clone()));
        assert!(progress.completed.is_none());
    }
}

#[test]
fn checked_condition_evidence_rejects_a_different_source_condition() {
    let state = CState::new();
    let source_condition = CExpression::Variable("x".to_string());
    let theorem_condition = CExpression::Variable("y".to_string());
    let source = CStatement::If {
        condition: source_condition,
        then_branch: Box::new(CStatement::Skip),
        else_branch: Box::new(CStatement::Skip),
    };
    assert!(
        check_evidence_events(
            &[condition_event(&state, &theorem_condition, true)],
            state,
            Some(source),
        )
        .is_none()
    );
}

#[test]
fn a_summarized_loop_matches_only_a_less_annotated_source_loop() {
    fn loop_statement(invariant: Vec<Proposition>, body: CStatement) -> CStatement {
        CStatement::While {
            condition: CExpression::Variable("c".to_string()),
            invariant,
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
            body: Box::new(body),
        }
    }
    let clause = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Constant(0)),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let body = CStatement::Skip;
    let bare = loop_statement(Vec::new(), body.clone());
    let annotated = loop_statement(vec![clause], body.clone());

    // The `loop { ... }` tactic's own clauses may be added to a source
    // loop that carries none: the C program is the same and the theorem
    // discharged more.
    assert!(checked_source_statement_matches(&annotated, &bare));
    assert!(checked_source_statement_matches(&bare, &bare));
    assert!(checked_source_statement_matches(&annotated, &annotated));
    // The reverse would drop an obligation the source asked for.
    assert!(!checked_source_statement_matches(&bare, &annotated));
    // The C itself is still exact.
    assert!(!checked_source_statement_matches(
        &loop_statement(Vec::new(), CStatement::Break),
        &bare
    ));
    let mut other_condition = bare.clone();
    if let CStatement::While { condition, .. } = &mut other_condition {
        *condition = CExpression::Variable("d".to_string());
    }
    assert!(!checked_source_statement_matches(&other_condition, &bare));
    let mut do_while = bare.clone();
    if let CStatement::While { do_while: flag, .. } = &mut do_while {
        *flag = true;
    }
    assert!(!checked_source_statement_matches(&do_while, &bare));
    // Only loops have proof clauses; nothing else relaxes.
    assert!(!checked_source_statement_matches(
        &CStatement::Skip,
        &CStatement::Break
    ));
}

#[test]
fn checked_branch_join_accepts_empty_arms_only_at_the_artifact_tail() {
    let function = c_function(
        CType::Void,
        "branch",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    );
    let state = CState::new();
    let condition = CExpression::Variable("x".to_string());
    let branch_statement = CStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(CStatement::Skip),
        else_branch: Box::new(CStatement::Skip),
    };
    let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
    let then_theorem = match condition_event(&state, &condition, true) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let else_theorem = match condition_event(&state, &condition, false) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let root_facts = ProofFacts::default();
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement,
        continuation,
        condition,
        root_facts: root_facts.clone(),
        paths: vec![
            CheckedBranchPath {
                outcome: CConditionOutcome::Value(true),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: then_theorem.clone(),
            },
            CheckedBranchPath {
                outcome: CConditionOutcome::Value(false),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: else_theorem.clone(),
            },
        ],
    };
    let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let at_branch = FrontierPosition::StatementEntry {
        remaining: Arc::new(crate::kernel::c_seq(
            split.branch_statement.clone(),
            split.continuation.clone().expect("a continuation"),
        )),
    };
    let mut then_arm = parent.clone();
    then_arm.frontier.position = at_branch.clone();
    then_arm
        .record_condition_transition(
            &function,
            &[],
            then_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the then condition decides the frontier's `if`");
    then_arm.frontier.region = ExecutionRegionKind::BranchArm;
    then_arm.frontier.position = FrontierPosition::RegionBoundary;
    let mut else_arm = parent.clone();
    else_arm.frontier.position = at_branch;
    else_arm
        .record_condition_transition(
            &function,
            &[],
            else_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the else condition decides the frontier's `if`");
    else_arm.frontier.region = ExecutionRegionKind::BranchArm;
    else_arm.frontier.position = FrontierPosition::RegionBoundary;

    let checked = CheckedExecutionBranch::check(
        split.clone(),
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        [&[], &[]],
    )
    .expect("the exact empty arms should join at the retained continuation");
    assert_eq!(checked.joined_state(), &state);
    // Each empty arm records its condition theorem and the context it
    // was proved under.
    assert_eq!(checked.arm_events(0).len(), 2);
    assert_eq!(checked.arm_events(1).len(), 2);

    assert!(
        CheckedExecutionBranch::check(
            split,
            &root_facts,
            [&else_theorem, &then_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            [&[], &[]],
        )
        .is_err(),
        "swapped arm evidence must not certify the source partition"
    );
}

#[test]
fn branch_split_obligations_require_evidence_on_each_named_arm() {
    use crate::kernel::{ConditionTerm, ProofObligation};
    let state = CState::new();
    let condition = CExpression::Value(int32(1));
    let x = Bitvector32Term::Variable(Variable(930_000));
    let strong = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let required = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
        true,
    );
    let root = ProofFacts::default().with_fact(strong);
    let theorems = [true, false].map(|value| match condition_event(&state, &condition, value) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    });
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement: CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        },
        continuation: None,
        condition: condition.clone(),
        root_facts: root.clone(),
        paths: [true, false]
            .into_iter()
            .enumerate()
            .map(|(index, value)| CheckedBranchPath {
                outcome: CConditionOutcome::Value(value),
                facts: Vec::new().into(),
                obligations: vec![ProofObligation::new(required.clone())],
                theorem: theorems[index].clone(),
            })
            .collect(),
    };
    let exact = root.with_fact(required);
    let validate = |arms| {
        split.validates_exhaustive_join(
            &state,
            &condition,
            &root,
            [Some(&theorems[0]), Some(&theorems[1])],
            arms,
        )
    };
    assert!(
        !validate([Some(&root), Some(&root)]),
        "general derivability is not retained evidence"
    );
    assert!(
        !validate([Some(&exact), Some(&root)]),
        "then evidence cannot discharge the else obligation"
    );
    assert!(
        !validate([Some(&root), Some(&exact)]),
        "else evidence cannot discharge the then obligation"
    );
    assert!(validate([Some(&exact), Some(&exact)]));
    assert!(
        !validate([Some(&exact), None]),
        "an omitted arm is not exhaustive"
    );
    let unrelated = ProofFacts::default().with_fact(Proposition::ConditionIs(
        ConditionTerm::Constant(true),
        true,
    ));
    assert!(
        !validate([Some(&exact), Some(&unrelated)]),
        "evidence must descend from this split root"
    );
}

#[test]
fn interface_logical_read_does_not_establish_validity() {
    use crate::kernel::{CPointerValue, SpecMemory};
    let state = CState::new();
    let pointer = crate::kernel::Pointer {
        block: "interface_cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
            pointer,
            CType::Int32Pointer,
        )))),
        value_type: CType::Int32,
    };
    let spec = SpecProposition::Comparison {
        left: load.clone(),
        operator: CComparisonOperator::Equal,
        right: load.clone(),
    };
    let path = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
        .unwrap()
        .remove(0);
    assert!(path.facts.is_empty());
    assert!(path.obligations.is_empty());
    let mut facts = ProofFacts::default().with_fact(path.proposition.clone());
    for fact in &path.facts {
        facts = facts.with_fact(fact.proposition().clone());
    }
    assert!(
        CheckedInterfaceLowering::check(
            &SpecProposition::Defined(load),
            &state,
            &state,
            &facts,
            &InterfaceReadPremises::default(),
        )
        .is_none(),
        "logical reflexivity grants no read validity"
    );
    for obligation in &path.obligations {
        facts = facts.with_fact(obligation.proposition().clone());
    }
    let checked = CheckedInterfaceLowering::check(
        &spec,
        &state,
        &state,
        &facts,
        &InterfaceReadPremises::default(),
    )
    .unwrap();
    assert_eq!(checked.path.as_ref(), &path);
    assert!(checked.has_complete_proof());
    assert_eq!(
        checked.proofs.len(),
        1 + path.facts.len() + path.obligations.len()
    );
    assert!(checked.facts.shares_premises_with(&facts));
    assert_eq!(checked.snapshot, state);
    assert_eq!(checked.reference, state);
    assert_eq!(checked.spec.as_ref(), &spec);
    let copy = checked.clone();
    assert!(Arc::ptr_eq(&copy.path, &checked.path));
    assert!(Arc::ptr_eq(&copy.spec, &checked.spec));
    assert!(Arc::ptr_eq(&copy.proofs, &checked.proofs));
    let mut incomplete = checked.clone();
    incomplete.proofs = Arc::new(checked.proofs[..checked.proofs.len() - 1].to_vec());
    assert!(!incomplete.has_complete_proof());
}

#[test]
fn interface_assertion_requires_an_available_proof_not_derivability() {
    use crate::kernel::ConditionTerm;
    let term = Bitvector32Term::Variable(Variable(949_000));
    let state = CState::new().with_local("x", CValue::Int32(term.clone()));
    let spec = SpecProposition::Comparison {
        left: SpecExpression::CExpression(CExpression::Variable("x".into())),
        operator: CComparisonOperator::GreaterEqual,
        right: SpecExpression::Value(int32(0)),
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(term.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let facts = ProofFacts::default().with_fact(Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(term, Bitvector32Term::Constant(0)),
        true,
    ));
    assert!(
        facts.assumptions().proves(&goal),
        "the removed contextual checker could derive this consequence"
    );
    assert!(
        CheckedInterfaceLowering::check(
            &spec,
            &state,
            &state,
            &facts,
            &InterfaceReadPremises::default()
        )
        .is_none()
    );
    let established = facts.with_fact(goal);
    assert!(
        CheckedInterfaceLowering::check(
            &spec,
            &state,
            &state,
            &established,
            &InterfaceReadPremises::default()
        )
        .unwrap()
        .has_complete_proof()
    );
}

#[test]
fn interface_load_definition_rejects_wrong_variable_address_and_snapshot() {
    use crate::kernel::{CMemory, ConditionTerm, Pointer};
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let pointer = Pointer {
        block: "interface_definition".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let variable = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Bits32,
    );
    let equation = |variable, memory, pointer| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::MemoryLoad(
                    memory,
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32,
                )),
            ),
            true,
        )
    };
    let correct = equation(variable, memory.clone(), pointer.clone());
    let definition = CheckedInterfaceLoadDefinition::check(&correct).unwrap();
    assert!(definition.matches_goal_exactly(&correct));
    let wrong_variable = equation(Variable(17), memory.clone(), pointer.clone());
    let wrong_address = equation(
        variable,
        memory,
        Pointer {
            block: "other".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
    );
    let wrong_snapshot = equation(
        variable,
        crate::kernel::intern_c_memory(CMemory::new().with_block("different", 4)),
        pointer,
    );
    for wrong in [wrong_variable, wrong_address, wrong_snapshot] {
        assert!(CheckedInterfaceLoadDefinition::check(&wrong).is_none());
        assert!(!definition.matches_goal_exactly(&wrong));
    }
}

#[test]
fn interface_branch_constructs_resources_and_rejects_unproved_facts() {
    let function = c_function(
        CType::Void,
        "interface",
        Vec::new(),
        CStatement::Return(CExpression::Value(CValue::Void)),
    );
    let state = CState::new()
        .with_local("x", int32(7))
        .with_local("flag", int32(0));
    let condition = CExpression::Variable("flag".to_string());
    let branch_statement = CStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(CStatement::Skip),
        else_branch: Box::new(CStatement::Skip),
    };
    let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
    let then_theorem = match condition_event(&state, &condition, true) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let else_theorem = match condition_event(&state, &condition, false) {
        CheckedExecutionEvent::Condition(theorem) => theorem,
        _ => unreachable!(),
    };
    let root_facts = ProofFacts::default();
    let split = CheckedBranchSplit {
        state: state.clone(),
        branch_statement,
        continuation,
        condition,
        root_facts: root_facts.clone(),
        paths: vec![
            CheckedBranchPath {
                outcome: CConditionOutcome::Value(true),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: then_theorem.clone(),
            },
            CheckedBranchPath {
                outcome: CConditionOutcome::Value(false),
                facts: Vec::new().into(),
                obligations: Vec::new(),
                theorem: else_theorem.clone(),
            },
        ],
    };
    let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let at_branch = FrontierPosition::StatementEntry {
        remaining: Arc::new(crate::kernel::c_seq(
            split.branch_statement.clone(),
            split.continuation.clone().expect("a continuation"),
        )),
    };
    let mut then_arm = parent.clone();
    then_arm.frontier.position = at_branch.clone();
    then_arm
        .record_condition_transition(
            &function,
            &[],
            then_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the then condition decides the frontier's `if`");
    then_arm.frontier.region = ExecutionRegionKind::BranchArm;
    then_arm.frontier.position = FrontierPosition::RegionBoundary;
    let mut else_arm = parent.clone();
    else_arm.frontier.position = at_branch;
    else_arm
        .record_condition_transition(
            &function,
            &[],
            else_theorem.clone(),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("the else condition decides the frontier's `if`");
    else_arm.frontier.region = ExecutionRegionKind::BranchArm;
    else_arm.frontier.position = FrontierPosition::RegionBoundary;
    let stable_join_locals = state
        .locals()
        .object_values()
        .map(|(name, value)| (name.to_string(), value.clone()))
        .collect::<BTreeMap<_, _>>();
    let spec = SpecProposition::Comparison {
        left: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
    };
    let checked_fact = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
        .expect("the simple interface should lower")
        .remove(0)
        .proposition;
    let successor_facts = root_facts.with_fact(checked_fact.clone());

    let checked = CheckedExecutionBranch::construct_interface(
        split.clone(),
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        &stable_join_locals,
        std::slice::from_ref(&spec),
        &[],
        [&[], &[]],
        &state,
        &successor_facts,
        None,
    )
    .expect("the exact fact-only abstraction should check");
    assert_eq!(checked.interface_lowerings.len(), 1);
    let retained = &checked.interface_lowerings[0];
    assert!(retained[0].facts.shares_premises_with(&root_facts));
    assert!(retained[1].facts.shares_premises_with(&root_facts));
    assert!(retained[2].facts.shares_premises_with(&successor_facts));
    assert!(
        retained
            .iter()
            .all(|lowering| lowering.path.proposition == checked_fact)
    );
    assert!(checked.matches_interface_resource_definitions(&function));
    let mut stale = checked.clone();
    stale.interface_successor_facts = Some(successor_facts.with_fact(Proposition::Predicate {
        name: "stale".into(),
        arguments: Vec::new(),
    }));
    assert!(!stale.matches_interface_resource_definitions(&function));
    assert_eq!(
        checked
            .interface_execution_facts()
            .iter()
            .map(ExecutionPureFact::proposition)
            .collect::<Vec<_>>(),
        vec![&checked_fact],
        "only the validated successor delta gains execution-fact authority"
    );

    let forged_fact = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    assert!(
        CheckedExecutionBranch::construct_interface(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            &stable_join_locals,
            std::slice::from_ref(&spec),
            &[],
            [&[], &[]],
            &state,
            &successor_facts.with_fact(forged_fact),
            None,
        )
        .is_err(),
        "an unrelated successor fact must not gain interface authority"
    );

    let forged_resource = CResourceFact::own_token("missing".to_string(), Vec::new());
    let forged_state = state
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(forged_resource));
    let constructed = CheckedExecutionBranch::construct_interface(
        split,
        &root_facts,
        [&then_theorem, &else_theorem],
        [&root_facts, &root_facts],
        &parent,
        [&then_arm, &else_arm],
        &function,
        &[],
        &stable_join_locals,
        std::slice::from_ref(&spec),
        &[],
        [&[], &[]],
        &forged_state,
        &successor_facts,
        None,
    )
    .expect("ownership is derived from the arms, not the proposed state");
    assert!(
        constructed.joined_state.resources().is_empty(),
        "a resource absent from both arms must not gain interface authority"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/tests.rs");
}
