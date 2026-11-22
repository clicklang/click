// Scaling tests of `src/kernel/proof/execution.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn balanced_unit_sum_domain_uses_only_indexed_related_bounds() {
    use crate::kernel::ConditionTerm;
    let a = MachineTerm::Variable(Variable(200));
    let b = MachineTerm::Variable(Variable(201));
    let one = MachineTerm::constant(1);
    let goal = Proposition::condition_is(
        ConditionTerm::signed_add_overflows(
            MachineTerm::add(a.clone(), one.clone()),
            MachineTerm::subtract(b.clone(), one),
        ),
        false,
    );
    let mut measurements = Vec::new();
    for n in [8, 32, 128, 512] {
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
                false,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(a.clone(), MachineTerm::constant(i32::MAX as u32)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(b.clone(), MachineTerm::constant(1)),
                true,
            );
        for i in 0..n {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_equal(
                    MachineTerm::Variable(Variable(1000 + i)),
                    MachineTerm::constant(100),
                ),
                true,
            );
        }
        let (valid, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.settles_exactly(&goal));
        assert!(valid);
        // Removing the old domain must fail without searching the frame.
        let missing_old = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_than(a.clone(), MachineTerm::constant(i32::MAX as u32)),
            true,
        );
        assert!(!missing_old.settles_exactly(&goal));
        measurements.push(work);
    }
    assert!(
        measurements
            .iter()
            .all(|work| *work <= measurements[0] + 16),
        "{measurements:?}"
    );
}

#[test]
fn named_cell_check_rejects_removals_and_ignores_unchanged_cells() {
    use crate::kernel::{Address, AddressBase, AddressOffset, SymbolicMemory};
    let target = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let mut samples = Vec::new();
    for count in [8, 32, 128, 512] {
        let mut before = SymbolicMemory::new();
        for index in 0..count {
            before = before.store(
                Address {
                    base: AddressBase::Heap(index),
                    offset: AddressOffset::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
        }
        let name = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_memory(before.clone()),
            target.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let after = before
            .clone()
            .materialize_named_cell(target.clone(), ProgramValue::Int32(name));
        let before_state = crate::kernel::ExecutionState::new().with_memory(before.clone());
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::memory_only_adds_named_cells(&before_state, &after)
        });
        checked.unwrap();
        samples.push(work);
        let after_state = crate::kernel::ExecutionState::new().with_memory(after);
        assert!(super::super::memory_only_adds_named_cells(&after_state, &before).is_err());
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn constructor_partition_transports_pointer_payloads_without_scanning_ambient_facts() {
    let (core, mut value) = constructor_partition_fixture_with_type(2, ProgramType::Int32Pointer);
    let payload = Address::symbolic(Variable(7_000_000));
    let program = Address::symbolic(Variable(1_000_001));
    value.node = crate::kernel::AlgebraicTermNode::Constructor {
        variant: "C0".into(),
        fields: vec![crate::kernel::AlgebraicValue::Program(
            ProgramValue::typed_pointer(payload.clone(), ProgramType::Int32Pointer),
        )],
    };
    let alias = Proposition::condition_is(
        crate::kernel::ConditionTerm::address_equal(payload.clone(), program.clone()),
        true,
    );
    let env = crate::kernel::ExecutionEnvironment::new();
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut facts = PureFactStore::default().with_fact(alias.clone());
        for index in 0..size {
            facts = facts.with_fact(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            });
        }
        let ((partition, fields, _), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                core.algebraic_case_partition(&facts, &value, &env, &[], None, 0)
                    .unwrap()
            });
        let witness = Address::symbolic(fields[0][0].0);
        let transported = Proposition::condition_is(
            crate::kernel::ConditionTerm::address_equal(program.clone(), witness),
            true,
        );
        assert!(partition.facts_for_case(0).unwrap().available(&transported));
        // The scrutinee is `C0(payload)`, so the `C1` arm is impossible:
        // its two constructors share one class.
        let other = partition.facts_for_case(1).unwrap();
        assert!(other.assumptions().is_inconsistent());
        assert!(!facts.available(&transported));
        let (unrelated, _, _) = core
            .algebraic_case_partition(&PureFactStore::default(), &value, &env, &[], None, 0)
            .unwrap();
        assert!(!unrelated.facts_for_case(0).unwrap().available(&transported));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn concrete_constructor_payload_spelling_is_checked_and_indexed() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
        AlgebraicValueType, AlgebraicVariantType, Term,
    };
    let (core, mut payload) = constructor_partition_fixture(2);
    payload.node = AlgebraicTermNode::Variable(Variable::produced(
        crate::kernel::Producer::AlgebraicBinder,
        1,
    ));
    let inner_key = AlgebraicValueType::Algebraic {
        name: "Cases".into(),
        arguments: vec![],
    };
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Pair".into(),
        fields: vec![inner_key.clone(), inner_key.clone()],
    }]
    .into();
    let mut sibling = payload.clone();
    sibling.node = AlgebraicTermNode::Variable(Variable::produced(
        crate::kernel::Producer::AlgebraicBinder,
        2,
    ));
    let value = AlgebraicTerm {
        algebraic_type: AlgebraicType {
            rigid: false,
            name: "Wrapper".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([
                (inner_key, payload.algebraic_type.variants.clone()),
                (
                    AlgebraicValueType::Algebraic {
                        name: "Wrapper".into(),
                        arguments: vec![],
                    },
                    variants,
                ),
            ]))),
        },
        node: AlgebraicTermNode::Constructor {
            variant: "Pair".into(),
            fields: vec![
                AlgebraicValue::Algebraic(payload.clone()),
                AlgebraicValue::Algebraic(sibling.clone()),
            ],
        },
    };
    assert_eq!(
        crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 0),
        Some(&payload)
    );
    assert_eq!(
        crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 1),
        Some(&sibling)
    );
    assert!(crate::kernel::arm_algebraic_payload_spelling(&value, "Other", 0).is_none());
    assert!(crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 2).is_none());
    assert!(crate::kernel::arm_algebraic_payload_spelling(&payload, "Pair", 0).is_none());
    let environment = crate::kernel::ExecutionEnvironment::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let facts = PureFactStore::from_ordered(
            &(0..size)
                .map(|index| Proposition::Predicate {
                    name: format!("ambient{index}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let ((partition, witnesses, _), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                core.algebraic_case_partition(&facts, &value, &environment, &[], None, 0)
                    .unwrap()
            });
        // Reusing the spelling must not reuse existential witness identities.
        assert!(
            witnesses
                .iter()
                .flatten()
                .all(|(variable, _)| variable.algebraic_binder_index() > Some(2))
        );
        let spelled = Proposition::Equal(
            Term::Algebraic(value.clone().into()),
            Term::Algebraic(value.clone().into()),
        );
        assert!(partition.facts_for_case(0).unwrap().contains(&spelled));
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples[2] <= samples[0] * 2,
        "ambient facts must not cause a scan: {samples:?}"
    );
}

#[test]
fn cached_body_loadability_work_is_linear_in_cache_delta_and_selected_facts() {
    let before = (0..2048).fold(SymbolicMemory::new(), |memory, index| {
        memory.store(
            Address {
                base: "ambient".into(),
                offset: crate::kernel::AddressOffset::Constant(i64::from(index) * 4),
            },
            int32(index),
        )
    });
    for size in [16u32, 32, 64, 128] {
        let cached = (0..size).fold(before.clone(), |memory, index| {
            let source = crate::kernel::intern_memory_ref(&memory);
            memory.with_seeded_cells(
                Address {
                    base: format!("cache-{index}").into(),
                    offset: crate::kernel::AddressOffset::Constant(0),
                },
                4,
                crate::kernel::ProgramType::Int32,
                0,
                2,
                source,
            )
        });
        let view = |memory, index| Proposition::MemoryLoadable {
            memory,
            base: Address {
                base: "body".into(),
                offset: crate::kernel::AddressOffset::Constant(i64::from(index) * 4),
            },
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        };
        let allowed = (0..size).map(|index| view(before.clone(), index)).collect();
        let goals = (0..size)
            .map(|index| view(cached.clone(), index))
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut comparisons = HashMap::new();
            for fact in &goals {
                assert!(cached_body_loadability(
                    fact,
                    &before,
                    &allowed,
                    &mut comparisons
                ));
            }
            assert_eq!(comparisons.len(), 1);
        });
        assert!(work <= 32 * size as usize + 64, "size={size}, work={work}");
    }
}

#[test]
fn return_materialized_reads_scale_with_the_selected_cells() {
    let samples = [16, 32, 64, 128].map(|size| {
        let mut memory = SymbolicMemory::new();
        let pointers: Vec<_> = (0..size).map(|i| Address::symbolic(Variable(i))).collect();
        for pointer in &pointers {
            memory = memory.store(pointer.clone(), int32(7));
        }
        let state = ExecutionState::new().with_memory(memory.clone());
        let mut base = PureFactStore::default();
        let (function, mut events) = returned_proposition_trace(&state, &base);
        let initial = base.clone();
        let context = returned_proposition_context(&state);
        for pointer in pointers {
            let fact = Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: pointer,
                bytes: (MachineTerm::constant(4)).into(),
                wide: false,
            };
            let roots = base.with_fact(fact.clone());
            events.push(returned_proposition_event(
                &context, &state, &base, &roots, fact,
            ));
            base = roots;
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(trace_completion(&function, &events, initial.assumptions(), false).is_ok());
        });
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
        "materialized reads rescanned their context: {samples:?}"
    );
}

#[test]
fn return_proposition_context_validation_scales_with_introductions() {
    let samples = [16, 32, 64, 128].map(|size| {
        let state = ExecutionState::new();
        let mut base = PureFactStore::default();
        let premises: Vec<_> = (0..size)
            .map(|i| {
                Proposition::condition_is(
                    crate::kernel::ConditionTerm::equal(
                        MachineTerm::Variable(Variable(i)),
                        MachineTerm::constant(i as u32),
                    ),
                    true,
                )
            })
            .collect();
        for fact in &premises {
            base = base.with_fact(fact.clone());
        }
        let (function, mut events) = returned_proposition_trace(&state, &base);
        let initial = base.clone();
        let context = returned_proposition_context(&state);
        for fact in premises {
            let goal = Proposition::And(Box::new(fact.clone()), Box::new(fact));
            events.push(returned_proposition_event(
                &context,
                &state,
                &base,
                &base,
                goal.clone(),
            ));
            base = base.with_fact(goal);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(trace_completion(&function, &events, initial.assumptions(), false).is_ok());
        });
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
        "return proofs rescanned their growing ambient contexts: {samples:?}"
    );
}

#[test]
fn return_instance_folds_are_indexed_and_do_not_copy_sibling_traces() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(1)),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![],
        None,
        false,
        vec![crate::kernel::ResourceSpec::owned_memory(
            crate::kernel::MemorySegment {
                uninitialized: false,
                value_runs: Default::default(),
                base: ProgramExpression::Value(ProgramValue::pointer(
                    crate::kernel::Address::symbolic(Variable(100)),
                )),
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                element_width: 4,
                guard: None,
            },
        )],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let statement = ProgramStatement::Return(ProgramExpression::Value(int32(7)));
    let function = program_function(ProgramType::Int32, "test", vec![], statement.clone())
        .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = ResourceFact::own(Resource::Instance(instance.clone()));
    let folded = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();
    let (open, _) = crate::kernel::rewrite_resource_instance(
        &folded,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let trace = |state: ExecutionState| {
        let mut trace = ExecutionEvidence::default();
        trace.push(CheckedExecutionEvent::Statement(Theorem::new(
            Proposition::ProgramStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement.clone()),
                outcome: StatementOutcome::Return {
                    value: int32(7).into(),
                    state: Box::new(state),
                },
            },
        )));
        trace.push(CheckedExecutionEvent::Context(Box::new(
            PureFactContext::new(),
        )));
        trace
    };
    let mut work_samples = Vec::new();
    let mut exchange_samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut core = ExecutionProofCore::at_entry(folded.clone(), ExecutionFrontier::default());
        core.execution_evidence = (0..size)
            .map(|index| {
                // A sibling lacks the body ownership. Its state cannot be used
                // to satisfy this path's fold, or vice versa.
                trace(if index == size - 1 {
                    ExecutionState::new()
                } else {
                    open.clone()
                })
            })
            .collect::<Vec<_>>()
            .into();
        core.evidence_completed = true;
        core.return_proof_contexts = core.return_proof_contexts.with_inserted(
            size / 2,
            Arc::new(CheckedReturnContext {
                origin: StatementOutcome::Return {
                    value: int32(7).into(),
                    state: Box::new(open.clone()),
                },
                published: FunctionOutcome::Return {
                    value: int32(7).into(),
                    state: Box::new(open.clone()),
                },
                facts: ExecutionFacts::new(),
            }),
        );
        let base = core.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            core.rewrite_return_resource_instance_with_children(
                &function,
                size / 2,
                &facts,
                &instance,
                false,
                None,
            )
            .unwrap();
        });
        work_samples.push(work);
        for index in 0..size {
            assert!(
                core.execution_evidence[index].shares_tail_with(&base.execution_evidence[index])
            );
            assert_eq!(
                core.return_resource_rewrites.get(&index).is_some(),
                index == size / 2
            );
        }
        assert!(
            core.record_return_resource_rewrite(&function, size - 1, &facts, &selected, &facts)
                .is_err()
        );
        assert!(
            core.record_return_resource_rewrite(&function, size, &facts, &selected, &facts)
                .is_err()
        );
        assert!(
            core.record_return_resource_rewrite(&function, size / 2, &facts, &selected, &facts)
                .is_err()
        );
        let events = core
            .return_resource_rewrites
            .get(&(size / 2))
            .unwrap()
            .to_vec();
        let (outcome, _, _) =
            trace_completion(&function, &events, facts.assumptions(), false).unwrap();
        // The fold publishes read authority for the cells it consumed;
        // apart from that observation the state is the folded one.
        let StatementOutcome::Return { value, state } = outcome else {
            panic!("the completion returns");
        };
        assert_eq!(*value.native(), int32(7));
        let resources = state
            .resources()
            .clone()
            .without_owned_instance_read_views();
        assert_eq!(state.with_resource_context(resources), folded);
        // Copying an event to a different path with a different body
        // state is rejected when completing the execution proof.
        let mut forged = base.execution_evidence[size - 1].clone();
        forged.push(events.last().unwrap().clone());
        assert!(trace_completion(&function, &forged.to_vec(), facts.assumptions(), false).is_err());
        let mut collected = base.clone();
        collected
            .collect_return_resource_rewrites(&core, size / 2)
            .unwrap();
        let extra = Proposition::condition_is(
            crate::kernel::ConditionTerm::equal(
                MachineTerm::Variable(Variable(1000)),
                MachineTerm::constant(9),
            ),
            true,
        );
        let state_facts = facts.with_fact(extra.clone());
        let mut retained_state = base.clone();
        retained_state
            .record_return_resource_rewrite(&function, 0, &state_facts, &selected, &state_facts)
            .unwrap();
        let (_, retained, _) = trace_completion(
            &function,
            &retained_state
                .return_resource_rewrites
                .get(&0)
                .unwrap()
                .to_vec(),
            facts.assumptions(),
            false,
        )
        .unwrap();
        assert!(
            !crate::kernel::search::ProofSearch::proves(&(retained), &extra),
            "a fold must not publish unrelated state assumptions"
        );
        let mut repeated = base.clone();
        let mut repeated_facts = facts.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                for unfold in [false, true] {
                    let (_, next_facts) = repeated
                        .rewrite_return_resource_instance_with_children(
                            &function,
                            size / 2,
                            &repeated_facts,
                            &instance,
                            unfold,
                            None,
                        )
                        .unwrap();
                    repeated_facts = next_facts;
                }
            }
        });
        exchange_samples.push(work);
        let mut unrelated = base;
        unrelated.execution_evidence[size / 2] = trace(open.clone());
        assert!(
            unrelated
                .collect_return_resource_rewrites(&core, size / 2)
                .is_err()
        );
    }
    for pair in work_samples.windows(2) {
        assert!(
            pair[1] <= pair[0] + 128,
            "path-local fold work: {work_samples:?}"
        );
    }
    for pair in exchange_samples.windows(2) {
        assert!(
            pair[1] <= 2 * pair[0] + 128,
            "return exchanges revisited their history: {exchange_samples:?}"
        );
    }
}

#[test]
fn instance_rewrite_certificate_rejects_unrelated_state_and_fact_changes() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        InstanceId::from_variable(Variable(1)),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new("cell", vec![], None, false, vec![], vec![])
        .with_instance_schema(Some(schema));
    let function = program_function(
        ProgramType::Void,
        "test",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = ResourceFact::own(Resource::Instance(instance.clone()));
    let before = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = PureFactStore::default();
    let (opened, _) = crate::kernel::rewrite_resource_instance(
        &before,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let calls = CheckedCallEvents::default();
    CheckedResourceRewrite::check(
        &function, &before, &facts, &selected, &opened, &facts, &calls,
    )
    .unwrap();
    let forged = opened.clone().with_resource_context(
        opened
            .resources()
            .clone()
            .unchecked_with_fact(ResourceFact::own_token("forged".into(), vec![])),
    );
    assert!(
        CheckedResourceRewrite::check(
            &function, &before, &facts, &selected, &forged, &facts, &calls
        )
        .is_err()
    );
    let forged = opened
        .clone()
        .with_memory(SymbolicMemory::new().with_block("invented", 4));
    assert!(
        CheckedResourceRewrite::check(
            &function, &before, &facts, &selected, &forged, &facts, &calls
        )
        .is_err()
    );
    let mut forged = opened.clone();
    forged.instance_field_scope = ResourceContext::new().unchecked_with_fact(selected.clone());
    assert!(
        CheckedResourceRewrite::check(
            &function, &before, &facts, &selected, &forged, &facts, &calls,
        )
        .is_err(),
        "a rewrite cannot retain scratch field bindings as a handle"
    );
    let forged_facts = facts.with_fact(Proposition::condition_is(
        crate::kernel::ConditionTerm::Constant(false),
        true,
    ));
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &before,
            &facts,
            &selected,
            &opened,
            &forged_facts,
            &calls
        )
        .is_err()
    );
    let (closed, _) = crate::kernel::rewrite_resource_instance(
        &opened,
        &instance,
        &definition,
        facts.assumptions(),
        false,
    )
    .unwrap();
    CheckedResourceRewrite::check(
        &function, &opened, &facts, &selected, &closed, &facts, &calls,
    )
    .unwrap();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = before.clone();
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = InstanceId::from_variable(Variable(identity));
            state.resources = state
                .resources
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (open, _) = crate::kernel::rewrite_resource_instance(
                &state,
                &instance,
                &definition,
                facts.assumptions(),
                true,
            )
            .unwrap();
            CheckedResourceRewrite::check(
                &function, &state, &facts, &selected, &open, &facts, &calls,
            )
            .unwrap();
            let (closed, _) = crate::kernel::rewrite_resource_instance(
                &open,
                &instance,
                &definition,
                facts.assumptions(),
                false,
            )
            .unwrap();
            CheckedResourceRewrite::check(
                &function, &open, &facts, &selected, &closed, &facts, &calls,
            )
            .unwrap();
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] + 256,
            "certificate must inspect only its exchange: {samples:?}"
        );
    }
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &ExecutionState::new(),
            &facts,
            &selected,
            &before,
            &facts,
            &calls
        )
        .is_err()
    );
}

#[test]
fn interface_abstraction_work_scales_with_unrelated_locals_and_memory() {
    let mut samples = Vec::new();
    for size in [64_u32, 128, 256, 512] {
        let mut memory = SymbolicMemory::new();
        let mut then_state = ExecutionState::new().with_local("changed", int32(1));
        let mut stable_locals = BTreeMap::new();
        for index in 0..size {
            let name = format!("stable_{index}");
            let value = int32(index);
            then_state = then_state.with_local(name.clone(), value.clone());
            stable_locals.insert(name, value);
            memory = memory.store(
                Address {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::Constant(i64::from(index * 4)),
                },
                int32(index),
            );
        }
        then_state = then_state.with_memory(memory);
        let else_state = then_state.clone().with_local("changed", int32(2));
        let siblings = [&then_state, &else_state];
        let ((then_join, else_join), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (
                    crate::kernel::abstract_execution_state_for_interface_join_across(
                        &then_state,
                        &siblings,
                        0,
                    )
                    .expect("the then arm should abstract"),
                    crate::kernel::abstract_execution_state_for_interface_join_across(
                        &else_state,
                        &siblings,
                        0,
                    )
                    .expect("the else arm should abstract"),
                )
            });
        assert_eq!(then_join, else_join);
        samples.push((size, work));
    }
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "interface abstraction work grew superlinearly: {samples:?}"
        );
    }
}

#[test]
fn branch_fact_availability_is_exact_and_independent_of_ambient_history() {
    use crate::kernel::ConditionTerm;
    let x = MachineTerm::Variable(Variable(910_000));
    let strong = Proposition::condition_is(
        ConditionTerm::signed_greater_than(x.clone(), MachineTerm::constant(0)),
        true,
    );
    let weak = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0)),
        true,
    );
    let reflexive = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(x.clone()),
            right: Box::new(x),
        },
        true,
    );
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut facts = PureFactStore::default().with_fact(strong.clone());
        for index in 0..size {
            facts = facts.with_fact(Proposition::condition_is(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(920_000 + index)),
                    MachineTerm::constant(100),
                ),
                true,
            ));
        }
        assert!(
            crate::kernel::search::ProofSearch::proves(facts.assumptions(), &weak),
            "the old general route could derive this missing fact"
        );
        let exact = facts.with_fact(weak.clone());
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!checked_branch_fact_is_available(&facts, &weak));
            assert!(checked_branch_fact_is_available(&exact, &weak));
            assert!(checked_branch_fact_is_available(&facts, &reflexive));
            assert!(!checked_branch_fact_is_available(
                &facts,
                &Proposition::Not(Box::new(reflexive.clone()))
            ));
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "branch availability scanned unrelated history: {samples:?}"
    );
}

// Interface re-lowering must use the checked arm's address aliases without
// acquiring read authority, leaking an arm fact, or scanning its history.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn interface_aliased_wide_read_preserves_scope_history_and_scales() {
    use crate::kernel::{ConditionTerm, Pointer, SpecPoint};
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Address::symbolic(Variable(951_000));
    let alias = Address::symbolic(Variable(951_001));
    let value = MachineTerm::uint64_constant(0x1234_5678_9abc_def0);
    let load = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(Pointer::new(
            alias.clone(),
            ProgramType::UInt64Pointer,
        )))),
        value_type: ProgramType::UInt64,
        exact: false,
    };
    let spec = SpecProposition::Comparison {
        left: load.clone(),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(ProgramValue::UInt64(value.clone())),
    };
    let mut previous = None;
    for count in [16_u32, 64, 256, 1024] {
        let mut memory = SymbolicMemory::new();
        let mut parent = PureFactStore::default();
        for index in 0..count {
            memory = memory.store(owner.offset_by_bytes((index + 1) * 8), int32(index));
            parent = parent.with_fact(Proposition::condition_is(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(952_000 + u64::from(index))),
                    MachineTerm::constant(index),
                ),
                true,
            ));
        }
        memory = memory.store(owner.clone(), ProgramValue::UInt64(value.clone()));
        let state = ExecutionState::new().with_memory(memory.clone());
        let arm = parent.with_fact(Proposition::condition_is(
            ConditionTerm::address_equal(alias.clone(), owner.clone()),
            true,
        ));
        let check = |state: &ExecutionState, facts: &PureFactStore, spec: &SpecProposition| {
            CheckedInterfaceLowering::check(
                spec,
                state,
                state,
                facts,
                &InterfaceReadPremises::default(),
            )
        };
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(&state, &arm, &spec));
        assert!(checked.is_some(), "{count} unrelated cells and premises");
        assert!(checked.unwrap().has_complete_proof());
        if let Some(previous) = previous {
            assert!(work <= previous + 128, "{count}: {work} after {previous}");
        }
        previous = Some(work);
        assert!(
            check(&state, &parent, &spec).is_none(),
            "alias stays in its arm"
        );
        assert!(
            check(&state, &arm, &SpecProposition::Defined(load.clone())).is_none(),
            "logical value evidence does not authorize a C read"
        );
        for (offset, overwrite) in [
            (0, ProgramValue::UInt64(MachineTerm::uint64_constant(7))),
            (4, int32(7)),
        ] {
            let address = owner.offset_by_bytes(offset);
            let changed = memory
                .without_possible_aliasing_cells(
                    &address,
                    overwrite.byte_width(),
                    arm.assumptions(),
                )
                .store(address, overwrite);
            assert!(
                check(&state.clone().with_memory(changed), &arm, &spec).is_none(),
                "a full or partial overwrite invalidates the old value"
            );
        }
    }
}

#[test]
fn interface_read_premises_are_indexed_and_check_the_exact_range() {
    use crate::kernel::{Address, SymbolicMemory};
    let memory = SymbolicMemory::new();
    let readable = |memory: SymbolicMemory, block: String, width| Proposition::MemoryLoadable {
        memory,
        base: Address {
            base: block.into(),
            offset: AddressOffset::Constant(0),
        },
        bytes: (MachineTerm::constant(width)).into(),
        wide: false,
    };
    let goal = readable(memory.clone(), "selected".into(), 4);
    let source = readable(memory.clone(), "selected".into(), 8);
    let samples = [16, 32, 64, 128].map(|size| {
        let inputs = (0..size)
            .map(|i| readable(memory.clone(), format!("unrelated_{i}"), 8))
            .chain(std::iter::once(source.clone()))
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let index = InterfaceReadPremises::new(inputs);
            let selected = index.for_goal(&goal).unwrap();
            assert_eq!(selected, &source);
            assert!(interface_read_is_subrange(&goal, selected));
            assert!(!interface_read_is_subrange(
                &readable(memory.clone(), "selected".into(), 9),
                selected
            ));
            assert!(!interface_read_is_subrange(
                &readable(memory.clone(), "other".into(), 4),
                selected
            ));
            assert!(!interface_read_is_subrange(
                &readable(
                    SymbolicMemory::new().with_block("other", 4),
                    "selected".into(),
                    4
                ),
                selected
            ));
        });
        work
    });
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "explicit resource index scaled superlinearly: {samples:?}"
    );
    assert!(InterfaceReadPremises::default().for_goal(&goal).is_none());
}

#[test]
fn interface_lowering_retention_shares_unrelated_history() {
    let spec = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(1)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let samples = [16, 32, 64, 128].map(|size| {
        let mut facts = PureFactStore::default();
        let mut state = ExecutionState::new();
        for index in 0..size {
            facts = facts.with_fact(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: Vec::new(),
            });
            state = state.with_local(format!("unrelated_{index}"), int32(index));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let checked = CheckedInterfaceLowering::check(
                &spec,
                &state,
                &state,
                &facts,
                &InterfaceReadPremises::default(),
            )
            .unwrap();
            let copy = checked.clone();
            assert!(copy.facts.shares_premises_with(&facts));
            assert_eq!(copy.retained_state, state);
            assert_eq!(copy.reference, state);
            assert!(Arc::ptr_eq(&copy.path, &checked.path));
        });
        work
    });
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "retention scanned unrelated history: {samples:?}"
    );
}

/// A fold publishes the resource exchange and its evidence in the operation
/// that derives it. Recording must not lower the same written clauses again.
#[test]
fn constructing_an_instance_fold_pays_for_its_body_once() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance};
    let mut samples = Vec::new();
    for size in [4u32, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let schema = ResourceFieldSchema::new(vec![(
            "tag".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        let instance = ResourceInstance::new(
            InstanceId::from_variable(Variable(995_800)),
            "cell".into(),
            vec![].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap();
        let clauses = (0..size)
            .map(|index| crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::ProgramExpression(ProgramExpression::Value(
                    int32(index),
                )),
                operator: crate::kernel::ComparisonOperator::Equal,
                right: crate::kernel::SpecExpression::ProgramExpression(ProgramExpression::Value(
                    int32(index),
                )),
            })
            .collect();
        let definition =
            CompositeResourceDefinition::new("cell", vec![], None, false, vec![], clauses)
                .with_instance_schema(Some(schema));
        let function = program_function(
            ProgramType::Void,
            "test",
            vec![],
            ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let before = ExecutionState::new();
        let facts = PureFactStore::default();
        let (_, direct) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &before,
                &instance,
                &definition,
                function.composite_resource_definitions(),
                facts.assumptions(),
                false,
                None,
            )
            .unwrap()
        });
        let (folded, total) = crate::instrumentation::measure_deterministic_work(|| {
            let mut core =
                ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
            let (result, _) = core
                .fold_resource_instance_with_children(&function, &[], &facts, &instance, None)
                .unwrap();
            result
        });
        assert!(
            folded
                .state
                .resources()
                .owned_instance(instance.identity())
                .is_some()
        );
        samples.push((direct, total));
    }
    assert!(
        samples.iter().all(|(direct, total)| *total <= direct + 128),
        "[direct derivation, construction and recording]: {samples:?}"
    );
}

#[test]
fn an_interface_owned_export_normalizes_only_its_neighbors() {
    use crate::kernel::{MemorySegment, program_expression::int32_literal};

    use crate::kernel::primitives::take_whole_normalization_facts;

    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = ProgramExpression::Value(ProgramValue::typed_pointer(
            Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Constant(0),
            },
            ProgramType::Int32Pointer,
        ));
        let spec_at = |start, end| {
            ResourceSpec::owned_memory(MemorySegment::new(
                pointer.clone(),
                int32_literal(start),
                int32_literal(end),
            ))
        };
        let facts = PureFactStore::default();
        let state = ExecutionState::new();
        let fact_at = |start, end| {
            evaluate_interface_resource_spec(&spec_at(start, end), &state, &facts)
                .expect("the footprint lowers")
        };
        let exported = fact_at(0, 1);
        let adjacent = fact_at(1, 2);
        let merged = fact_at(0, 2);
        let frame = (0..count)
            .map(|index| fact_at(4 + 2 * index, 5 + 2 * index))
            .collect::<Vec<_>>();
        let resources = ResourceContext::new_with_equalities(facts.assumptions())
            .unchecked_with_facts(frame.iter().cloned().chain([exported, adjacent]));
        let parent = ExecutionProofCore::at_entry(
            state.clone().with_resource_context(resources.clone()),
            ExecutionFrontier::default(),
        );
        take_whole_normalization_facts();
        let (joined, work) = crate::instrumentation::measure_deterministic_work(|| {
            interface_join_resources(
                &parent,
                [&parent, &parent],
                [&facts, &facts],
                &[spec_at(0, 1)],
                &state,
                &facts,
            )
        });
        assert_eq!(take_whole_normalization_facts(), 0);
        let successor = joined
            .expect("both arms supply the export")
            .expected_resources;
        assert_eq!(successor.fact_count(), frame.len() + 1);
        assert!(successor.contains_exact_representation(&merged));
        for fact in &frame {
            assert_eq!(
                successor.owned_occurrences_for_fact(fact),
                resources.owned_occurrences_for_fact(fact)
            );
        }
        samples.push(work);
    }
    // Allow the indexed lookups to cost a little more in a deeper tree.
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "one export did too much work beside the disjoint frame: {samples:?}"
    );
}

#[test]
fn an_interface_view_check_ignores_unrelated_owned_ranges() {
    use crate::kernel::primitives::take_whole_normalization_facts;
    use crate::kernel::{MemorySegment, program_expression::int32_literal};

    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = ProgramExpression::Value(ProgramValue::typed_pointer(
            Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Constant(0),
            },
            ProgramType::Int32Pointer,
        ));
        let segment = |start, end| {
            MemorySegment::new(pointer.clone(), int32_literal(start), int32_literal(end))
        };
        let facts = PureFactStore::default();
        let state = ExecutionState::new();
        let evaluate = |spec: ResourceSpec| {
            evaluate_interface_resource_spec(&spec, &state, &facts).expect("the range lowers")
        };
        let held = evaluate(ResourceSpec::owned_memory(segment(0, 2)));
        let view = evaluate(ResourceSpec::viewed_memory(segment(2, 3)));
        let frame = (0..count).map(|index| {
            evaluate(ResourceSpec::owned_memory(segment(
                4 + 2 * index,
                5 + 2 * index,
            )))
        });
        let resources = ResourceContext::new_with_equalities(facts.assumptions())
            .unchecked_with_facts([held, view].into_iter().chain(frame));
        let parent = ExecutionProofCore::at_entry(
            state.clone().with_resource_context(resources.clone()),
            ExecutionFrontier::default(),
        );
        // An exact held view, a subrange of an owner, and an unheld gap.
        for (start, end, exists) in [(2, 3, true), (1, 2, true), (3, 4, false)] {
            take_whole_normalization_facts();
            let spec = ResourceSpec::viewed_memory(segment(start, end));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                interface_join_resources(
                    &parent,
                    [&parent, &parent],
                    [&facts, &facts],
                    &[spec],
                    &state,
                    &facts,
                )
            });
            assert_eq!(take_whole_normalization_facts(), 0);
            if exists {
                let successor = result
                    .expect("the view is already available")
                    .expected_resources;
                assert!(successor.shares_storage_with(&resources));
            } else {
                assert_eq!(
                    result.err(),
                    Some("an interface resource is not owned by one concrete arm")
                );
            }
            samples.push(work);
        }
    }
    for (index, work) in samples.iter().enumerate() {
        assert!(
            *work <= samples[index % 3] + 32,
            "view checking visited the disjoint frame: {samples:?}"
        );
    }
}

#[test]
fn a_checked_interface_join_does_not_reconstruct_a_calls_havoc() {
    let mut samples = Vec::new();
    for count in [4u32, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let mut memory = SymbolicMemory::new();
        for index in 0..count {
            memory = memory.store(base.offset_by_bytes(index * 4), int32(index));
        }
        let range =
            crate::kernel::MemoryRange::new_with_element_width(base, 0u32.into(), count.into(), 4);
        let assumptions = PureFactContext::new();
        let after = memory.clone().with_call_memory_havoc(
            Variable(9_940_000),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        );
        let before_state = ExecutionState::new().with_memory(memory.clone());
        let after_state = before_state.clone().with_memory(after.clone());
        let parent =
            ExecutionProofCore::at_entry(before_state.clone(), ExecutionFrontier::default());
        let effect = ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
            before: memory.clone(),
            after: after.clone(),
            mutable_ranges: vec![range.clone()],
        })
        .into_certified();
        let mut called = parent.clone();
        called.state = after_state.clone().into();
        called.effect_facts.push(effect);
        // The statement recorder retains exactly one effect for this call.
        // Its checked walk is the join's record of the effect stream.
        let steps = [CheckedMemoryStep {
            before: memory,
            after,
            may_write: true,
            statement_effects: Some(1),
        }];
        let (joined, work) = crate::instrumentation::measure_deterministic_work(|| {
            checked_interface_effect_facts_along(
                &before_state,
                &after_state,
                [&called, &parent],
                [&PureFactStore::default(), &PureFactStore::default()],
                [&called.effect_facts, &parent.effect_facts],
                Some([&steps, &[]]),
            )
        });
        let joined = joined.unwrap();
        assert!(joined.iter().any(|fact| fact.is_join_summary() && matches!(fact.proposition(), Proposition::MemoryEffectSummary { mutable_ranges, .. } if mutable_ranges == std::slice::from_ref(&range))));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "the join reconstructed the already checked call's havoc: {samples:?}"
    );
}

#[test]
fn taking_a_constructor_arm_reuses_its_constructed_fact_context() {
    let mut samples = Vec::new();
    for count in [4u64, 8, 16, 32] {
        let (core, mut value) = constructor_partition_fixture(2);
        value.node = crate::kernel::AlgebraicTermNode::Constructor {
            variant: "C0".into(),
            fields: vec![crate::kernel::AlgebraicValue::Program(ProgramValue::Int32(
                MachineTerm::ClickFunctionApplication {
                    name: "opaque_payload".into(),
                    arguments: (0..count)
                        .map(|i| {
                            crate::kernel::PureFunctionArgument::Value(ProgramValue::Int32(
                                MachineTerm::Variable(Variable(8_100_000 + i)),
                            ))
                        })
                        .collect(),
                },
            ))],
        };
        let root = PureFactStore::default();
        let (partition, _, _) = core
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::ExecutionEnvironment::new(),
                &[],
                None,
                0,
            )
            .unwrap();
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            partition.facts_for_case(0).unwrap()
        });
        assert!(facts.contains(partition.case_fact(0).unwrap()));
        assert!(!root.contains(partition.case_fact(0).unwrap()));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "entering an already constructed arm rebuilt its payload facts: {samples:?}"
    );
}

#[test]
fn constructed_composite_observation_preserves_the_owner_beside_growing_frames() {
    let definition = CompositeResourceDefinition::new(
        "bundle",
        Vec::new(),
        None,
        false,
        vec![ResourceSpec::token(
            ResourceAccessMode::Own,
            "child".to_string(),
            Vec::new(),
            Vec::new(),
        )],
        Vec::new(),
    );
    let function = program_function(
        ProgramType::Void,
        "observe_bundle",
        vec![],
        ProgramStatement::Skip,
    )
    .with_composite_resource_definitions(vec![definition]);
    let selected = ResourceFact::own_composite("bundle".to_string(), Vec::new());
    let child = ResourceFact::view_token("child".to_string(), Vec::new());
    for related in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut frame = ResourceContext::new().unchecked_with_fact(selected.clone());
            for index in 0..count {
                let base = crate::kernel::Address::symbolic(Variable(
                    9_832_000 + if related { 0 } else { u64::from(index) },
                ));
                frame = frame.unchecked_with_fact(ResourceFact::own_memory(
                    MemoryRange::new_with_element_width(
                        base,
                        (index * 4).into(),
                        (index * 4 + 1).into(),
                        1,
                    ),
                ));
            }
            let support = frame.unique_owned_occurrence_for_fact(&selected).unwrap().0;
            let before = ExecutionState::new().with_resource_context(frame);
            let facts = PureFactStore::default();
            let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
                CheckedResourceObservation::certify(
                    &function,
                    &before,
                    &facts,
                    &selected,
                    ResourceObservationInput::NamedCells(before.memory()),
                    &facts,
                    &PersistentOrderedSet::default(),
                    &CheckedCallEvents::default(),
                )
                .unwrap()
            });
            assert!(
                observed
                    .after_state
                    .resources()
                    .has_supported_projection(&child, support, &selected,)
            );
            assert_eq!(
                observed
                    .after_state
                    .resources()
                    .owned_fact_for_occurrence(support),
                Some(&selected)
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn borrowed_observation_work_tracks_the_selected_body_instead_of_the_frame_or_borrow() {
    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let definition = CompositeResourceDefinition::new(
            "borrow_box",
            Vec::new(),
            None,
            false,
            vec![ResourceSpec::token(
                ResourceAccessMode::Own,
                "child".into(),
                Vec::new(),
                Vec::new(),
            )],
            Vec::new(),
        );
        let function = program_function(
            ProgramType::Void,
            "observe_borrow",
            Vec::new(),
            ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let head = ResourceFact::View(
            ResourceFact::own_composite("borrow_box".into(), Vec::new())
                .resource()
                .clone(),
        );
        let child = ResourceFact::view_token("child".into(), Vec::new());
        let resources = ResourceContext::new().unchecked_with_fact(head.clone());
        let support = resources.first_exact_occurrence(&head).unwrap();
        let ledger = crate::kernel::BorrowLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let backing = crate::kernel::borrows::BorrowedContractInputBacking::from_checked_expansion(
            support,
            head.clone(),
            Vec::new(),
        )
        .unwrap();
        let opening = ledger
            .borrowed_contract_input(holder, support, head.clone(), Some(backing))
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let binding = crate::kernel::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: head.clone(),
            hold: None,
        };
        // Simulate previous projections from this borrow and unrelated owners
        // in the same execution state.
        let old_views = (0..count)
            .map(|index| ResourceFact::view_token(format!("old_{index}"), Vec::new()))
            .collect();
        let ledger = ledger
            .project_observed_body(
                holder,
                &binding,
                crate::kernel::borrows::CompositeProjectionEvidence::from_checked_expansion(
                    head.clone(),
                    old_views,
                )
                .unwrap(),
            )
            .unwrap();
        let resources = resources.unchecked_with_facts(
            (0..count).map(|index| ResourceFact::own_token(format!("owner_{index}"), Vec::new())),
        );
        let state = ExecutionState::new()
            .with_borrow_ledger(Some(ledger))
            .with_borrow_participant(Some(holder))
            .with_resource_context_and_borrow_dependencies(resources, [(support, binding.clone())]);
        let facts = PureFactStore::default();
        let observe = |state: &ExecutionState| {
            CheckedResourceObservation::certify(
                &function,
                state,
                &facts,
                &head,
                ResourceObservationInput::NamedCells(state.memory()),
                &facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .map(|observation| observation.after_state)
        };
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| observe(&state));
        let after = after.unwrap();
        let child_occurrence = after.resources().first_exact_occurrence(&child).unwrap();
        let child_binding = after
            .resources()
            .borrow_dependency(child_occurrence)
            .unwrap();
        assert_eq!(
            child_binding,
            &crate::kernel::BorrowBinding {
                viewed: child.clone(),
                ..binding
            }
        );
        assert!(
            after
                .borrow_ledger()
                .unwrap()
                .validate_view_binding(child_binding.clone(), holder)
                .is_ok()
        );
        assert_eq!(state.resources().first_exact_occurrence(&child), None);
        assert_eq!(
            observe(&after)
                .unwrap()
                .resources()
                .occurrences_for_fact(&child),
            [child_occurrence],
        );
        let unbound = state
            .clone()
            .with_resource_context(state.resources().clone().unchecked_with_fact(child.clone()));
        assert!(observe(&unbound).is_err());
        let wrong_holder = state.clone().with_borrow_participant(Some(
            state.borrow_ledger().unwrap().fresh_participant().unwrap(),
        ));
        assert!(observe(&wrong_holder).is_err());
        samples.push(work);
    }
    assert!(samples[2] <= samples[0] + 64, "{samples:?}");
}
