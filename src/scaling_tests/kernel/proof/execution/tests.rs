// Scaling tests of `src/kernel/proof/execution.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn balanced_unit_sum_domain_uses_only_indexed_related_bounds() {
    use crate::kernel::ConditionTerm;
    let a = Bitvector32Term::Variable(Variable(200));
    let b = Bitvector32Term::Variable(Variable(201));
    let one = Bitvector32Term::Constant(1);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(
            Bitvector32Term::add(a.clone(), one.clone()),
            Bitvector32Term::subtract(b.clone(), one),
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
                ConditionTerm::signed_less_than(
                    a.clone(),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(b.clone(), Bitvector32Term::Constant(1)),
                true,
            );
        for i in 0..n {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(1000 + i)),
                    Bitvector32Term::Constant(100),
                ),
                true,
            );
        }
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::authority_control_evaluation_condition_proven(&facts, &goal)
        });
        assert!(valid);
        // Removing the old domain must fail without searching the frame.
        let missing_old = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_than(a.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
            true,
        );
        assert!(!super::super::authority_control_evaluation_condition_proven(&missing_old, &goal));
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
    use crate::kernel::{CMemory, Pointer, PointerBlock, PointerOffsetTerm};
    let target = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for count in [8, 32, 128, 512] {
        let mut before = CMemory::new();
        for index in 0..count {
            before = before.store(
                Pointer {
                    block: PointerBlock::Heap(index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::Int32(Bitvector32Term::Constant(7)),
            );
        }
        let name = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_c_memory(before.clone()),
            target.clone(),
            crate::kernel::LoadKind::Bits32,
        );
        let after = before
            .clone()
            .materialize_named_cell(target.clone(), CValue::Int32(name));
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::memory_only_adds_named_cells(&before, &after)
        });
        checked.unwrap();
        samples.push(work);
        assert!(super::super::memory_only_adds_named_cells(&after, &before).is_err());
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn constructor_partition_transports_pointer_payloads_without_scanning_ambient_facts() {
    let (core, mut value) = constructor_partition_fixture_with_type(2, CType::Int32Pointer);
    let payload = Pointer::symbolic(Variable(7_000_000));
    let program = Pointer::symbolic(Variable(1_000_001));
    value.node = crate::kernel::AlgebraicTermNode::Constructor {
        variant: "C0".into(),
        fields: vec![crate::kernel::AlgebraicValue::C(CValue::typed_pointer(
            payload.clone(),
            CType::Int32Pointer,
        ))],
    };
    let alias = Proposition::ConditionIs(
        crate::kernel::ConditionTerm::pointer_equal(payload.clone(), program.clone()),
        true,
    );
    let env = crate::kernel::CExecutionEnvironment::new();
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut facts = ProofFacts::default().with_fact(alias.clone());
        for index in 0..size {
            facts = facts.with_fact(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            });
        }
        let ((partition, fields, _), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                core.algebraic_case_partition(&facts, &value, &env, &[], None, 4_000_000, 65_536)
                    .unwrap()
            });
        let witness = Pointer::symbolic(fields[0][0].0);
        let transported = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::pointer_equal(program.clone(), witness),
            true,
        );
        assert!(partition.facts_for_case(0).unwrap().available(&transported));
        assert!(!partition.facts_for_case(1).unwrap().available(&transported));
        assert!(!facts.available(&transported));
        let (unrelated, _, _) = core
            .algebraic_case_partition(
                &ProofFacts::default(),
                &value,
                &env,
                &[],
                None,
                4_000_000,
                65_536,
            )
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
    payload.node = AlgebraicTermNode::Variable(Variable(4_065_536));
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
    sibling.node = AlgebraicTermNode::Variable(Variable(4_131_072));
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
    let environment = crate::kernel::CExecutionEnvironment::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|index| Proposition::Predicate {
                    name: format!("ambient{index}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let ((partition, witnesses, _), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                core.algebraic_case_partition(
                    &facts,
                    &value,
                    &environment,
                    &[],
                    None,
                    4_000_000,
                    65_536,
                )
                .unwrap()
            });
        // Reusing the spelling must not reuse existential witness identities.
        assert!(
            witnesses
                .iter()
                .flatten()
                .all(|(variable, _)| variable.0 > 4_131_072)
        );
        let spelled = Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(value.clone()),
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
    for size in [16u32, 32, 64, 128] {
        let before = (0..2048).fold(CMemory::new(), |memory, index| {
            memory.store(
                Pointer {
                    block: "ambient".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(i64::from(index) * 4),
                },
                int32(index),
            )
        });
        let cached = (0..size).fold(before.clone(), |memory, index| {
            let source = crate::kernel::intern_c_memory_ref(&memory);
            memory.with_seeded_cells(
                Pointer {
                    block: format!("cache-{index}").into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                4,
                crate::kernel::CType::Int32,
                0,
                2,
                source,
            )
        });
        let view = |memory, index| Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: "body".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(i64::from(index) * 4),
            },
            bytes: Bitvector32Term::Constant(4),
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
        let mut memory = CMemory::new();
        let pointers: Vec<_> = (0..size).map(|i| Pointer::symbolic(Variable(i))).collect();
        for pointer in &pointers {
            memory = memory.store(pointer.clone(), int32(7));
        }
        let state = CState::new().with_memory(memory.clone());
        let mut base = ProofFacts::default();
        let (function, mut events) = returned_proposition_trace(&state, &base);
        let initial = base.clone();
        let context = returned_proposition_context(&state);
        for pointer in pointers {
            let fact = Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: pointer,
                bytes: Bitvector32Term::Constant(4),
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
        let state = CState::new();
        let mut base = ProofFacts::default();
        let premises: Vec<_> = (0..size)
            .map(|i| {
                Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(i)),
                        Bitvector32Term::Constant(i as u32),
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
    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let instance = ResourceInstance::new(
        Variable(1),
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
        vec![crate::kernel::CResourceSpec::owned_memory(
            crate::kernel::CMemorySegment {
                base: CExpression::Value(CValue::pointer(crate::kernel::Pointer::symbolic(
                    Variable(100),
                ))),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                element_width: 4,
                guard: None,
            },
        )],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let statement = CStatement::Return(CExpression::Value(int32(7)));
    let function = c_function(CType::Int32, "test", vec![], statement.clone())
        .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = CResourceFact::own(CResource::Instance(instance.clone()));
    let folded = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
    let (open, _) = crate::kernel::rewrite_resource_instance(
        &folded,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let trace = |state: CState| {
        let mut trace = PersistentSequence::default();
        trace.push(CheckedExecutionEvent::Statement(Theorem::new(
            Proposition::CStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement.clone()),
                outcome: CStatementOutcome::Return {
                    value: int32(7),
                    state: Box::new(state),
                },
            },
        )));
        trace.push(CheckedExecutionEvent::Context(PureFactContext::new()));
        trace
    };
    let mut work_samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut core = ExecutionProofCore::at_entry(folded.clone(), ExecutionFrontier::default());
        core.execution_evidence = (0..size)
            .map(|index| {
                // A sibling lacks the body ownership. Its state cannot be used
                // to satisfy this path's fold, or vice versa.
                trace(if index == size - 1 {
                    CState::new()
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
                origin: CStatementOutcome::Return {
                    value: int32(7),
                    state: Box::new(open.clone()),
                },
                published: CFunctionOutcome::Return {
                    value: int32(7),
                    state: Box::new(open.clone()),
                },
                facts: ExecutionFacts::new(),
            }),
        );
        let (observed_after, _) = crate::kernel::rewrite_resource_instance(
            &open,
            &instance,
            &definition,
            facts.assumptions(),
            false,
        )
        .unwrap();
        let base = core.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            core.record_return_resource_rewrite_with_children(
                &function,
                size / 2,
                &facts,
                &selected,
                &facts,
                false,
                None,
                Some((&open, &observed_after)),
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
        let CStatementOutcome::Return { value, state } = outcome else {
            panic!("the completion returns");
        };
        assert_eq!(value, int32(7));
        let resources = state
            .resources()
            .clone()
            .without_owned_instance_read_views();
        assert_eq!(state.with_resource_context(resources), folded);
        // Copying an event to a different path with a different body
        // state is rejected during final certification.
        let mut forged = base.execution_evidence[size - 1].clone();
        forged.push(events.last().unwrap().clone());
        assert!(trace_completion(&function, &forged.to_vec(), facts.assumptions(), false).is_err());
        let mut collected = base.clone();
        collected
            .collect_return_resource_rewrites(&core, size / 2)
            .unwrap();
        let extra = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(1000)),
                Bitvector32Term::Constant(9),
            ),
            true,
        );
        let snapshot_facts = facts.with_fact(extra.clone());
        let mut snapshot = base.clone();
        snapshot
            .record_return_resource_rewrite(
                &function,
                0,
                &snapshot_facts,
                &selected,
                &snapshot_facts,
            )
            .unwrap();
        let (_, retained, _) = trace_completion(
            &function,
            &snapshot.return_resource_rewrites.get(&0).unwrap().to_vec(),
            facts.assumptions(),
            false,
        )
        .unwrap();
        assert!(
            !retained.proves(&extra),
            "a fold must not publish unrelated snapshot assumptions"
        );
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
}

#[test]
fn instance_rewrite_certificate_rejects_unrelated_state_and_fact_changes() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
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
    let function = c_function(
        CType::Void,
        "test",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = CResourceFact::own(CResource::Instance(instance.clone()));
    let before = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
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
            .unchecked_with_fact(CResourceFact::own_token("forged".into(), vec![])),
    );
    assert!(
        CheckedResourceRewrite::check(
            &function, &before, &facts, &selected, &forged, &facts, &calls
        )
        .is_err()
    );
    let forged = opened
        .clone()
        .with_memory(CMemory::new().with_block("invented", 4));
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
    let forged_facts = facts.with_fact(Proposition::ConditionIs(
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
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
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
            &CState::new(),
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
        let mut memory = CMemory::new();
        let mut then_state = CState::new().with_local("changed", int32(1));
        let mut stable_locals = BTreeMap::new();
        for index in 0..size {
            let name = format!("stable_{index}");
            let value = int32(index);
            then_state = then_state.with_local(name.clone(), value.clone());
            stable_locals.insert(name, value);
            memory = memory.store(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(i64::from(index * 4)),
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
                    crate::kernel::abstract_c_state_for_interface_join_across(
                        &then_state,
                        &siblings,
                        &stable_locals,
                        0,
                    )
                    .expect("the then arm should abstract"),
                    crate::kernel::abstract_c_state_for_interface_join_across(
                        &else_state,
                        &siblings,
                        &stable_locals,
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
    let x = Bitvector32Term::Variable(Variable(910_000));
    let strong = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let weak = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let reflexive = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(x.clone()), Box::new(x)),
        true,
    );
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut facts = ProofFacts::default().with_fact(strong.clone());
        for index in 0..size {
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(920_000 + index)),
                    Bitvector32Term::Constant(100),
                ),
                true,
            ));
        }
        assert!(
            facts.assumptions().proves(&weak),
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
#[ignore = "nightly: 0.7s in the parallel gate"]
fn interface_aliased_wide_read_preserves_scope_history_and_scales() {
    use crate::kernel::{CPointerValue, ConditionTerm, SpecMemory};
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Pointer::symbolic(Variable(951_000));
    let alias = Pointer::symbolic(Variable(951_001));
    let value = Bitvector32Term::UInt64Constant(0x1234_5678_9abc_def0);
    let load = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
            alias.clone(),
            CType::UInt64Pointer,
        )))),
        value_type: CType::UInt64,
    };
    let spec = SpecProposition::Comparison {
        left: load.clone(),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(CValue::UInt64(value.clone())),
    };
    let mut previous = None;
    for count in [16_u32, 64, 256, 1024] {
        let mut memory = CMemory::new();
        let mut parent = ProofFacts::default();
        for index in 0..count {
            memory = memory.store(owner.offset_by_bytes((index + 1) * 8), int32(index));
            parent = parent.with_fact(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(952_000 + u64::from(index))),
                    Bitvector32Term::Constant(index),
                ),
                true,
            ));
        }
        memory = memory.store(owner.clone(), CValue::UInt64(value.clone()));
        let state = CState::new().with_memory(memory.clone());
        let arm = parent.with_fact(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(alias.clone(), owner.clone()),
            true,
        ));
        let check = |state: &CState, facts: &ProofFacts, spec: &SpecProposition| {
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
            (0, CValue::UInt64(Bitvector32Term::UInt64Constant(7))),
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
    use crate::kernel::{CMemory, Pointer};
    let memory = CMemory::new();
    let readable = |memory: CMemory, block: String, width| Proposition::CMemoryLoadable {
        memory,
        base: Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::Constant(width),
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
                &readable(CMemory::new().with_block("other", 4), "selected".into(), 4),
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
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let samples = [16, 32, 64, 128].map(|size| {
        let mut facts = ProofFacts::default();
        let mut state = CState::new();
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
            assert_eq!(copy.snapshot, state);
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
