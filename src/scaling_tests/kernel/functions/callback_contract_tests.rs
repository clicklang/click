// Scaling tests of `src/kernel/functions/callback_contract_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn authoritative_memory_projection_scales_with_used_members_not_unrelated_frames() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:projection:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 512));
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let mut memory = state.memory.clone();
        for unrelated in 0..256 {
            memory = memory.with_block(format!("local:projection:frame:{unrelated}"), 4);
        }
        let state = state.clone().with_memory(memory);
        let function = c_function(
            CType::Void,
            format!("project_{used_members}"),
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Skip,
        )
        .with_contract(
            vec![],
            vec![],
            (0..used_members)
                .map(|index| {
                    CMemorySegment::new(
                        c_variable("p"),
                        c_int32_literal(index as u32),
                        c_int32_literal(index as u32 + 1),
                    )
                })
                .collect(),
            vec![],
            true,
        );
        let mut budget = ExecutionBudget::default();
        let (projection, work) = crate::instrumentation::measure_deterministic_work(|| {
            project_contract_memory_effects(
                &state,
                function.contract_interface(),
                None,
                &PureFactContext::new(),
                &mut budget,
            )
        });
        assert_eq!(projection.unwrap().unwrap().ranges.len(), used_members);
        samples.push((used_members, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0).max(1) + 64,
            "memory projection should charge used members, not unrelated frames: {samples:?}"
        );
    }

    // Resource-derived frames use the checked transition as their source of
    // memory authority. A bare resource summary without this marker must not
    // turn an abstract callback into an unconditional memory havoc.
    let resource = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(1),
    ));
    let resource_function = c_function(
        CType::Void,
        "project_resource",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::Skip,
    )
    .with_resource_summary(vec![resource], vec![])
    .with_resource_derived_mutable_frame();
    let checked_resources = [CCheckedResourceFact {
        fact: CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        role: CResourceTransferRole::Consume,
        snapshot: CResourceSnapshot::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    }];
    let projection = project_contract_memory_effects(
        &state,
        resource_function.contract_interface(),
        Some(&checked_resources),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(projection.ranges.len(), 1);
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn checked_transition_projection_ignores_unrelated_caller_frame() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:transition:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let mut frame_work = None;
        for unrelated in [0, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let requirements = (0..used_members)
                .map(|index| {
                    CResourceSpec::owned_memory(CMemorySegment::new(
                        CExpression::Variable("p".into()),
                        CExpression::Value(int32(index as u32)),
                        CExpression::Value(int32(index as u32 + 1)),
                    ))
                })
                .collect::<Vec<_>>();
            let owned = (0..used_members)
                .map(|index| {
                    CResourceFact::own_memory(CMemoryRange::new(
                        pointer.clone(),
                        Bitvector32Term::Constant(index as u32),
                        Bitvector32Term::Constant(index as u32 + 1),
                    ))
                })
                .chain((0..unrelated).map(|index| {
                    CResourceFact::own_token(format!("unrelated_transition_token_{index}"), vec![])
                }))
                .collect::<Vec<_>>();
            let state = CState::new()
                .with_local("p", CValue::pointer(pointer.clone()))
                .with_memory(CMemory::new().with_block(pointer.block.clone(), 512))
                .with_resource_context(ResourceContext::new().unchecked_with_facts(owned));
            let function = c_function(
                CType::Void,
                format!("transition_projection_{used_members}"),
                vec![c_parameter("p", CType::Int32Pointer)],
                CStatement::Skip,
            )
            .with_contract(vec![], vec![], vec![], vec![], true)
            .with_resource_summary(requirements, vec![])
            .with_resource_derived_mutable_frame();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let transfer = prepare_contract_resource_transfer(
                    &state,
                    &state,
                    function.name(),
                    function.contract_interface(),
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                    false,
                    ResourceTransitionPurpose::FunctionBoundary,
                )
                .unwrap()
                .unwrap();
                let mut inputs = transfer.borrowed_inputs.clone();
                inputs.extend(transfer.consumed_inputs.clone());
                project_contract_memory_effects(
                    &state,
                    function.contract_interface(),
                    Some(&inputs),
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                )
            });
            assert_eq!(result.unwrap().unwrap().ranges.len(), used_members);
            if let Some(previous) = frame_work {
                assert_eq!(
                    work, previous,
                    "unrelated caller frame changed transition work"
                );
            }
            frame_work = Some(work);
        }
        samples.push((used_members, frame_work.unwrap()));
    }
    // A single member has only a zero-offset address; later members also
    // register displaced addresses. Compare marginal work per added member
    // rather than requiring these two different operations to cost the same.
    for triple in samples.windows(3) {
        let earlier_work = triple[1].1 - triple[0].1;
        let later_work = triple[2].1 - triple[1].1;
        let earlier_members = triple[1].0 - triple[0].0;
        let later_members = triple[2].0 - triple[1].0;
        assert!(
            later_work * earlier_members <= earlier_work * later_members,
            "checked transition work per added member grew: {samples:?}"
        );
    }
}

#[test]
fn checked_wrapper_projection_scales_with_used_members() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:wrapper:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let contains = (0..used_members)
            .map(|index| {
                CResourceSpec::owned_memory(CMemorySegment::new(
                    CExpression::Variable("data".into()),
                    CExpression::Value(int32(index as u32)),
                    CExpression::Value(int32(index as u32 + 1)),
                ))
            })
            .collect();
        let definition = CCompositeResourceDefinition::new(
            "TransitionWrapper",
            vec![c_parameter("data", CType::Int32Pointer)],
            None,
            false,
            contains,
            vec![],
        );
        let requirement = CResourceSpec::composite(
            CResourceAccessMode::Own,
            "TransitionWrapper".into(),
            vec![CExpression::Variable("p".into())],
            vec![CType::Int32Pointer],
        );
        let state = CState::new()
            .with_local("p", CValue::pointer(pointer.clone()))
            .with_memory(CMemory::new().with_block(pointer.block.clone(), 512))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_composite(
                    "TransitionWrapper".into(),
                    vec![CValue::pointer(pointer.clone())],
                ),
            ));
        let function = c_function(
            CType::Void,
            format!("wrapper_projection_{used_members}"),
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Skip,
        )
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![requirement], vec![])
        .with_composite_resource_definitions(vec![definition])
        .with_resource_derived_mutable_frame();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let transfer = prepare_contract_resource_transfer(
                &state,
                &state,
                function.name(),
                function.contract_interface(),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
                false,
                ResourceTransitionPurpose::FunctionBoundary,
            )
            .unwrap()
            .unwrap();
            let mut inputs = transfer.borrowed_inputs.clone();
            inputs.extend(transfer.consumed_inputs.clone());
            project_contract_memory_effects(
                &state,
                function.contract_interface(),
                Some(&inputs),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
        });
        // Adjacent body members are normalized to one physical range; the
        // curve still charges their checked expansion and effect projection.
        assert_eq!(result.unwrap().unwrap().ranges.len(), 1);
        samples.push((used_members, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0).max(1) + 256,
            "wrapper projection should charge used members: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn callback_fact_lookup_scales_with_calls_not_unrelated_supported_facts() {
    fn callback_fact(name: &str, pointer: Pointer, state: CState) -> Proposition {
        Proposition::Predicate {
            name: CFunctionContract::predicate_name_for(name),
            arguments: vec![
                Term::CState(Box::new(state)),
                Term::CValue(CValue::typed_pointer(
                    pointer,
                    CType::FunctionPointer(CallbackSignature::from_encoded(91_000)),
                )),
            ],
        }
    }

    let target = Pointer::symbolic_function(Variable(92_000));
    let mut samples = Vec::new();
    for calls in [1usize, 2, 4, 8, 16] {
        for unrelated in [4usize, 16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new().assume_proposition(callback_fact(
                "Target",
                target.clone(),
                CState::new(),
            ));
            for index in 0..unrelated {
                assumptions = assumptions.assume_proposition(callback_fact(
                    "Unrelated",
                    Pointer::symbolic_function(Variable(93_000 + index as u64)),
                    CState::new(),
                ));
            }
            let before_allocations = crate::persistent::persistent_node_allocations();
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                (0..calls)
                    .map(|_| assumptions.function_contract_facts_for(&target).count())
                    .sum::<usize>()
            });
            let allocations = crate::persistent::persistent_node_allocations() - before_allocations;
            assert_eq!(found, calls);
            assert_eq!(
                allocations, 0,
                "lookup must not allocate for unrelated facts"
            );
            samples.push((calls, unrelated, work));
        }
    }

    for calls in [1usize, 2, 4, 8, 16] {
        let row = samples
            .iter()
            .filter(|(sample_calls, _, _)| *sample_calls == calls)
            .collect::<Vec<_>>();
        assert!(
            row.windows(2).all(|pair| pair[1].2 == pair[0].2),
            "unrelated supported callback facts changed lookup work at {calls} calls: {row:?}"
        );
    }
    for pair in samples
        .iter()
        .filter(|(_, unrelated, _)| *unrelated == 4)
        .collect::<Vec<_>>()
        .windows(2)
    {
        assert!(
            pair[1].2 <= pair[0].2 * 2,
            "callback lookup work should grow linearly with selected calls: {samples:?}"
        );
    }
}

/// Contract refinement decides one named clause by the exact routes only:
/// indexed exact membership and the frozen condition checker on a bare
/// condition. Neither a decided clause nor a rejected one may scan the
/// ambient facts, so growing the unrelated context must not change the work.
#[test]
fn contract_refinement_work_is_flat_in_unrelated_facts() {
    let variable = |index| Bitvector32Term::Variable(Variable(index));
    let bound = ConditionTerm::signed_less_than(variable(70_001), Bitvector32Term::Constant(10));
    let equality = ConditionTerm::equal(variable(70_002), variable(70_003));
    let refuted = ConditionTerm::signed_less_than(variable(70_005), Bitvector32Term::Constant(0));
    let unproved = Proposition::Predicate {
        name: "unproved_refinement_clause".to_string(),
        arguments: vec![],
    };
    // An exactly available bare condition.
    let exact = Proposition::ConditionIs(equality.clone(), true);
    // A bare condition the frozen checker decides against, read through `not`.
    let negated = Proposition::Not(Box::new(Proposition::ConditionIs(refuted.clone(), true)));
    // Compound clauses no exact route establishes. The logical descent that
    // used to split these now belongs to the refinement theorem's proof, so
    // the kernel answers no — and must do so without an ambient scan.
    let structural = Proposition::And(
        Box::new(Proposition::ConditionIs(bound.clone(), true)),
        Box::new(Proposition::Or(
            Box::new(Proposition::ConditionIs(equality.clone(), true)),
            Box::new(unproved.clone()),
        )),
    );
    let guarded = Proposition::Implies(
        Box::new(Proposition::ConditionIs(refuted.clone(), true)),
        Box::new(unproved),
    );

    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new()
                .assume_condition(bound.clone(), true)
                .assume_condition(equality.clone(), true)
                .assume_condition(refuted.clone(), false);
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(71_000 + index as u64)),
                        Bitvector32Term::Constant(index as u32 + 1),
                    ),
                    true,
                );
            }
            let measure = |goal: &Proposition, expected: bool| {
                let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                    contract_refinement_proves(&assumptions, goal)
                });
                assert_eq!(
                    proved, expected,
                    "refinement answer changed with {size} unrelated facts"
                );
                work
            };
            (
                size,
                measure(&exact, true),
                measure(&negated, true),
                measure(&structural, false),
                measure(&guarded, false),
            )
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| {
            pair[0].1 == pair[1].1
                && pair[0].2 == pair[1].2
                && pair[0].3 == pair[1].3
                && pair[0].4 == pair[1].4
        }),
        "refinement checking must not scan unrelated ambient facts: {samples:?}"
    );
}
