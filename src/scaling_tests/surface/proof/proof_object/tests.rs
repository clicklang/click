// Scaling tests of `src/surface/proof/proof_object/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

fn same_block_offset_rewrite_work(
    pointer_history: usize,
    snapshot_count: usize,
    from_cursor: bool,
) -> usize {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let base = Pointer {
        block: crate::kernel::PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(8_179_100))),
            byte_width: 4,
        },
    };
    let remaining = Bitvector32Term::Variable(Variable(8_179_101));
    let k = Bitvector32Term::UInt32From64(Box::new(remaining.clone()));
    let shifted = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(base.offset.clone()),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Subtract(
                    Box::new(Bitvector32Term::Constant(4)),
                    Box::new(k.clone()),
                )),
                byte_width: 4,
            }),
        ),
    };
    let cursor = Pointer::symbolic(Variable(8_179_099));
    let state = CState::new()
        .with_local("cursor", CValue::pointer(cursor.clone()))
        .with_local("base", CValue::pointer(base.clone()))
        .with_local("k", CValue::UInt64(remaining));
    let mut facts = (0..pointer_history)
        .flat_map(|i| {
            let old = Bitvector32Term::UInt32From64(Box::new(Bitvector32Term::Variable(Variable(
                8_180_000 + i as u64,
            ))));
            [
                Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(
                        Pointer {
                            block: base.block.clone(),
                            offset: PointerOffsetTerm::Add(
                                Box::new(base.offset.clone()),
                                Box::new(PointerOffsetTerm::Int32Scaled {
                                    value: Box::new(Bitvector32Term::Subtract(
                                        Box::new(Bitvector32Term::Constant(4)),
                                        Box::new(old.clone()),
                                    )),
                                    byte_width: 4,
                                }),
                            ),
                        },
                        base.clone(),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(old),
                        Box::new(Bitvector32Term::Constant(4)),
                    ),
                    true,
                ),
            ]
        })
        .collect::<Vec<_>>();
    let bound = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(k), Box::new(Bitvector32Term::Constant(4))),
        true,
    );
    facts.push(bound.clone());
    let fixture = crate::surface::parse("theorem shifted(cursor: int32*, base: int32*, k: uint64) { requires ((int32)(uint32)k) == 4; requires cursor == base + (4 - ((int32)(uint32)k)); ensures true; }").unwrap();
    let surface = fixture.theorem_definitions()[0].requires[0]
        .proposition()
        .unwrap()
        .clone();
    let mut surfaces = SurfacePropositionMap::default();
    // The checked scalar fact has no recorded source form, as in a loop-head have.
    let lowered = lower_fixed_state_proposition_with_assumptions(
        &surface,
        &PureFactContext::new(),
        ParameterBinding::default(),
        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    assert_eq!(lowered, bound);
    let entry = state.clone().with_local(
        "k",
        CValue::UInt64(Bitvector32Term::Variable(Variable(8_179_098))),
    );
    if from_cursor {
        let CValue::Pointer(cursor_value) = state.locals().get("cursor").unwrap() else {
            unreachable!()
        };
        let CValue::Pointer(base_value) = state.locals().get("base").unwrap() else {
            unreachable!()
        };
        let mut shifted_value = base_value.clone();
        shifted_value.replace_pointer(shifted.clone());
        let relation = Proposition::ConditionIs(
            ConditionTerm::pointer_value_equal(cursor_value.clone(), shifted_value),
            true,
        );
        let relation_surface = fixture.theorem_definitions()[0].requires[1]
            .proposition()
            .unwrap()
            .clone();
        assert_eq!(
            lower_fixed_state_proposition_with_assumptions(
                &relation_surface,
                &PureFactContext::new(),
                ParameterBinding::default(),
                FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
                SpecDefinitions::new(&predicates, &functions),
            )
            .unwrap(),
            relation,
        );
        surfaces
            .record_lowering(&relation_surface, &relation)
            .unwrap();
        facts.insert(0, relation);
    }
    let mut snapshots = RecordedSnapshots::new();
    for i in 0..snapshot_count {
        snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Statement(i),
                kind: ProgramPointKind::Entry,
            },
            entry.clone(),
        );
    }
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Statement(snapshot_count - 1),
        kind: ProgramPointKind::Entry,
    };
    let root = Proof::for_fixed_state_goal_with_requirements(
        "same-block offset equality",
        0,
        &facts,
        Proposition::ConditionIs(
            ConditionTerm::pointer_equal(if from_cursor { cursor } else { shifted }, base),
            true,
        ),
        ParameterBinding::default(),
        FixedStateFrame::new(&entry, &state, None, &snapshots),
        Some(&anchor),
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
        &[],
        &[],
    );
    let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
        root.try_indexed_goal_equality_rewrite_closure()
    });
    let closed = closed.expect("the offset's k == 4 fact should close the pointer equality");
    assert!(closed.is_complete());
    // Shared literal propagation can close the goal during its last rewrite;
    // only the selected pointer equality needs an explicit checked rewrite.

    assert_eq!(
        closed
            .certificate()
            .steps()
            .iter()
            .filter(|step| matches!(step, ProofStep::Rewrite(_)))
            .count(),
        1
    );
    work
}

#[test]
fn same_block_pointer_offset_rewrite_ignores_other_pointers_at_the_base() {
    let costs = [4, 8, 16, 32].map(|size| same_block_offset_rewrite_work(size, 4, false));
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn same_block_pointer_offset_rewrite_does_not_search_recorded_snapshots() {
    let costs = [4, 8, 16, 32].map(|size| same_block_offset_rewrite_work(4, size, true));
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn both_and_scopes_are_isolated_check_provenance_and_scale() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let truth = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let other = Proposition::Equal(
        Term::Bitvector32(Bitvector32Term::Constant(7)),
        Term::Bitvector32(Bitvector32Term::Constant(7)),
    );
    let goal = Proposition::And(Box::new(truth.clone()), Box::new(other.clone()));
    let samples = [16, 32, 64, 128].map(|size| {
        let facts = (0..size)
            .map(|i| Proposition::Predicate {
                name: format!("ambient_{i}"),
                arguments: vec![],
            })
            .collect::<Vec<_>>();
        let root = Proof::for_pure_goal(
            "both",
            &facts,
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let ((joined, split_proof, left_done, marker, split, ids), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let (split_proof, split, ids) = root.split_focused_both().unwrap();
                let marker = split_proof.checkpoint();
                assert_eq!(
                    split_proof.focus_branch(ids[0]).unwrap().goal(),
                    Some(&truth)
                );
                assert_eq!(
                    split_proof.focus_branch(ids[1]).unwrap().goal(),
                    Some(&other)
                );
                assert!(!split_proof.facts().contains(&truth));
                assert!(!split_proof.facts().contains(&other));
                let left_done = split_proof
                    .focus_branch(ids[0])
                    .unwrap()
                    .apply_step(ProofStep::Normalize)
                    .unwrap();
                let right = left_done.focus_branch(ids[1]).unwrap();
                assert!(!right.facts().contains(&truth));
                let done = right.apply_step(ProofStep::Normalize).unwrap();
                let joined = done.join_focused_both(&marker, split, ids).unwrap();
                (joined, split_proof, left_done, marker, split, ids)
            });
        assert!(joined.is_complete());
        assert!(left_done.join_focused_both(&marker, split, ids).is_err());
        let (foreign, foreign_split, foreign_ids) = root.split_focused_both().unwrap();
        let done = left_done
            .focus_branch(ids[1])
            .unwrap()
            .apply_step(ProofStep::Normalize)
            .unwrap();
        assert!(
            done.join_focused_both(&foreign.checkpoint(), foreign_split, foreign_ids)
                .is_err()
        );
        assert_eq!(split_proof.branches().count(), 2);
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Both { .. }]
        ));
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 5.7s in the parallel gate"]
fn loop_entry_simp_keeps_checked_unspellable_assumptions_and_scales() {
    let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
    let state = CState::new();
    let result = int32(0);
    let arguments = vec![CExpression::Value(result.clone())];
    let snapshots = RecordedSnapshots::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    // Loop producers may capture a value that the phase's source naming
    // tables do not spell. The producer's kernel judgment is authoritative;
    // its source proposition is a presentation, not a replacement judgment.
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".into())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_less_than(
            Bitvector32Term::Variable(crate::kernel::Variable(1_000_000)),
            Bitvector32Term::UInt64Constant(22208),
        ),
        true,
    );
    let obligation = crate::kernel::ProofObligation::new(goal.clone());
    let mut previous_work = None;
    for size in [16_u32, 64, 256, 1024] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::uint64_less_than(
                        Bitvector32Term::Variable(crate::kernel::Variable(1_000_000)),
                        Bitvector32Term::UInt64Constant(22209 + u64::from(index)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        facts.push(goal.clone());
        let root = Proof::for_fixed_state_frontier(
            "loop entry unspellable assumption",
            0,
            &facts,
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &snapshots),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let scope = root
            .begin_loop_entry_goal(surface.clone(), &obligation)
            .unwrap();
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            scope.try_simp_closure().unwrap().unwrap()
        });
        assert_eq!(
            checked.body().certificate().steps(),
            &[ProofStep::Assumption]
        );
        let completion = checked.completed_loop_entry_goal().unwrap();
        assert_eq!(completion.proposition(), &goal);
        assert!(
            completion
                .root_assumptions()
                .shares_assumptions_with(root.facts())
        );
        assert!(checked.join().unwrap().facts().contains(&goal));
        if let Some(previous) = previous_work {
            assert!(
                work <= previous + 128,
                "{size}: {work} units after {previous}"
            );
        }
        previous_work = Some(work);
        let missing = Proof::for_fixed_state_frontier(
            "loop entry missing assumption",
            0,
            &facts[..facts.len() - 1],
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &snapshots),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let missing = missing
            .begin_loop_entry_goal(surface.clone(), &obligation)
            .unwrap();
        assert!(missing.apply_step(ProofStep::Assumption).is_err());
        assert!(missing.join().is_err());
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn choose_projection_walk_is_deterministic_across_selected_body_sizes() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                requires exists (k: int32) { k == x };
                ensures result == x;
            }
        "#,
    )
    .expect("the existential requirement should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let function = parsed_function.to_kernel_function();
    let predicates = PredicateEnvironment::new(&[]);
    let click_functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let execution_environment = CExecutionEnvironment::new();
    let state = CState::new();
    let arguments = vec![CExpression::Value(int32(7))];

    fn balanced_and(mut leaves: Vec<Proposition>) -> Proposition {
        while leaves.len() > 1 {
            let mut next = Vec::with_capacity(leaves.len().div_ceil(2));
            let mut pairs = leaves.into_iter();
            while let Some(left) = pairs.next() {
                let Some(right) = pairs.next() else {
                    next.push(left);
                    break;
                };
                next.push(Proposition::And(Box::new(left), Box::new(right)));
            }
            leaves = next;
        }
        leaves
            .pop()
            .expect("a selected body must have at least one leaf")
    }

    let run = |size: u32| {
        let chosen_variable = Variable(9_300_000);
        let body = balanced_and(
            (0..size)
                .map(|index| {
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(Bitvector32Term::Variable(chosen_variable)),
                            Box::new(Bitvector32Term::Constant(index)),
                        ),
                        true,
                    )
                })
                .collect(),
        );
        let source = Proposition::Exists {
            name: "source_value".to_string(),
            var: chosen_variable,
            sort: Sort::CInt32,
            body: Box::new(body),
        };
        let owner = CallerSourceOwnerId::ordinary("test.c", "identity");
        let entry_origins = vec![EntryFactOrigin::Requirement {
            source_id: RequirementSourceId {
                owner: owner.clone(),
                outer_ordinal: 0,
            },
            role: RequirementFactRole::Principal {
                unfolding_path: Vec::new(),
            },
        }];
        let caller_requirement_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            function_block,
            parsed_function.parameters(),
            std::slice::from_ref(&source),
            &entry_origins,
            crate::kernel::CMemorySnapshotIdentity::of(state.memory()),
        );
        let before = fact_node_allocations();
        let root = Proof::for_execution_frontier(
            "chosen projection scaling",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedSnapshots::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            vec![source.clone()],
            ExecutionProofConstants {
                function_entry_state: Some(state.clone()),
                execution_start_facts: Arc::new(PureFactList::from(vec![source])),
                entry_fact_origins: entry_origins.into(),
                caller_requirement_index: caller_requirement_index.into(),
                caller_source_owner: Some(owner),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &execution_environment,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        );
        CHOSEN_PROJECTION_WALK_WORK.with(|count| count.set((0, 0)));
        let chosen = root
            .apply_step(ProofStep::Choose(ProofChoice {
                name: "candidate".to_string(),
                source: ProofFactSource::Requirement(0),
            }))
            .expect("the selected existential should check");
        let leaves = chosen
            .execution()
            .and_then(|execution| execution.presentation.chosen_projection.as_ref())
            .map_or(0, |projection| projection.leaves.len());
        (
            leaves,
            CHOSEN_PROJECTION_WALK_WORK.with(std::cell::Cell::get),
            fact_node_allocations() - before,
        )
    };

    let mut samples = Vec::new();
    for size in [8_u32, 32, 128, 512] {
        let _ = run(size);
        let first = crate::instrumentation::measure_deterministic_work(|| run(size));
        let second = crate::instrumentation::measure_deterministic_work(|| run(size));
        assert_eq!(
            first.0.0, second.0.0,
            "leaf count must be deterministic at {size}"
        );
        assert_eq!(
            first.0.0, size as usize,
            "all selected leaves must be retained at {size}"
        );
        // Fact indexing and proof setup are outside the projection walk.
        // Their AVL shapes can differ between identical semantic samples:
        // a phased reproduction had totals 3047/3049 at 32 leaves, while
        // setup used 6 nodes and the walk used 96 nodes in both runs.
        assert_eq!(
            first.0.1, second.0.1,
            "projection visits and allocations must be deterministic at {size}"
        );
        assert_eq!(
            first.0.1.0,
            (2 * size - 1) as usize,
            "the walk must visit each selected conjunction node once"
        );
        samples.push((size, first.1, first.0.1.1, first.0.2));
        samples.push((size, second.1, second.0.1.1, second.0.2));
    }
    let (base_size, base_work, base_walk_allocations, _) = samples[0];
    for (size, work, walk_allocations, total_allocations) in samples {
        assert!(
            work <= base_work + 64 * (size - base_size) as usize,
            "selected-body projection work exceeded the linear bound at {size}: {work}"
        );
        assert!(
            walk_allocations <= base_walk_allocations + 8 * (size - base_size) as usize,
            "projection walk allocations exceeded the linear bound at {size}: {walk_allocations}"
        );
        // The complete choose also updates persistent fact indexes; their
        // logarithmic search paths have a separate size-dependent bound.
        let index_height = (u32::BITS - size.leading_zeros()) as usize;
        assert!(
            total_allocations <= 32 * size as usize * index_height,
            "proof setup and choose allocations exceeded the indexed bound at {size}: {total_allocations}"
        );
    }
}

#[test]
fn explicit_loop_have_retains_checked_body_and_complete_invariant_bundle() {
    let file = crate::surface::parse(
        r#"
        predicate selected(x: int32) { x == x }
        int32 identity(int32 x) { ensures result == x; }
    "#,
    )
    .unwrap();
    let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
    let function = parsed.to_kernel_function();
    let predicates = PredicateEnvironment::new(file.predicate_definitions());
    let click_functions = ClickFunctionEnvironment::new(file.click_function_definitions());
    let theorems = TheoremEnvironment::new(file.theorem_definitions());
    let resources = ResourceEnvironment::new(file.resource_definitions());
    let environment = CExecutionEnvironment::new();
    let arguments = vec![CExpression::Value(int32(7))];
    let value = ContractExpression::CFragment(CExpression::Value(int32(7)));
    let surface = ClickProposition::PredicateCall {
        name: "selected".into(),
        arguments: vec![value.clone()],
    };
    let body_surface = ClickProposition::Comparison {
        left: value.clone(),
        operator: ComparisonOperator::Equal,
        right: value,
    };
    let spec = crate::kernel::SpecProposition::Comparison {
        left: crate::kernel::SpecExpression::Value(int32(7)),
        operator: crate::kernel::CComparisonOperator::Equal,
        right: crate::kernel::SpecExpression::Value(int32(7)),
    };
    let checks = vec![
        CLoopInvariantCheck::new(spec, None, None),
        CLoopInvariantCheck::new(
            crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::Value(int32(7)),
                operator: crate::kernel::CComparisonOperator::LessEqual,
                right: crate::kernel::SpecExpression::Value(int32(8)),
            },
            None,
            None,
        ),
    ];
    let legacy_surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Value(int32(7))),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(8))),
    };
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let frontier = ExecutionFrontier {
            region: ExecutionRegionKind::LoopBody,
            position: FrontierPosition::RegionBoundary,
            ..ExecutionFrontier::default()
        };
        let root = Proof::for_execution_frontier(
            "checked loop have",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                frontier,
                RecordedSnapshots::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                invariant_body_context: Some(Arc::new(InvariantBodyContext {
                    checks: checks.clone(),
                    ..InvariantBodyContext::default()
                })),
                ..ExecutionProofConstants::default()
            },
            &file.function_blocks()[0],
            &function,
            &parsed,
            &arguments,
            &environment,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        )
        .apply_step(ProofStep::UnfoldPredicate("selected".into()))
        .unwrap();
        let body_kernel = root.lower_surface_goal(&body_surface, "test body").unwrap();
        let scope = root.begin_have(surface.clone()).unwrap();
        assert!(scope.clone().join().is_err());
        let closed = scope.apply_step(ProofStep::Normalize).unwrap();
        let (joined, work) =
            crate::instrumentation::measure_deterministic_work(|| closed.join().unwrap());
        samples.push(work);
        assert!(joined.facts().contains(&body_kernel));
        assert!(!root.facts().contains(&body_kernel));
        assert_eq!(joined.added_facts().len(), 2);
        assert!(
            joined
                .execution()
                .unwrap()
                .presentation
                .surface_propositions
                .available_kernel_matching(&surface, |kernel| joined.facts().contains(kernel))
                .is_some()
        );
        let explicit = root
            .apply_step(ProofStep::Have {
                proposition: surface.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Normalize]).unwrap()),
            })
            .unwrap();
        assert!(explicit.facts().contains(&body_kernel));
        assert!(joined.certify_loop_invariant_bundle(&checks, &[]).is_err());
        let prepared = joined
            .prepare_loop_invariant_bundle(
                &CState::new(),
                &CState::new(),
                &CExpression::Value(int32(1)),
                &checks,
                &[],
                None,
                &[surface.clone(), legacy_surface.clone()],
                &[],
                &[],
                false,
            )
            .unwrap()
            .unwrap();
        let certified = prepared
            .certify_loop_invariant_bundle(&checks, &[])
            .unwrap();
        let execution = certified.execution().unwrap();
        let record = execution.core.checked_invariant_lowerings.as_ref().unwrap();
        assert_eq!(record.checks(), checks);
        assert!(matches!(
            prepared.certificate().steps().last(),
            Some(ProofStep::CloseInvariantsBy(_))
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "loop have join work: {samples:?}"
        );
    }
}

#[test]
fn explicit_invariant_body_scales_and_supplies_kernel_validation() {
    let file = crate::surface::parse("int32 region(int32 x) { ensures result == x; }").unwrap();
    let block = &file.function_blocks()[0];
    let predicates = PredicateEnvironment::new(&[]);
    let click_functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let parsed = syntax::parse_function("int32 region(int32 x) { return x; }").unwrap();
    let function = parsed.to_kernel_function();
    let functions = CExecutionEnvironment::new();
    let resources = ResourceEnvironment::new(&[]);
    let arguments = [CExpression::Value(int32(7))];
    let checks = vec![crate::kernel::CLoopInvariantCheck::new(
        crate::kernel::SpecProposition::Comparison {
            left: crate::kernel::SpecExpression::Value(int32(0)),
            operator: crate::kernel::CComparisonOperator::LessEqual,
            right: crate::kernel::SpecExpression::Value(int32(0)),
        },
        None,
        None,
    )];
    let samples = [16, 32, 64, 128].map(|size| {
        let root = Proof::for_execution_frontier(
            "explicit invariant body",
            0,
            ExecutionProofState::at_entry(
                CState::new(),
                ExecutionFrontier {
                    region: ExecutionRegionKind::LoopBody,
                    position: FrontierPosition::RegionBoundary,
                    ..Default::default()
                },
                RecordedSnapshots::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                invariant_body_context: Some(Arc::new(InvariantBodyContext {
                    checks: checks.clone(),
                    ..InvariantBodyContext::default()
                })),
                ..Default::default()
            },
            block,
            &function,
            &parsed,
            &arguments,
            &functions,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        );
        let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.apply_close_invariants_body(&[ProofTactic::Normalize])
                .unwrap()
        });
        assert!(root.certificate().steps().is_empty());
        assert!(
            !root
                .execution()
                .unwrap()
                .core
                .region_invariants_close_requested
        );
        assert!(
            closed
                .execution()
                .unwrap()
                .core
                .region_invariants_close_requested
        );
        assert_eq!(root.facts().to_vec(), closed.facts().to_vec());
        assert!(
            root.execution()
                .unwrap()
                .core
                .state
                .shares_storage_with(&closed.execution().unwrap().core.state)
        );
        assert!(matches!(
            closed.certificate().steps(),
            [ProofStep::CloseInvariantsBy(_)]
        ));
        // A bare request is not evidence; the completed kernel-owned scope is.
        let Ok(requested) = root.state.request_frontier_invariant_closure() else {
            panic!("an unclosed loop frontier accepts a closure request")
        };
        assert!(
            root.with_kernel_state(requested)
                .certify_loop_invariant_bundle(&checks, &[])
                .is_err()
        );
        closed.certify_loop_invariant_bundle(&checks, &[]).unwrap();
        assert!(
            closed
                .apply_close_invariants_body(&[ProofTactic::Normalize])
                .is_err()
        );
        assert!(root.apply_close_invariants_body(&[]).is_err());
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cursor_execution_load_binding_work_is_deterministic_and_output_sized() {
    let click_file = crate::surface::parse(
        r#"
            int32 branch_load_scaling(int32 x, int32 p[1]) {
                ensures returns_any: result == result by { assumption(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function(
        "int32 branch_load_scaling(int32 x, int32 p[1]) { if (x < 0) { return p[0]; } else { return p[0]; } }",
    )
    .expect("test C branch should parse");
    let function = parsed_function.to_kernel_function();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
    ));
    let arguments = vec![
        CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(60_002)))),
        CExpression::Value(CValue::pointer(pointer)),
    ];
    let function_environment = CExecutionEnvironment::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let run = |size: u32| {
        let root = Proof::for_execution_frontier(
            "cursor load scaling proof",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier {
                    next_statement_index: 0,
                    ..ExecutionFrontier::default()
                },
                RecordedSnapshots::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("scaling branch should split");
        let advanced = split
            .focus_split_arm(&record, true)
            .expect("then scaling arm should be open")
            .apply_step(ProofStep::Step)
            .expect("then scaling load should execute")
            .focus_split_arm(&record, false)
            .expect("else scaling arm should be open")
            .apply_step(ProofStep::Step)
            .expect("else scaling load should execute");
        let joined = advanced
            .join_focused_execution_terminal(&record)
            .expect("scaling load arms should join");
        let execution = joined.execution().expect("joined execution should remain");
        (
            execution.presentation.generated_load_bindings.len(),
            execution.presentation.generated_load_binding_events.len(),
        )
    };
    let mut samples = Vec::new();
    for size in [8_u32, 32, 128, 512] {
        // Warm the shared parser/kernel caches so the measured cursor work
        // reflects the transition and join paths rather than one-time setup.
        let _ = run(size);
        let (first, first_work) = crate::instrumentation::measure_deterministic_work(|| run(size));
        let (second, _second_work) =
            crate::instrumentation::measure_deterministic_work(|| run(size));
        assert_eq!(
            first, second,
            "cursor result must be deterministic at size {size}"
        );
        assert_eq!(
            first,
            (1, 1),
            "load metadata output must stay constant at size {size}"
        );
        samples.push((size, first_work));
    }
    let (base_size, base_work) = samples[0];
    for (size, work) in samples {
        assert!(
            work <= base_work + 64 * (size - base_size) as usize,
            "cursor load metadata work grew beyond the output-sized bound at size {size}: {work} > {}",
            base_work + 64 * (size - base_size) as usize
        );
    }
}

#[test]
fn integer_equality_rewrite_builds_names_only_on_refusal_and_scales() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let x = IntegerTerm::var(Variable(9_103_000));
    let y = IntegerTerm::var(Variable(9_103_001));
    let equality = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(x.clone().into(), y.clone().into()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(
            IntegerTerm::multiply(x.clone(), x.clone()).into(),
            y.clone().into(),
        ),
        true,
    );
    let surface = ClickProposition::Comparison {
        left: ContractExpression::Binding("x".into()),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Binding("y".into()),
    };
    let mut baseline = None;
    for size in [4usize, 16, 64, 256] {
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: CMemory::new(),
            array_refs: BTreeMap::new(),
            requires: vec![equality.clone()],
            surface_requirements: SurfacePropositionMap::default(),
            values: (0..size)
                .map(|i| (format!("unused_{i}"), int32(i as u32)))
                .collect(),
        };
        let root = Proof::for_pure_goal(
            "Integer rewrite names",
            &context.requires,
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let calls = std::cell::Cell::new(0);
        let name = || {
            calls.set(calls.get() + 1);
            crate::surface::diagnostics::value_naming_tables(&context.values)
        };
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.finish_rewrite(
                Box::new(goal.clone()),
                Box::new(equality.clone()),
                &surface,
                name,
            )
        });
        checked.expect("checked Integer rewrite should refine its goal");
        assert_eq!(
            calls.get(),
            0,
            "size {size}: successful rewrite scanned diagnostic names"
        );
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "size {size}: unrelated locals changed rewrite work"
        );
        let empty = Proof::for_pure_goal(
            "Integer rewrite refusal names",
            &[],
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let error = empty
            .finish_rewrite(
                Box::new(goal.clone()),
                Box::new(equality.clone()),
                &surface,
                name,
            )
            .err()
            .expect("missing evidence should be refused");
        assert_eq!(calls.get(), 1);
        assert!(error.message().contains("exact available fact"));
        assert!(error.message().len() < 8000);
    }
}

#[test]
fn snapshot_premise_synthesis_seeks_near_anchor_without_scanning_history() {
    let parameters = syntax::parse_function("int32 noop(int32 x) { return x; }").unwrap();
    let value = Bitvector32Term::Variable(Variable(8_178_901));
    let arguments = vec![CExpression::Value(CValue::Int32(value.clone()))];
    let parameter_binding = ParameterBinding::new(parameters.parameters(), &arguments);
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(value), Box::new(Bitvector32Term::Constant(0))),
        true,
    );
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Statement(1),
        kind: ProgramPointKind::Entry,
    };
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                },
                CState::new(),
            );
        }
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::super::smart_closures::synthesize_surface_at_recorded_snapshots(
                &kernel,
                parameter_binding,
                &snapshots,
                &anchor,
            )
            .next()
        });
        let surface = surface.expect("the nearest snapshot should name the parameter");
        assert!(proposition_contains_at_expression(&surface));
        let state = CState::new();
        let lowered = lower_fixed_state_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            parameter_binding,
            FixedStateFrame::new(&state, &state, None, &snapshots),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
        )
        .expect("the candidate must lower against the selected snapshot");
        assert_eq!(
            lowered, kernel,
            "snapshot spelling must preserve the exact premise"
        );
        let height = usize::BITS - size.leading_zeros();
        assert!(
            work <= 32 * height as usize + 128,
            "size {size}: {work} synthesis work"
        );
        crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            assert!(
                super::super::super::smart_closures::synthesize_surface_at_recorded_snapshots(
                    &kernel,
                    parameter_binding,
                    &snapshots,
                    &anchor
                )
                .next()
                .is_none()
            );
        });
    }
}

#[test]
fn missing_snapshot_premise_spelling_has_bounded_history_search() {
    let parameters = syntax::parse_function("int32 noop() { return 0; }").unwrap();
    // No state or parameter names this symbolic value. Every synthesis probe
    // misses, exercising the exhaustive-history fallback rather than the
    // successful first-candidate case.
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(8_178_903))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                },
                CState::new(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Statement(size / 2),
            kind: ProgramPointKind::Entry,
        };
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut candidates =
                super::super::super::smart_closures::synthesize_surface_at_recorded_snapshots(
                    &kernel,
                    ParameterBinding::new(parameters.parameters(), &[]),
                    &snapshots,
                    &anchor,
                );
            let count = candidates.by_ref().count();
            assert!(candidates.next().is_none());
            count
        });
        assert_eq!(count, 0);
        let height = usize::BITS - size.leading_zeros();
        assert!(
            work <= 256 * height as usize + 8192,
            "size {size}: {work} work"
        );
    }
}

#[test]
fn snapshot_premise_candidates_stop_on_deterministic_work_exhaustion() {
    use crate::instrumentation::{TacticEvent, TacticWorkLimits, VerificationEvent};
    let parameters = syntax::parse_function("int32 noop(int32 x) { return x; }").unwrap();
    let value = Bitvector32Term::Variable(Variable(8_178_902));
    let arguments = vec![CExpression::Value(CValue::Int32(value.clone()))];
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(value), Box::new(Bitvector32Term::Constant(0))),
        true,
    );
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Statement(0),
        kind: ProgramPointKind::Entry,
    };
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                },
                CState::new(),
            );
        }
        // Exhaust before the independent snapshot-candidate search cap. A
        // normal bounded search miss need not consume the tactic budget.
        let limit = 8;
        let ((candidates, work), events) = crate::instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: limit,
                smart: limit,
                control: limit,
            },
            || {
                crate::instrumentation::collect(|| {
                    let tactic = TacticEvent {
                        source_tactic_path: None,
                        claim: "snapshot budget".into(),
                        tactic_index: 0,
                        tactic_name: "simp".into(),
                        class: "smart".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    crate::instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                    let measured = crate::instrumentation::measure_deterministic_work(|| {
                        let mut candidates =
                            super::super::super::smart_closures::synthesize_surface_at_recorded_snapshots(
                                &kernel,
                                ParameterBinding::new(parameters.parameters(), &arguments),
                                &snapshots,
                                &anchor,
                            );
                        let count = candidates.by_ref().count();
                        assert!(candidates.next().is_none());
                        count
                    });
                    crate::instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                    measured
                })
            },
        );
        assert!(
            candidates < size,
            "exhaustion must prevent visiting the whole history"
        );
        assert!(
            work <= limit + 16,
            "size {size}: {work} work after limit {limit}"
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, VerificationEvent::TacticWorkBudgetExceeded { .. })),
            "the work miss must retain its budget diagnosis"
        );
    }
}

#[test]
fn wide_bound_direct_rewrite_ignores_connected_ambient_equalities() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let x = Bitvector32Term::Variable(Variable(9_920_000));
    let y = Bitvector32Term::Variable(Variable(9_920_001));
    let bound = Bitvector32Term::UInt64Constant(22208);
    let equality = Proposition::ConditionIs(
        ConditionTerm::Bitvector64Equal(Box::new(x.clone()), Box::new(y.clone())),
        true,
    );
    let known = Proposition::ConditionIs(
        ConditionTerm::Bitvector64UnsignedLessThan(Box::new(y.clone()), Box::new(bound.clone())),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector64UnsignedLessThan(Box::new(x.clone()), Box::new(bound.clone())),
        true,
    );
    let expression = |name: &str| ContractExpression::CFragment(CExpression::Variable(name.into()));
    let equality_surface = ClickProposition::Comparison {
        left: expression("x"),
        operator: ComparisonOperator::Equal,
        right: expression("y"),
    };
    let goal_surface = ClickProposition::Comparison {
        left: expression("x"),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(CValue::UInt64(bound))),
    };
    let mut costs = Vec::new();
    for ambient in [0, 16, 64, 256, 1024] {
        let mut facts = vec![equality.clone(), known.clone()];
        for i in 0..ambient {
            facts.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(
                    Box::new(y.clone()),
                    Box::new(Bitvector32Term::Variable(Variable(9_921_000 + i))),
                ),
                true,
            ));
        }
        let mut surface_requirements = SurfacePropositionMap::default();
        surface_requirements
            .record_lowering(&equality_surface, &equality)
            .unwrap();
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: CMemory::new(),
            values: BTreeMap::from([
                ("x".into(), CValue::UInt64(x.clone())),
                ("y".into(), CValue::UInt64(y.clone())),
            ]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements,
        };
        let root = Proof::for_pure_goal_with_surface(
            "direct wide bound",
            &facts,
            goal.clone(),
            Some(goal_surface.clone()),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.try_indexed_goal_equality_rewrite_direct_closure(false)
        });
        let closed = closed.expect("one checked rewrite should expose the recorded bound");
        assert!(closed.is_complete());
        assert_eq!(closed.certificate().steps().len(), 2);
        assert!(matches!(
            &closed.certificate().steps()[0],
            ProofStep::Rewrite(_)
        ));
        assert!(matches!(
            &closed.certificate().steps()[1],
            ProofStep::Assumption
        ));
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0]),
        "{costs:?}"
    );
}

#[test]
fn loop_entry_wide_extent_guard_retains_its_own_source_and_scales() {
    let parsed = syntax::parse_function("void span(const uint8* buf, uint64 len) { }").unwrap();
    let pointer = Pointer::symbolic(Variable(812_000));
    let original = Bitvector32Term::Variable(Variable(812_001));
    let remaining =
        Bitvector32Term::uint64_subtract(original.clone(), Bitvector32Term::UInt64Constant(16));
    let extent =
        Bitvector32Term::uint64_add(Bitvector32Term::UInt64Constant(16), remaining.clone());
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(extent, Bitvector32Term::UInt64Constant(i64::MAX as u64)),
        true,
    );
    let obligation = crate::kernel::ProofObligation::new(goal.clone());
    let base = CExpression::Variable("buf".into());
    let start = CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(0)));
    let end = CExpression::Add(
        Box::new(CExpression::Value(CValue::UInt64(
            Bitvector32Term::UInt64Constant(16),
        ))),
        Box::new(CExpression::Variable("len".into())),
    );
    let surface = ClickProposition::Loadable {
        segment: ContractSegment {
            state: ContractSegmentState::Current,
            base: base.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::CFragment(base),
                start: ContractExpression::CFragment(start),
                end: ContractExpression::CFragment(end),
            },
        },
    };
    let arguments = vec![
        CExpression::Value(CValue::typed_pointer(pointer.clone(), CType::UInt8Pointer)),
        CExpression::Value(CValue::UInt64(original.clone())),
    ];
    let entry = CState::new()
        .with_local(
            "buf",
            CValue::typed_pointer(pointer.clone(), CType::UInt8Pointer),
        )
        .with_local("len", CValue::UInt64(original));
    let snapshots = RecordedSnapshots::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let mut work = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = entry
            .clone()
            .with_local("len", CValue::UInt64(remaining.clone()));
        for index in 0..size {
            state = state.with_local(format!("unused_{index}"), int32(index));
        }
        let facts = vec![goal.clone()];
        let root = Proof::for_fixed_state_frontier(
            "wide loop view guard",
            0,
            &facts,
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&entry, &state, None, &snapshots),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
            let scope = root
                .begin_loop_entry_goal(surface.clone(), &obligation)
                .unwrap();
            let before = scope.body().clone();
            let completed = before.apply_step(ProofStep::Assumption).unwrap();
            let retained = before.retain_completed_goal(&completed, &[]).unwrap();
            assert!(retained.facts().contains(&goal));
        });
        work.push(units);
    }
    assert!(
        work[3] <= work[0] * 3 + 128,
        "loop guard source walked unrelated locals: {work:?}"
    );
}

#[test]
fn completed_goal_retention_validates_current_source_after_stale_recording() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let entry_len = Bitvector32Term::Variable(Variable(813_000));
    let current_len =
        Bitvector32Term::uint64_subtract(entry_len.clone(), Bitvector32Term::UInt64Constant(16));
    let limit = Bitvector32Term::UInt64Constant(22208);
    let bound = |length| {
        Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(length, limit.clone()),
            true,
        )
    };
    let old_goal = bound(entry_len.clone());
    let current_goal = bound(current_len.clone());
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("len".into())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Value(CValue::UInt64(limit))),
    };
    let entry = CState::new().with_local("len", CValue::UInt64(entry_len));
    let snapshots = RecordedSnapshots::new();
    let mut surfaces = SurfacePropositionMap::default();
    surfaces.record_lowering(&surface, &old_goal).unwrap();
    let mut work = Vec::new();
    for size in [0, 16, 64, 256, 1024] {
        let mut state = entry
            .clone()
            .with_local("len", CValue::UInt64(current_len.clone()));
        for index in 0..size {
            state = state.with_local(format!("unused_{index}"), int32(index));
        }
        let facts = vec![old_goal.clone(), current_goal.clone()];
        let root = Proof::for_fixed_state_surface_goal(
            "current retained bound",
            0,
            &facts,
            current_goal.clone(),
            surface.clone(),
            ParameterBinding::default(),
            &entry,
            &state,
            &snapshots,
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        assert_eq!(
            root.lower_surface_proposition(&surface, "stale source")
                .unwrap(),
            old_goal
        );
        let completed = root.apply_step(ProofStep::Assumption).unwrap();
        let (retained, units) = crate::instrumentation::measure_deterministic_work(|| {
            root.retain_completed_goal(&completed, &[]).unwrap()
        });
        assert!(retained.facts().contains(&current_goal));
        work.push(units);
        let empty_surfaces = SurfacePropositionMap::default();
        let wrong = Proof::for_fixed_state_surface_goal(
            "mismatched retained bound",
            0,
            std::slice::from_ref(&old_goal),
            old_goal.clone(),
            surface.clone(),
            ParameterBinding::default(),
            &entry,
            &state,
            &snapshots,
            &empty_surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let completed = wrong.apply_step(ProofStep::Assumption).unwrap();
        assert!(wrong.retain_completed_goal(&completed, &[]).is_err());
    }
    assert!(
        work[4] <= work[0] * 3 + 128,
        "retention walked unrelated locals: {work:?}"
    );
}
