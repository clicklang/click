// Scaling tests of `src/kernel/tests/resource_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn normalized_resource_spec_evaluation_preserves_indexed_lookup_scaling() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let names = (0..size)
                .map(|index| format!("token{index}"))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts(
                names
                    .iter()
                    .cloned()
                    .map(|name| CResourceFact::own_token(name, Vec::new())),
            );
            let spec = CResourceSpec::declared(
                ResourceFamily::Token,
                CResourceAccessMode::Own,
                names[size / 2].clone(),
                Vec::new(),
                Vec::new(),
                CResourceTransferRole::Consume,
                CResourceSnapshot::Current,
            )
            .unwrap();
            let state = CState::new().with_resource_context(context);
            let assumptions = PureFactContext::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut budget = ExecutionBudget::default();
                let fact = crate::kernel::functions::evaluate_function_resource_spec(
                    &state,
                    &spec,
                    &assumptions,
                    &mut budget,
                )
                .unwrap()
                .unwrap();
                assert!(state.resources().satisfies_fact(&fact, &assumptions));
                let remaining = state
                    .resources()
                    .clone()
                    .without_fact_delaying_normalization(&fact, &assumptions)
                    .expect("indexed lookup finds the normalized token");
                assert_eq!(remaining.facts().len(), size - 1);
            });
            assert!(work > 0);
            (size, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3) + 64),
        "normalized resource evaluation is superlinear: {samples:?}"
    );
}

#[test]
fn aliased_memory_consumption_does_not_walk_the_pointer_class() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let pointer = |i| Pointer::symbolic(Variable(800_000 + i));
        let cell = |base| {
            CMemoryRange::new(
                base,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )
        };
        let mut assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(cell(pointer(size))));
        for i in 1..=size {
            assumptions = assumptions
                .assume_condition(ConditionTerm::pointer_equal(pointer(0), pointer(i)), true);
        }
        // Establish the paired snapshot once. Subsequent queries and forks
        // must share its persistent index, rather than enumerate aliases.
        resources = resources
            .without_fact_incrementally(&CResourceFact::view_memory(cell(pointer(0))), &assumptions)
            .unwrap();
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.without_fact_incrementally(
                &CResourceFact::own_memory(cell(pointer(0))),
                &assumptions,
            )
        });
        assert!(remaining.unwrap().facts().is_empty());
        samples.push((size, work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 3 + 64,
        "fixed consumption walked the growing alias class: {samples:?}"
    );
}

#[test]
fn paired_memory_index_updates_move_the_smaller_resource_payload() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let root = Pointer::symbolic(Variable(820_000));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    Pointer {
                        block: root.block.clone(),
                        offset: PointerOffsetTerm::Constant(i as i64 * 4),
                    },
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )));
        }
        let mut assumptions = PureFactContext::new();
        resources.synchronize_memory_equalities(&assumptions);
        let (assumptions, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 1..=size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::pointer_equal(
                        root.clone(),
                        Pointer::symbolic(Variable(820_000 + i)),
                    ),
                    true,
                );
                resources.synchronize_memory_equalities(&assumptions);
            }
            assumptions
        });
        let required = CResourceFact::own_memory(CMemoryRange::new(
            Pointer::symbolic(Variable(820_000 + size)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let (remaining, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.without_fact_incrementally(&required, &assumptions)
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work, query_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 6 + 128,
            "class updates repeatedly moved a large payload: {samples:?}"
        );
        assert!(
            pair[1].2 <= pair[0].2 * 2 + 64,
            "lookup scanned unrelated addresses: {samples:?}"
        );
    }
}

#[test]
fn paired_memory_consumption_indexes_disjoint_spans_at_one_base() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(840_000));
        let alias = Pointer::symbolic(Variable(840_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    owner.clone(),
                    Bitvector32Term::Constant(i as u32 * 2),
                    Bitvector32Term::Constant(i as u32 * 2 + 1),
                )));
        }
        let assumptions = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&assumptions);
        let required = CResourceFact::own_memory(CMemoryRange::new(
            alias,
            Bitvector32Term::Constant(size as u32),
            Bitvector32Term::Constant(size as u32 + 1),
        ));
        let ((remaining, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.without_fact_incrementally(&required, &assumptions)
            })
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work, map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 64,
        "consumption scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128,
        "index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn indexed_memory_lookup_ignores_unrelated_pointer_parameters() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(870_000 + id)),
        };
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new(at(i), 0u32.into(), 1u32.into()),
            ));
        }
        let limit = Bitvector32Term::Variable(Variable(871_100));
        let index = Bitvector32Term::Variable(Variable(869_000));
        let symbolic = resources
            .clone()
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                at(size),
                0u32.into(),
                limit.clone(),
            )));
        let concrete = resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            at(size),
            0u32.into(),
            4u32.into(),
        )));
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_than(index.clone(), limit), true);
        symbolic.synchronize_memory_equalities(&facts);
        let query = at(size).offset_by_elements(index, 4);
        let required =
            |base| CResourceFact::view_memory(CMemoryRange::new(base, 1u32.into(), 2u32.into()));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(symbolic.permits_memory_read(&query, 4, &facts));
                assert!(!symbolic.permits_memory_read(&at(size + 1), 4, &facts));
                assert!(concrete.satisfies_memory_fact_structurally(&required(at(size))));
                assert!(!concrete.satisfies_memory_fact_structurally(&required(at(size + 1))));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "structural lookup scanned unrelated parameters: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "structural index scanned unrelated parameters: {samples:?}"
    );
}

#[test]
fn write_candidates_do_not_scan_unrelated_memory_ranges() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(860_000));
        let alias = Pointer::symbolic(Variable(860_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    owner.clone(),
                    (i as u32 * 8).into(),
                    (i as u32 * 8 + 4).into(),
                    1,
                ),
            ));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let facts = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |offset| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let query = |offset| {
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    resources
                        .memory_write_range(&at(offset), 4, &facts)
                        .is_some()
                })
            })
        };
        let ((hit, work), map_work) = query(size as i64 * 4);
        let ((miss, miss_work), miss_map_work) = query(size as i64 * 4 + 4);
        assert!(hit);
        assert!(!miss);
        assert!(
            resources
                .memory_write_range(&at(size as i64 * 4), 4, &empty)
                .is_none()
        );
        samples.push((size, work, map_work, miss_work, miss_map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 32 && samples[2].3 <= samples[0].3 * 2 + 32,
        "write checks scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128 && samples[2].4 <= samples[0].4 * 3 + 128,
        "write index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn owned_fragment_reservation_scales_with_fragments_not_ambient_memory() {
    for base in [
        Pointer::symbolic(Variable(862_010)),
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(862_011)), 4),
        },
    ] {
        let fact = |start: u32, end: u32| {
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                base.clone(),
                start.into(),
                end.into(),
                1,
            ))
        };
        let measure = |fragments: u32, ambient: u32| {
            let mut resources = ResourceContext::new();
            for i in 0..fragments {
                resources = resources.unchecked_with_fact(fact(i * 4, i * 4 + 4));
            }
            for i in 0..ambient {
                resources = resources.unchecked_with_fact(fact(8192 + i * 8, 8196 + i * 8));
            }
            let facts = PureFactContext::new();
            resources.synchronize_memory_equalities(&facts);
            let required = fact(0, fragments * 4);
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert!(
                        resources
                            .directly_supporting_owned_entry(&required, &facts)
                            .is_none()
                    );
                    let (_, supports) = resources
                        .reserve_owned_memory_fragments(&required, &facts)
                        .unwrap();
                    assert_eq!(supports.len(), fragments as usize);
                })
            });
            (work, map_work)
        };
        let ambient = [16, 64, 256, 1024].map(|n| measure(4, n));
        assert!(
            ambient[3].0 <= ambient[0].0 * 2 + 32,
            "reservation scanned unrelated memory: {ambient:?}"
        );
        assert!(
            ambient[3].1 <= ambient[0].1 * 4 + 256,
            "reservation index scanned unrelated memory: {ambient:?}"
        );
        let fragments = [8, 32, 128].map(|n| measure(n, 0));
        assert!(
            fragments[2].0 <= fragments[0].0 * 20 + 128,
            "reservation is superlinear: {fragments:?}"
        );
        assert!(
            fragments[2].1 <= fragments[0].1 * 40 + 1024,
            "reservation index is superlinear: {fragments:?}"
        );
        eprintln!("fragment reservation at {base:?}: ambient {ambient:?}; fragments {fragments:?}");
    }
}

#[test]
fn specification_read_candidates_do_not_scan_unrelated_memory_ranges() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(850_000));
        let alias = Pointer::symbolic(Variable(850_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    owner.clone(),
                    Bitvector32Term::Constant(i as u32 * 2),
                    Bitvector32Term::Constant(i as u32 * 2 + 1),
                )));
        }
        let facts = PureFactContext::new();
        resources.synchronize_memory_equalities(&facts);
        let facts =
            facts.assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |index| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(index * 4),
        };
        let ((allowed, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.permits_memory_read(&at(size as i64), 4, &facts)
            })
        });
        assert!(allowed);
        let ((denied, miss_work), miss_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    resources.permits_memory_read(&at(size as i64 + 1), 4, &facts)
                })
            });
        assert!(!denied, "a gap between ranges is not readable");
        samples.push((size, work, map_work, miss_work, miss_map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 32 && samples[2].3 <= samples[0].3 * 2 + 32,
        "read checks scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128 && samples[2].4 <= samples[0].4 * 3 + 128,
        "read index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
fn stored_child_arguments_require_owned_memory() {
    let (instance, mut definition, state) = recursive_child_fixture();
    let arm = &mut definition.matched.as_mut().unwrap().arms[1];
    let Some(segment) = arm.contains[0].memory_segment_mut() else {
        unreachable!()
    };
    segment.end = c_int32_literal(2); // one LP64 pointer
    arm.children[0].arguments = vec![SpecExpression::CExpression(CExpression::TypedLoad {
        pointer: Box::new(c_variable("p")),
        value_type: CType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    })];
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let assumptions = PureFactContext::new();
    let rewrite = |state: &CState,
                   definition: &CCompositeResourceDefinition,
                   assumptions: &PureFactContext,
                   unfold| {
        crate::kernel::rewrite_resource_instance_selecting_children(
            state,
            &instance,
            definition,
            std::slice::from_ref(definition),
            assumptions,
            unfold,
            Some(&children),
        )
    };
    let open = rewrite(&state, &definition, &assumptions, true)
        .unwrap()
        .state;
    rewrite(&open, &definition, &assumptions, false).unwrap();
    let mut unreadable = definition.clone();
    unreadable.matched.as_mut().unwrap().arms[1]
        .contains
        .clear();
    // Even a caller using permissive specification lowering cannot grant
    // child construction an unchecked read outside the owned body.
    assert!(
        rewrite(
            &state,
            &unreadable,
            &assumptions.clone().allow_symbolic_contract_loads(),
            true
        )
        .is_err()
    );
    let mut missing = open.clone();
    missing.resources = ResourceContext::new().unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_none())
            .cloned(),
    );
    assert!(rewrite(&missing, &definition, &assumptions, false).is_err());
    assert!(rewrite(&open, &unreadable, &assumptions, false).is_err());
    let concrete = Pointer {
        block: "unowned-link".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let concrete_state = state.clone().with_memory(
        CMemory::new()
            .with_block("unowned-link", 8)
            .store(concrete.clone(), CValue::pointer(Pointer::null())),
    );
    let mut concrete_definition = definition.clone();
    concrete_definition.matched.as_mut().unwrap().arms[1].children[0].arguments =
        vec![SpecExpression::CExpression(CExpression::TypedLoad {
            pointer: Box::new(c_pointer_value(concrete.clone())),
            value_type: CType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        })];
    // A materialized C block is not authority to read a link outside the
    // resource body, even though ordinary C execution can access that block.
    assert!(rewrite(&concrete_state, &concrete_definition, &assumptions, true).is_err());
    concrete_definition.matched.as_mut().unwrap().arms[1]
        .contains
        .push(CResourceSpec::owned_memory(CMemorySegment {
            base: c_pointer_value(concrete),
            start: c_int32_literal(0),
            end: c_int32_literal(2),
            element_width: 4,
            guard: None,
        }));
    rewrite(&concrete_state, &concrete_definition, &assumptions, true).unwrap();
    // The parent's concrete memory may not also be owned by the surrounding
    // frame: unfolding must reject overlapping ownership.
    let mut overlap = state.clone();
    overlap.resources = overlap.resources.unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_some())
            .cloned(),
    );
    assert!(rewrite(&overlap, &definition, &assumptions, true).is_err());
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut framed = open.clone();
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            framed.resources = framed
                .resources
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    other,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite(&framed, &definition, &assumptions, false)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn instance_fold_preserves_memory_pieces_without_scanning_unrelated_resources() {
    let (instance, mut definition, _) = instance_memory_fixture();
    definition.contains = (0..3)
        .map(|i| {
            CResourceSpec::owned_memory(CMemorySegment {
                base: c_variable("p"),
                start: c_int32_literal(i),
                end: c_int32_literal(i + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    let CValue::Pointer(value) = instance.arguments()[0].as_c_value().unwrap() else {
        unreachable!()
    };
    let pointer = value.pointer().clone();
    let pieces = (0..3)
        .map(|i| {
            CResourceFact::own_memory(CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(i),
                Bitvector32Term::Constant(i + 1),
            ))
        })
        .collect::<Vec<_>>();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut resources = ResourceContext::new().unchecked_with_facts(pieces.iter().cloned());
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    other,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )));
        }
        let state = CState::new().with_resource_context(resources);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&[]),
            )
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn independent_children_kernel_work_ignores_unrelated_instances() {
    let (instance, definition, initial) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 10_000..10_000 + size {
            state
                .resources
                .record_instance_consumption(Variable(identity), Some(InstanceConsumption::Unfold));
        }
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let open = crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                true,
                Some(&children),
            )
            .unwrap()
            .state;
            assert!(open.instance_field_scope.is_empty());
            crate::kernel::rewrite_resource_instance_selecting_children(
                &open,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&children),
            )
            .unwrap()
        });
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn resource_match_constructor_index_tracks_evidence_and_scales_locally() {
    let ty = resource_index_type("Mark", vec![]);
    let model = resource_index_variable(&ty, 7);
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![],
        },
    };
    let equality = Proposition::Equal(
        Term::Algebraic(model.clone()),
        Term::Algebraic(constructor.clone()),
    );
    let reversed = Proposition::Equal(
        Term::Algebraic(constructor.clone()),
        Term::Algebraic(model.clone()),
    );
    for fact in [equality.clone(), reversed] {
        let mut assumptions = PureFactContext::new().assume_proposition(fact.clone());
        assert_eq!(
            assumptions.known_algebraic_constructor(&model),
            Some(constructor.clone())
        );
        assumptions.remove_proposition_fact(&fact);
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
        assumptions.insert_proposition_fact(fact.clone());
        assumptions.retain_proposition_facts(|entry| entry != &fact);
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
        assumptions.insert_proposition_fact(fact);
        assumptions.clear_proposition_facts();
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
    }
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(equality.clone());
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(Proposition::Equal(
                Term::Algebraic(resource_index_variable(&ty, index)),
                Term::Algebraic(constructor.clone()),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                assumptions.known_algebraic_constructor(&model),
                Some(constructor.clone())
            );
        });
        assert!(work > 0, "constructor lookup must count candidate visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn instance_memory_fold_work_is_local_to_the_selected_instance() {
    let (instance, definition, initial) = instance_memory_fixture();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (open, _) =
                rewrite_resource_instance(&state, &instance, &definition, &assumptions, true)
                    .unwrap();
            assert!(open.resource_instance_fields(instance.identity()).is_none());
            rewrite_resource_instance(&open, &instance, &definition, &assumptions, false).unwrap()
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] + 128,
            "unrelated handle scaling: {samples:?}"
        );
    }
}

#[test]
fn resource_instance_lookup_and_transfer_scale_by_identity() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 1);
    let n = resource_index_variable(&ty, 2);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(m.clone()),
        Term::Algebraic(n.clone()),
    ));
    let selected = CResourceFact::own(CResource::Instance(field_instance(1, n, 0)));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (context, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for identity in 1..=size {
                context = context
                    .try_compose_into_valid_context_delaying_normalization(
                        [CResourceFact::own(CResource::Instance(field_instance(
                            identity,
                            m.clone(),
                            0,
                        )))],
                        &assumptions,
                    )
                    .unwrap();
            }
            context
        });
        assert!(context.shares_storage_with(&context.clone()));
        let bindings = std::sync::Arc::new(
            (1..=size)
                .map(|id| (Variable(size + id), Variable(id)))
                .collect(),
        );
        let mut state = CState::new().with_resource_context(context.clone());
        state.resource_bindings = Some(bindings);
        let snapshot = state.clone();
        assert!(std::sync::Arc::ptr_eq(
            state.resource_bindings.as_ref().unwrap(),
            snapshot.resource_bindings.as_ref().unwrap()
        ));
        let (remaining, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                state
                    .owned_resource_instance(Variable(size + 1))
                    .unwrap()
                    .identity(),
                Variable(1)
            );
            // A formal absent from the map must not fall back to a caller ID.
            assert!(state.owned_resource_instance(Variable(1)).is_none());
            let mut missing = snapshot.clone();
            missing.resources = ResourceContext::new();
            assert!(
                missing
                    .owned_resource_instance(Variable(size + 1))
                    .is_none()
            );
            assert!(context.owned_instance(Variable(1)).is_some());
            assert!(context.owned_instance(Variable(size + 1)).is_none());
            assert!(context.satisfies_fact(&selected, &assumptions));
            context
                .without_fact_delaying_normalization(&selected, &assumptions)
                .unwrap()
        });
        assert_eq!(remaining.facts().len(), size as usize - 1);
        samples.push((build_work, query_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 3 + 16,
            "instance build scaling: {samples:?}"
        );
        assert!(
            pair[1].1 <= pair[0].1 + 64,
            "fixed identity query scaling: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_share_snapshots_and_scale_with_indexed_context() {
    let ty = resource_index_type("Mark", vec![]);
    let selected = CResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_000),
        false,
    ));
    let renamed = CResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_001),
        false,
    ));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(resource_index_variable(&ty, 991_000)),
        Term::Algebraic(resource_index_variable(&ty, 991_001)),
    ));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (_, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for i in 0..size {
                let fact = CResourceFact::own(CResource::Token {
                    name: format!("indexed_{i}"),
                    arguments: vec![AlgebraicValue::Algebraic(resource_index_variable(
                        &ty,
                        992_000 + i,
                    ))]
                    .into(),
                });
                let cloned = fact.clone();
                let (CResource::Token { arguments: a, .. }, CResource::Token { arguments: b, .. }) =
                    (fact.resource(), cloned.resource())
                else {
                    unreachable!()
                };
                assert!(std::sync::Arc::ptr_eq(a, b));
                context = context.unchecked_with_fact(fact);
            }
            context
        });
        let context = unrelated_token_context(size as usize).unchecked_with_fact(selected.clone());
        let (remaining, transfer_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&renamed, &assumptions)
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize);
        samples.push((size, build_work, transfer_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3).saturating_add(16),
            "building ADT-indexed resources: {samples:?}"
        );
        assert!(
            pair[1].2 <= pair[0].2.saturating_mul(2).saturating_add(16),
            "fixed indexed transfer: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_exact_transfer_scales_with_same_family_indices() {
    let ty = resource_index_type("Mark", vec![]);
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let selected = CResourceFact::own(indexed_resource(resource_index_variable(&ty, 1), false));
        let context = ResourceContext::new().unchecked_with_facts((1..=size).map(|id| {
            CResourceFact::own(indexed_resource(resource_index_variable(&ty, id), false))
        }));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&selected, &PureFactContext::new())
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(16),
            "exact ADT index lookup: {samples:?}"
        );
    }
}

#[test]
fn zero_resource_identity_ignores_unrelated_resources() {
    let quantity = Bitvector32Term::Variable(Variable(911_000));
    let intermediate = Bitvector32Term::Variable(Variable(911_001));
    let assumptions = PureFactContext::new()
        .assume_proposition(equality(quantity.clone(), intermediate.clone()))
        .assume_proposition(equality(intermediate, Bitvector32Term::Constant(0)));
    let required = CResourceFact::own_quantity(
        CResource::Token {
            name: "empty".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity,
    );
    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .without_fact_delaying_normalization(&required, &assumptions)
            });
            assert_eq!(remaining.expect("zero consumption should succeed"), context);
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "zero-resource identity work changed with unrelated resources: {samples:?}"
    );
}

#[test]
fn owned_support_lookup_scales_with_unrelated_supported_facts() {
    let authority = CResourceFact::own_composite("authority".to_string(), Vec::new());
    let projected = CResourceFact::view_composite("nested".to_string(), vec![int32(7)]);
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size)
            .unchecked_with_fact(authority.clone())
            .unchecked_with_supported_facts(&authority, [projected.clone()]);
        let (support, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .directly_supporting_owned_entry(&projected, &PureFactContext::new())
                .map(|(_, support)| support)
        });
        assert_eq!(support, Some(&authority));
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(16),
            "indexed support lookup scanned unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn cached_support_updates_ignore_unrelated_cached_supports() {
    let target = CResourceFact::own_composite("target_cache".to_string(), Vec::new());
    let mut samples = Vec::new();
    for size in [4_usize, 8, 16, 32] {
        let mut context = ResourceContext::new();
        for index in 0..size {
            let support = CResourceFact::own_composite(format!("cached_{index}"), Vec::new());
            context = context.unchecked_with_fact(support.clone());
            let occurrence = context.owned_occurrences_for_fact(&support)[0];
            context = context.with_cached_supported_expansion_for_occurrence(
                occurrence,
                &support,
                vec![CResourceFact::own_token(
                    format!("body_{index}"),
                    Vec::new(),
                )],
            );
        }
        context = context.unchecked_with_fact(target.clone());
        let target_occurrence = context.owned_occurrences_for_fact(&target)[0];
        let before_cache_allocations = crate::persistent::persistent_node_allocations();
        let (context, cache_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.with_cached_supported_expansion_for_occurrence(
                target_occurrence,
                &target,
                vec![CResourceFact::own_token(
                    "target_body".to_string(),
                    Vec::new(),
                )],
            )
        });
        let cache_allocations =
            crate::persistent::persistent_node_allocations() - before_cache_allocations;
        let before_remove_allocations = crate::persistent::persistent_node_allocations();
        let (remaining, remove_work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .without_exact_representation_for_occurrence(target_occurrence)
                .expect("the target support should be removable")
        });
        let remove_allocations =
            crate::persistent::persistent_node_allocations() - before_remove_allocations;
        assert_eq!(remaining.cached_supported_expansions(&target).len(), 0);
        samples.push((
            size,
            cache_work,
            remove_work,
            cache_allocations,
            remove_allocations,
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8)
                && pair[1].2 <= pair[0].2.saturating_mul(2).saturating_add(8),
            "support cache updates scanned unrelated cached authorities: {samples:?}"
        );
    }
    let base_height = usize::BITS as usize - samples[0].0.leading_zeros() as usize;
    for (size, _, _, cache_allocations, remove_allocations) in samples {
        let height = usize::BITS as usize - size.leading_zeros() as usize;
        // A global canonical-map rebuild grows with every unrelated cache;
        // this logarithmic bound rejects that shape while allowing the
        // persistent paths for the affected support bucket.
        let bound = 32 * (height - base_height + 1);
        assert!(
            cache_allocations <= bound && remove_allocations <= bound,
            "support cache updates scaled with unrelated cache count at size {size}: cache={cache_allocations}, remove={remove_allocations}, bound={bound}"
        );
    }
}

#[test]
fn support_removal_visits_only_the_supported_projections() {
    const PROJECTION_COUNT: usize = 8;
    for size in [16_usize, 64, 256, 1024, 4096] {
        let authority =
            CResourceFact::own_composite("authority".to_string(), vec![int32(size as u32)]);
        let projections = (0..PROJECTION_COUNT)
            .map(|index| {
                CResourceFact::view_token(format!("projection_{index}"), vec![int32(size as u32)])
            })
            .collect::<Vec<_>>();
        let context = unrelated_token_context(size)
            .unchecked_with_fact(authority.clone())
            .unchecked_with_supported_facts(&authority, projections.clone());
        let ancestor = context.clone();

        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .without_exact_representation(&authority)
                .expect("the authority should be removable")
        });
        assert_eq!(
            work, PROJECTION_COUNT,
            "retiring support in a size-{size} context must visit only its projections"
        );
        assert_eq!(remaining.facts().len(), size);
        assert_eq!(ancestor.facts().len(), size + PROJECTION_COUNT + 1);
        for projection in projections {
            assert!(!remaining.satisfies_fact(&projection, &PureFactContext::new()));
        }
    }
}

#[test]
fn exact_resource_lookup_is_indexed_after_context_construction() {
    let required = CResourceFact::own_token("target".to_string(), vec![int32(0)]);
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size).unchecked_with_fact(required.clone());
        assert!(context.satisfies_fact(&required, &PureFactContext::new()));
        let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&required, &PureFactContext::new())
        });
        assert!(satisfied);
        assert_eq!(
            work, 0,
            "indexed exact lookup scanned a size-{size} context"
        );
    }
}

#[test]
fn exact_owned_resource_satisfies_view_without_entailment_scan() {
    let range = memory_range(
        Pointer {
            block: "owned-view-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let owned = CResourceFact::own_memory(range.clone());
    let required = CResourceFact::view_memory(range);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size).unchecked_with_fact(owned.clone());
            assert!(context.satisfies_fact(&required, &PureFactContext::new()));
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "exact ownership-to-view lookup should ignore unrelated resources: {samples:?}"
    );
}

/// A composite held under another spelling of its pointer is found among
/// the held composites whose pointer is related to the required one, not by
/// checking entailment against every held composite of the shape: a fold of
/// one heap object beside many costs the same at every size.
#[test]
fn nonexact_composite_entailment_ignores_unrelated_instances_of_the_shape() {
    let object = |index: u64| Pointer::symbolic(Variable(783_000 + index));
    let boxed = |pointer: Pointer| {
        CResourceFact::own_composite("boxed".into(), vec![CValue::pointer(pointer)])
    };
    let alias = Pointer::symbolic(Variable(782_999));
    let work = [16u64, 64, 256].map(|size| {
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| boxed(object(index))));
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(CPointerValue::new(alias.clone(), CType::Int32Pointer), CPointerValue::new(object(size - 1), CType::Int32Pointer)),
            true,
        );
        let (held, used) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&boxed(alias.clone()), &assumptions)
        });
        assert!(held, "size={size}");
        used
    });
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + 2),
        "composite entailment grows with unrelated instances of its shape: {work:?}"
    );
}

#[test]
fn nonexact_memory_entailment_ignores_unrelated_blocks() {
    let target_base = Pointer {
        block: "target-block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let required = CResourceFact::view_memory(memory_range(target_base.clone(), 2, 6));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::view_memory(memory_range(
                        Pointer {
                            block: format!("unrelated-{index}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        8,
                    ))
                }))
                .unchecked_with_fact(CResourceFact::own_memory(memory_range(
                    target_base.clone(),
                    0,
                    8,
                )));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed memory entailment should not inspect unrelated blocks: {samples:?}"
    );
}

#[test]
fn unrelated_resource_normalization_has_linear_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), size);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn adjacent_memory_normalization_has_linearithmic_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    index as u32,
                    index as u32 + 1,
                ))
            }));
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "adjacent resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn disjoint_concrete_range_validity_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            }));
            let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.validity_error(&PureFactContext::new())
            });
            assert!(error.is_none());
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "concrete range validation is superlinear: {samples:?}"
        );
    }
}

#[test]
fn observable_structural_separation_does_not_materialize_owned_pairs() {
    for same_base in [false, true] {
        let samples = [16, 32, 64, 128]
            .into_iter()
            .map(|size| {
                let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_memory(memory_range(
                        Pointer {
                            block: if same_base {
                                "shared_block".into()
                            } else {
                                format!("block_{index}").into()
                            },
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        if same_base { (index * 2) as u32 } else { 0 },
                        if same_base { (index * 2 + 1) as u32 } else { 1 },
                    ))
                }));
                let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .observable_facts(&PureFactContext::new())
                        .expect("structurally disjoint memory ranges should compose")
                });
                assert_eq!(facts.len(), 1, "size-{size} projection materialized pairs");
                assert!(matches!(facts[0], Proposition::CResourceComposition(_)));
                assert!(
                    PureFactContext::new().proves(&Proposition::CResourceSeparate {
                        left: Box::new(context.facts()[0].resource().clone()),
                        right: Box::new(context.facts()[size - 1].resource().clone()),
                    })
                );
                (size, work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "observable resource projection is superlinear: {samples:?}"
            );
        }
    }
}

#[test]
fn inserting_a_disjoint_concrete_range_uses_interval_neighbors() {
    for size in [16, 32, 64, 128] {
        let base = Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            CResourceFact::own_memory(memory_range(
                base.clone(),
                (index * 2) as u32,
                (index * 2 + 1) as u32,
            ))
        }));
        let next =
            CResourceFact::own_memory(memory_range(base, (size * 2) as u32, (size * 2 + 1) as u32));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.try_compose_into_valid_context_delaying_normalization(
                std::iter::once(next),
                &PureFactContext::new(),
            )
        });
        assert!(result.is_ok());
        assert!(
            work <= size + 4,
            "indexed insertion did too much work for {size} existing ranges: {work}"
        );
    }
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn installing_a_certified_resource_group_does_not_recheck_internal_pairs() {
    let base = Pointer {
        block: "certified_group".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let facts = (0..size)
            .map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            })
            .collect::<Vec<_>>();
        ResourceContext::new()
            .try_compose_with_facts(facts.clone(), &PureFactContext::new())
            .expect("the resource group must be valid before it is certified");
        let (installed, work) = crate::instrumentation::measure_deterministic_work(|| {
            ResourceContext::new()
                .try_compose_certified_group_into_valid_context_delaying_normalization(
                    facts,
                    &PureFactContext::new(),
                )
        });
        assert!(installed.is_ok());
        // Installation now also closes each explicit span into the address
        // graph, including the complete-address shift for displaced starts.
        // Bound that fixed per-input work and its growth; internal pair
        // comparisons would grow quadratically across these sizes.
        assert!(
            work <= 96 * size,
            "installing a certified size-{size} group rechecked its internal pairs: {work}"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "certified installation grew superlinearly: {samples:?}"
    );
}

#[test]
fn resource_consumption_ignores_unrelated_exact_shapes() {
    let required = CResourceFact::view_token("target".to_string(), vec![int32(7)]);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
                }))
                .unchecked_with_fact(CResourceFact::own_token(
                    "target".to_string(),
                    vec![int32(7)],
                ));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.without_fact_delaying_normalization(&required, &PureFactContext::new())
            });
            assert!(remaining.is_some());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed token consumption should not inspect unrelated resource shapes: {samples:?}"
    );
}

#[test]
fn incremental_quantity_consumption_normalizes_only_the_exact_resource_bucket() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let target_resource = CResource::Token {
            name: "shared_name".to_string(),
            arguments: vec![int32(size + 1).into()].into(),
        };
        let unit = CResourceFact::Own(
            target_resource.clone(),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let required =
            CResourceFact::own_quantity(target_resource.clone(), Bitvector32Term::Constant(2));
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_token("shared_name".to_string(), vec![int32(index)])
            }))
            .unchecked_with_fact(unit.clone())
            .unchecked_with_fact(unit.clone());
        let ancestor = context.clone();
        assert!(context.storage.materialized.get().is_none());

        let before = crate::persistent::persistent_node_allocations();
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .clone()
                .without_fact_incrementally(&required, &PureFactContext::new())
        });
        let remaining = remaining.expect("two retained units should satisfy quantity two");
        samples.push((
            size,
            usize::BITS as usize - (size as usize).leading_zeros() as usize,
            crate::persistent::persistent_node_allocations() - before,
            work,
        ));
        assert!(!remaining.satisfies_fact(&unit, &PureFactContext::new()));
        assert!(
            remaining.contains_exact_representation(&CResourceFact::own_token(
                "shared_name".to_string(),
                vec![int32(size / 2)],
            ))
        );
        assert!(remaining.storage.materialized.get().is_none());
        assert_eq!(
            ancestor
                .storage
                .index
                .exact
                .get(&unit)
                .map_or(0, |entries| entries.len()),
            2,
            "incremental consumption must leave its ancestor unchanged"
        );
        assert!(ancestor.shares_storage_with(&context));
    }

    let (_, base_height, base_allocations, base_work) = samples[0];
    for (size, height, allocations, work) in samples {
        let allocation_bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} incremental quantity consumption allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(
            work <= base_work + 2,
            "size {size} incremental quantity consumption used {work} deterministic units (base {base_work})"
        );
    }

    let unit = CResourceFact::own_token("target".to_string(), Vec::new());
    let context = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit);
    let unavailable = CResourceFact::own_quantity(
        CResource::Token {
            name: "target".to_string(),
            arguments: Vec::new().into(),
        },
        Bitvector32Term::Constant(3),
    );
    assert!(
        context
            .clone()
            .without_fact_incrementally(&unavailable, &PureFactContext::new())
            .is_none(),
        "failed incremental consumption must not manufacture a larger quantity"
    );
    assert_eq!(context.facts().len(), 2);
}

#[test]
fn cross_block_alias_owner_lookup_ignores_unrelated_bases() {
    let target = Pointer {
        block: PointerBlock::Symbolic(Variable(41_100)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(target.clone(), argument.clone()),
        true,
    );
    let query = CResourceFact::own_memory(memory_range(argument, 0, 1));
    let samples = [8usize, 16, 32, 64].map(|size| {
        let mut facts = vec![CResourceFact::own_memory(memory_range(
            target.clone(),
            0,
            1,
        ))];
        facts.extend((1..size).map(|index| {
            CResourceFact::own_memory(memory_range(
                Pointer {
                    block: target.block.clone(),
                    offset: PointerOffsetTerm::Constant((index * 8) as i64),
                },
                0,
                1,
            ))
        }));
        let existing = ResourceContext::new().unchecked_with_facts(facts);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            existing.try_compose_into_valid_context_delaying_normalization(
                [query.clone()],
                &assumptions,
            )
        });
        assert!(
            result.is_err(),
            "the exact alias must be checked at size {size}"
        );
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 2),
        "unrelated bases increased exact-alias lookup work: {samples:?}"
    );
}

#[test]
fn symbolic_same_block_ranges_emit_no_pairs_with_near_linear_work() {
    // The lazy-separation acceptance curve: N symbolic same-block owned
    // ranges expose one compact composition authority and zero pairwise
    // CResourceSeparate propositions, in work near-linear in N.
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            };
            let endpoints = (0..=size)
                .map(|index| Bitvector32Term::Variable(Variable(94_000 + index as u64)))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(CMemoryRange::new(
                    base.clone(),
                    endpoints[index].clone(),
                    endpoints[index + 1].clone(),
                ))
            }));
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.observable_facts_assuming_valid(&PureFactContext::new())
            });
            let pair_count = facts
                .iter()
                .filter(|fact| matches!(fact, Proposition::CResourceSeparate { .. }))
                .count();
            assert_eq!(
                pair_count, 0,
                "symbolic same-block ranges must not materialize pairwise separations"
            );
            assert!(
                facts
                    .iter()
                    .any(|fact| matches!(fact, Proposition::CResourceComposition(_))),
                "multi-owner contexts should expose one compact authority"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "observable fact projection is superlinear: {samples:?}"
        );
    }
}

/// Exposing a cell that an unfolded composite holds is a structural lookup
/// at each unfolding, not a proof: with a chain of order facts relating the
/// composites' pointers, reasoning about every candidate at every unfolding
/// grows superlinearly, while the structural answer stays near linear in the
/// number of composites. Regression for the binary-tree slowdown, where
/// certification exposed each derived load through the resource algebra's
/// reasoning and took minutes.
#[test]
fn composite_exposure_finds_held_cells_by_structure_near_linearly() {
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("item", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("item"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::Variable(Variable(900_000 + index)),
            4,
        ),
    };
    let samples = [4_u64, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_composite(
                    "cell".to_string(),
                    vec![CValue::pointer(pointer(index))],
                )
            }));
            let mut assumptions = PureFactContext::new();
            for index in 0..size - 1 {
                assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(900_000 + index)),
                        Bitvector32Term::Variable(Variable(900_000 + index + 1)),
                    ),
                    true,
                ));
            }
            let target = CResourceFact::view_memory(memory_range(pointer(size - 1), 0, 1));
            let (exposed, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::expose_composite_resource_fact(
                    &context,
                    &target,
                    std::slice::from_ref(&definition),
                    &CMemory::new(),
                    &assumptions,
                )
            });
            assert!(
                exposed.is_some(),
                "size {size}: the unfolded cell should be exposed"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    eprintln!("composite exposure samples: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "composite exposure is superlinear: {samples:?}"
        );
    }
}

/// Package 3 regression. The quantity relations behind populations and
/// the resource algebra are decided by exact lookup and the retained atomic
/// condition checker, so an ambient context of unrelated bounded variables must
/// not change their work. The general prover this replaced scanned every
/// condition fact for an inconsistency and every proposition fact for a
/// singleton substitution, so its work grew with `size`.
#[test]
fn quantity_relations_ignore_unrelated_facts() {
    let count = Bitvector32Term::Variable(Variable(960_001));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size).assume_condition(
                ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(3)),
                true,
            );
            let (decided, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    // `resource_quantity_is_positive`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_than(
                            count.clone(),
                            Bitvector32Term::Constant(0),
                        ),
                    ),
                    // `resource_quantity_at_least`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_equal(
                            count.clone(),
                            Bitvector32Term::Constant(2),
                        ),
                    ),
                    // An exact quantity equality
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(3)),
                    ),
                    // A relation that does not follow: the miss must also be
                    // flat, and must not be repaired by a broader search.
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(4)),
                    ),
                ]
            });
            assert_eq!(
                decided,
                [true, true, true, false],
                "size {size}: exact quantity routes decided the wrong relations"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "quantity relations scanned unrelated facts: {samples:?}"
    );
}

/// The same curve through the resource-algebra entry points that consume those
/// relations: symbolic-quantity entailment (`resource_quantity_at_least` and
/// the residual test in `consume_exact_resource_fact`) and access-mode coring
/// (`resource_quantity_is_positive`).
#[test]
fn symbolic_quantity_consumption_ignores_unrelated_facts() {
    let available_quantity = Bitvector32Term::Variable(Variable(960_011));
    let required_quantity = Bitvector32Term::Variable(Variable(960_012));
    let resource = CResource::Token {
        name: "counted".to_string(),
        arguments: vec![int32(7).into()].into(),
    };
    let available = CResourceFact::own_quantity(resource.clone(), available_quantity.clone());
    let required = CResourceFact::own_quantity(resource.clone(), required_quantity.clone());
    let empty_quantity = Bitvector32Term::Variable(Variable(960_014));
    let empty_core = CResourceFact::own_quantity(resource, empty_quantity.clone());
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size)
                .assume_condition(
                    ConditionTerm::signed_greater_equal(
                        available_quantity.clone(),
                        required_quantity.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_than(
                        available_quantity.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::equal(empty_quantity.clone(), Bitvector32Term::Constant(0)),
                    true,
                );
            let context = ResourceContext::new().unchecked_with_fact(available.clone());
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    context.satisfies_fact(&required, &assumptions),
                    available.core_with_assumptions(&assumptions).is_some(),
                    // The miss matters too: an exactly-zero quantity has no
                    // access-mode core, and the general prover answered that
                    // only after scanning every ambient condition fact for an
                    // inconsistency and every proposition fact for a singleton
                    // substitution.
                    empty_core.core_with_assumptions(&assumptions).is_some(),
                )
            });
            assert_eq!(
                outcome,
                (true, true, false),
                "size {size}: symbolic quantity entailment lost its exact premise"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "symbolic quantity consumption scanned unrelated facts: {samples:?}"
    );
}

/// Allocation separation now asks the retained atomic resource checker rather
/// than the general prover, so the same flat curve applies to it.
#[test]
fn allocation_separation_ignores_unrelated_facts() {
    let allocation_base = Pointer {
        block: "package-3-allocation".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(
        Pointer {
            block: "package-3-held".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let overlapping = own_memory_fact(allocation_base.clone(), 0, 8);
    let bytes = Bitvector32Term::Constant(16);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    held.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &bytes,
                        4,
                        &assumptions,
                    ),
                    overlapping.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &bytes,
                        4,
                        &assumptions,
                    ),
                )
            });
            assert_eq!(
                outcome,
                (true, false),
                "size {size}: allocation separation decided the wrong blocks"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "allocation separation scanned unrelated facts: {samples:?}"
    );
}

/// Package 10(a) regression for `ResourceContext::satisfies_fact`'s miss
/// path.
///
/// A resource query that misses must be paid for by the fact it names and by
/// the resources the context indexes under that fact's block — never by the
/// ambient condition facts that happen to be in scope. Two axes are measured,
/// each with one fixed query.
///
/// The resource axis is flat. On the ambient-condition axis the residual
/// slope is the exact order-path walk in `condition_reasoning/order_paths.rs`,
/// a whole-context loop inside the frozen condition checker that
/// the kernel authority boundary in `docs/internals/proof-objects.md` treats as a separate indexing debt. This test
/// pins the slope that remains after the two `condition_facts` scans in
/// `exact_less_equal_for_memory_resolution` became indexed lookups at the two
/// endpoints the query names. Before that change the same query grew at twice
/// this rate (93, 157, 285, 541 over these sizes), so the assertion fails on
/// the old representation.
#[test]
fn satisfies_fact_miss_ignores_unrelated_facts() {
    let base = Pointer {
        block: "package-10a-held".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(base.clone(), 0, 8);
    let adjacent = own_memory_fact(base.clone(), 8, 16);
    let symbolic_end = Bitvector32Term::Variable(Variable(970_001));
    // A miss whose end is symbolic: the shape that reaches the proof-aware
    // containment layers instead of being refused by constant bounds.
    let missing = own_memory_fact(base.clone(), 0, symbolic_end);
    let context = ResourceContext::new()
        .unchecked_with_fact(held.clone())
        .unchecked_with_fact(adjacent.clone());

    let sizes = [16, 32, 64, 128];
    let ambient = sizes
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = ambient[0].1;
    assert!(
        ambient
            .iter()
            .all(|(size, work)| *work <= base_work + 2 * (size - sizes[0])),
        "satisfies_fact's miss path still scans ambient condition facts: {ambient:?}"
    );

    // The other axis: unrelated resources in the same context, with the
    // ambient fact context held empty. The block index must keep this flat.
    let resources = sizes
        .into_iter()
        .map(|size| {
            let mut wide = ResourceContext::new()
                .unchecked_with_fact(held.clone())
                .unchecked_with_fact(adjacent.clone());
            for index in 0..size {
                wide = wide.unchecked_with_fact(own_memory_fact(
                    Pointer {
                        block: format!("package-10a-unrelated-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    0,
                    4,
                ));
            }
            let assumptions = PureFactContext::new();
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                wide.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = resources[0].1;
    assert!(
        resources
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "satisfies_fact's miss path scanned unrelated resources: {resources:?}"
    );
}

#[test]
fn resource_model_arm_selection_ignores_unrelated_premises() {
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 11);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let exclusion = |value: &AlgebraicTerm| {
        Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(empty.clone()),
        )))
    };
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(exclusion(&model));
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(exclusion(&resource_index_variable(&ty, index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                select_resource_model_arm(&model, &assumptions),
                Some(ResourceModelArmSelection::Variant("Filled".to_string()))
            );
        });
        assert!(work > 0, "arm selection must count the premises it visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

/// An adversarially ordered dependency chain is retried through an indexed
/// event worklist.  Its deterministic work should grow with the explicit
/// dependency nodes and edges, not with repeated whole-section scans.
#[test]
fn dependent_resource_clause_work_scales_with_dependency_nodes() {
    let pointer = |index: usize| Pointer {
        // Keep each node in its own block so the curve measures the clause
        // dependency walk rather than the unrelated same-block range
        // normalization cost of the resource algebra.
        block: PointerBlock::Concrete(format!("dependency-{index}")),
        offset: PointerOffsetTerm::Constant((index as i64) * 4),
    };
    let load = |pointer: Pointer| CExpression::TypedLoad {
        pointer: Box::new(c_pointer_value(pointer)),
        value_type: CType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let samples = [4_usize, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let pointers = (0..=size).map(pointer).collect::<Vec<_>>();
            let memory = pointers.windows(2).fold(CMemory::new(), |memory, pair| {
                memory.store(pair[0].clone(), CValue::pointer(pair[1].clone()))
            });
            let state = CState::new().with_memory(memory);
            // Clause 0 is the only initially readable provider.  Put it last
            // and reverse the dependents so a fixed-point implementation must
            // rescan the whole pending suffix once per dependency depth.  An
            // event queue instead retries only the newly unblocked successor.
            let clauses = (1..size)
                .rev()
                .chain(std::iter::once(0))
                .map(|index| {
                    let base = if index == 0 {
                        c_pointer_value(pointers[index].clone())
                    } else {
                        load(pointers[index - 1].clone())
                    };
                    CResourceSpec::owned_memory(CMemorySegment {
                        base,
                        start: c_int32_literal(0),
                        end: c_int32_literal(1),
                        element_width: 4,
                        guard: None,
                    })
                })
                .collect::<Vec<_>>();
            let ((result, work), attempts) =
                crate::kernel::measure_resource_clause_attempts(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::functions::evaluate_function_resource_context(
                            &state,
                            &clauses,
                            &[],
                            &PureFactContext::new(),
                            &mut ExecutionBudget::default(),
                        )
                    })
                });
            let result = result.unwrap();
            assert!(
                result.is_ok(),
                "the dependency chain should evaluate: {result:?}"
            );
            assert_eq!(
                attempts,
                size * 2 - 1,
                "each blocked clause should be retried once after its provider: size={size}"
            );
            (size, work, attempts)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| { pair[1].1 <= pair[0].1.saturating_mul(4) + 256 }),
        "dependent clause work should stay bounded by the dependency graph: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn memory_invalidation_scales_with_affected_intervals_and_barrier_output() {
    let mut samples = Vec::new();
    for unrelated_count in [4_usize, 16, 64, 256, 1024] {
        let target_support = CResourceFact::own_composite("curve_target".into(), Vec::new());
        let target_view = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: "curve-block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let memory = CMemory::new().with_block("curve-block", (8 * unrelated_count + 8) as u32);
        let mut resources = ResourceContext::new().unchecked_with_fact(target_support.clone());
        let target_occurrence = resources.owned_occurrences_for_fact(&target_support)[0];
        resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            target_occurrence,
            &target_support,
            [target_view.clone()],
            &memory,
        );
        let mut unrelated_views = Vec::new();
        for index in 0..unrelated_count {
            let support =
                CResourceFact::own_composite(format!("curve_unrelated_{index}"), Vec::new());
            resources = resources.unchecked_with_fact(support.clone());
            let occurrence = resources.owned_occurrences_for_fact(&support)[0];
            let view = CResourceFact::view_memory(CMemoryRange::new(
                Pointer {
                    block: "curve-block".into(),
                    offset: PointerOffsetTerm::Constant((8 + index * 8) as i64),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ));
            resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
                occurrence,
                &support,
                [view.clone()],
                &memory,
            );
            unrelated_views.push(view);
        }
        let state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(resources);
        let before_allocations = crate::persistent::persistent_node_allocations();
        let (after, store_work) = crate::instrumentation::measure_deterministic_work(|| {
            state.clone().with_memory(memory.clone().store(
                Pointer {
                    block: "curve-block".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(1),
            ))
        });
        let store_allocations =
            crate::persistent::persistent_node_allocations() - before_allocations;
        assert!(
            !after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(after.resources().contains_exact_representation(view));
        }

        let before_barrier_allocations = crate::persistent::persistent_node_allocations();
        let (barrier_after, barrier_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                state
                    .clone()
                    .with_memory(memory.clone().with_loop_memory_havoc_preserving_loans(
                        Variable(820),
                        &BTreeSet::new(),
                        None,
                        None,
                    ))
            });
        let barrier_allocations =
            crate::persistent::persistent_node_allocations() - before_barrier_allocations;
        assert!(
            !barrier_after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(
                !barrier_after
                    .resources()
                    .contains_exact_representation(view)
            );
        }
        let before_alias_allocations = crate::persistent::persistent_node_allocations();
        let (alias_after, alias_work) = crate::instrumentation::measure_deterministic_work(|| {
            state.with_memory(
                memory
                    .clone()
                    .store(Pointer::symbolic(Variable(821)), int32(1)),
            )
        });
        let alias_allocations =
            crate::persistent::persistent_node_allocations() - before_alias_allocations;
        assert!(
            !alias_after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(!alias_after.resources().contains_exact_representation(view));
        }
        samples.push((
            unrelated_count,
            store_work,
            store_allocations,
            barrier_work,
            barrier_allocations,
            alias_work,
            alias_allocations,
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 + 80 && pair[1].2 <= pair[0].2 + 256,
            "same-block disjoint intervals leaked unrelated work: {samples:?}"
        );
        assert!(
            pair[1].3 >= pair[0].3
                && pair[1].5 >= pair[0].5
                && pair[1].3 <= pair[0].3.saturating_mul(20).saturating_add(32)
                && pair[1].5 <= pair[0].5.saturating_mul(20).saturating_add(32)
                && pair[1].4 <= pair[0].4.saturating_mul(8).saturating_add(2048)
                && pair[1].6 <= pair[0].6.saturating_mul(8).saturating_add(2048),
            "barrier and alias fallback work/allocations must track affected output: {samples:?}"
        );
    }
}

/// A scalar-reference call carves four bytes from a padded field's eight-byte
/// slot. The returned scalar and preserved bytewise padding must rejoin even
/// when the object address is symbolic.
#[test]
#[ignore = "nightly: 2.8s in the parallel gate"]
fn returned_scalar_and_bytewise_padding_rejoin_over_symbolic_objects() {
    let mut samples = Vec::new();
    for size in [8usize, 32, 128, 512] {
        let mut pieces = Vec::new();
        let mut expected = Vec::new();
        for index in 0..size {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(88_300 + index as u64)),
                    4,
                ),
            };
            pieces.push(CResourceFact::own_memory(CMemoryRange::new(
                base.offset_by_bytes(8),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )));
            pieces.push(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    base.clone(),
                    Bitvector32Term::Constant(12),
                    Bitvector32Term::Constant(16),
                    1,
                ),
            ));
            expected.push(CResourceFact::own_memory(CMemoryRange::new(
                base,
                Bitvector32Term::Constant(2),
                Bitvector32Term::Constant(4),
            )));
        }
        let context = ResourceContext::new().unchecked_with_facts(pieces);
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            expected
                .iter()
                .all(|fact| context.satisfies_fact(fact, &PureFactContext::new()))
        });
        assert!(accepted);
        assert_eq!(
            context.facts().len(),
            2 * size,
            "a query preserves the held representation"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0] + 32),
        "{samples:?}"
    );
}

/// The frame check opens each owned composite of a published composition
/// exactly one level, the boundary a composite lend uses. A cell in the
/// frontier is framed by ownership; a cell below it, inside a nested
/// composite, is not: the kernel does not read inside a folded body. The
/// query's work is charged per head, never per nested level.
#[test]
fn frame_check_opens_owned_composites_one_level_and_charges_per_head() {
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::Variable(Variable(910_000 + index)),
            4,
        ),
    };
    let cell = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("p"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    // `wrap1(p)` owns `cell(p)`, `wrap2(p)` owns `wrap1(p)`, and so on.
    let wrap_name = |depth: usize| format!("wrap{depth}");
    let mut definitions = vec![cell];
    for depth in 1..=8 {
        let inner = if depth == 1 {
            "cell".to_string()
        } else {
            wrap_name(depth - 1)
        };
        definitions.push(CCompositeResourceDefinition::new(
            wrap_name(depth),
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::composite(
                CResourceAccessMode::Own,
                inner,
                vec![c_variable("p")],
                vec![CType::Int32Pointer],
            )],
            Vec::new(),
        ));
    }
    let _armed = crate::kernel::arm_frame_composite_definitions(definitions);
    let havoc_range = memory_range(pointer(1), 0, 1);
    let composition = |name: &str| {
        ResourceContext::new().unchecked_with_facts([
            CResourceFact::own_composite(name.to_string(), vec![CValue::pointer(pointer(0))]),
            CResourceFact::own_composite("cell".to_string(), vec![CValue::pointer(pointer(1))]),
        ])
    };
    let query = |name: &str| {
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::CResourceComposition(composition(name)));
        crate::instrumentation::measure_deterministic_work(|| {
            assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                std::slice::from_ref(&havoc_range),
                &pointer(0),
                &CMemory::new(),
            )
        })
    };

    // Depth one: `cell(a)` and `cell(b)` open to two owned ranges, so the
    // havoc over `b` is disjoint from `a` by ownership.
    let (frontier, _) = query("cell");
    assert!(frontier, "a frontier cell is framed by ownership");

    // Below the frontier: `wrap1(a)` opens to a folded `cell(a)`, which owns
    // no range the check may read; the answer is refused, not guessed.
    let (nested, _) = query("wrap1");
    assert!(
        !nested,
        "a cell inside a nested composite is not framed by the kernel"
    );

    let samples = [1_usize, 2, 4, 8]
        .into_iter()
        .map(|depth| {
            let (proved, work) = query(&wrap_name(depth));
            assert!(!proved, "depth {depth}: nested composites stay folded");
            (depth, work)
        })
        .collect::<Vec<_>>();
    eprintln!("one-level frame query samples: {samples:?}");
    // Two heads at every depth, so the work is a constant per query; a walk
    // into the nested levels would add work at each doubling. Depth one is
    // the one shape that differs: its head opens straight onto the frontier
    // `cell`, so it compares that member's address with the havoced range,
    // a few charged `exact_signed_constant` lookups the folded deeper levels
    // never make. It is the ceiling, not the floor.
    let (_, shallowest) = samples[0];
    assert!(
        samples.iter().all(|(_, work)| *work <= shallowest + 4),
        "frame query work grew with nesting depth: {samples:?}"
    );
}

/// A contract section whose clauses all evaluate on the first pass needs no
/// read authority from the frame, so evaluating it does not expand the
/// composites the frame holds. In `examples/arena`'s pipeline the call rule
/// read `arena_destroy`'s `produces object(arena)` this way and expanded every
/// arena resource the caller held, which cost 45 million units once the frame
/// carried two allocations' worth of history.
#[test]
fn first_pass_resource_section_does_not_expand_the_frame() {
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::Variable(Variable(915_000 + index)),
            4,
        ),
    };
    let cell = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("p"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let produced = CResourceSpec::owned_memory(CMemorySegment {
        base: CExpression::Value(CValue::pointer(pointer(0))),
        start: c_int32_literal(0),
        end: c_int32_literal(1),
        element_width: 4,
        guard: None,
    });
    let samples = [4_u64, 16, 64]
        .into_iter()
        .map(|held| {
            let frame = ResourceContext::new().unchecked_with_facts((1..=held).map(|index| {
                CResourceFact::own_composite(
                    "cell".to_string(),
                    vec![CValue::pointer(pointer(index))],
                )
            }));
            let state = CState::new().with_resource_context(frame);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::evaluate_function_resource_context(
                    &state,
                    std::slice::from_ref(&produced),
                    std::slice::from_ref(&cell),
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                )
                .expect("the section stays inside its budget")
            });
            assert!(result.is_ok(), "{held} held cells: {result:?}");
            (held, work)
        })
        .collect::<Vec<_>>();
    let base_work = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work == base_work),
        "evaluating a first-pass section grew with the frame's composites: {samples:?}"
    );
}

#[test]
fn returned_resource_prefix_consumes_only_selected_padded_field_fragments() {
    for width in [1u32, 4] {
        let mut samples = Vec::new();
        for size in [8usize, 32, 128, 512] {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(89_000)),
                    4,
                ),
            };
            let owned = |base, start, end, width| {
                CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                    base,
                    Bitvector32Term::Constant(start),
                    Bitvector32Term::Constant(end),
                    width,
                ))
            };
            let mut pieces = (0..size)
                .map(|index| {
                    owned(
                        Pointer {
                            block: PointerBlock::Heap(89_001 + index as u64),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                        4,
                    )
                })
                .collect::<Vec<_>>();
            pieces.push(owned(base.offset_by_bytes(8), 0, 1, 4));
            pieces.push(owned(base.clone(), 12 / width, 16 / width, width));
            let available = ResourceContext::new().unchecked_with_facts(pieces);
            let slot = owned(base.clone(), 2, 4, 4);
            let required = ResourceContext::new().unchecked_with_fact(slot.clone());
            let state = CState::new().with_resource_context(available.clone());
            let interface = CFunctionContractInterface::new(CType::Void, vec![]);
            let assumptions = PureFactContext::new();
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &required,
                    &state,
                    &interface,
                    &assumptions,
                )
            });
            assert!(accepted, "{width}-byte units, {size} unrelated objects");
            samples.push(work);
            let duplicated = required.unchecked_with_fact(slot);
            assert!(
                !crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &duplicated,
                    &state,
                    &interface,
                    &assumptions
                )
            );
            let too_wide = ResourceContext::new().unchecked_with_fact(owned(base, 2, 5, 4));
            assert!(
                !crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &too_wide,
                    &state,
                    &interface,
                    &assumptions
                )
            );
        }
        assert!(
            samples.iter().all(|work| *work <= 4 * samples[0] + 64),
            "{samples:?}"
        );
    }
}

// Once a match supplies the constructor, opening its resource must not
// reevaluate an expanding list of predicates about that same model.
#[test]
fn known_resource_constructor_skips_predicate_refutation_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 850001);
    let constructor = arm_selection_constructor(&ty, "Filled", vec![int32(7).into()]);
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(850000),
        "choice".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let mut definition =
        CCompositeResourceDefinition::new("choice", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            CResourceMatchArm {
                variant: "Filled".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                binding_variables: vec![None],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::ClickFunctionApplication {
                        name: format!("predicate{index}"),
                        arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                    },
                    Bitvector32Term::Constant(1),
                ),
                true,
            ));
        }
        let known = assumptions.clone().assume_proposition(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(constructor.clone()),
        ));
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &known,
            )
        });
        assert!(facts.is_empty());
        costs.push(work);
        let (_, unresolved_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &assumptions,
            )
        });
        assert!(
            unresolved_work >= size,
            "unknown model must still consider its predicate premises"
        );
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
        "{costs:?}"
    );
}

// Once the only fieldless arm is known excluded, no arm can be published: the
// exclusion is already a fact, and refuting the remaining arm could not name
// the model's constructor. The call must not reevaluate the model's
// predicates at every step.
#[test]
fn known_exclusion_skips_refutation_of_unpublishable_arms() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 850101);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(850100),
        "choice".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let mut definition =
        CCompositeResourceDefinition::new("choice", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            CResourceMatchArm {
                variant: "Filled".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                binding_variables: vec![None],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::ClickFunctionApplication {
                        name: format!("predicate{index}"),
                        arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                    },
                    Bitvector32Term::Constant(1),
                ),
                true,
            ));
        }
        let negation = Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(empty.clone()),
        )));
        let excluded = assumptions.assume_proposition(negation.clone());
        // The exact-fact index is built on its first query; a live context
        // has already paid for it.
        assert!(
            crate::kernel::reasoning::path_facts::required_obligation_is_exactly_discharged(
                &excluded, &negation,
            )
        );
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &excluded,
            )
        });
        assert!(facts.is_empty(), "{facts:?}");
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
        "{costs:?}"
    );
}

#[test]
fn observable_projection_ignores_excluded_loan_bindings_when_hashing() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let base = context_with_one_loan_dependency(false);
        let expected = base.observable_composition();
        let mut context = base;
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        for index in 0..size {
            let range = CMemoryRange::new(
                CMemory::local_pointer(&format!("hidden_{index}")),
                0u32.into(),
                1u32.into(),
            );
            let support = CResourceFact::own_memory(range.clone());
            let view = CResourceFact::view_memory(range);
            context = context.unchecked_with_fact(support.clone());
            let support_occurrence = context.owned_occurrences_for_fact(&support)[0];
            let opening = ledger
                .lend(owner, reader, support_occurrence, support.clone())
                .unwrap();
            context = context.unchecked_with_supported_facts(&support, [view.clone()]);
            let occurrence = context.occurrences_for_fact(&view)[0];
            context = context.with_loan_dependency(
                occurrence,
                LoanViewBinding {
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    support: support_occurrence,
                    viewed: view,
                    hold: None,
                },
            );
        }
        let observed = context.observable_composition();
        assert_eq!(observed, expected);
        let (hash, work) =
            crate::instrumentation::measure_deterministic_work(|| resource_context_hash(&observed));
        assert_eq!(hash, resource_context_hash(&expected));
        assert_eq!(observed.live_loan_dependencies().count(), 1);
        assert!(work <= 16, "{size} excluded loans caused {work} hash units");
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work == costs[0]),
        "excluded loan costs: {costs:?}"
    );
}

#[test]
fn observable_projection_with_one_owner_and_borrow_does_not_scan_views() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let context =
            context_with_one_loan_dependency(false).unchecked_with_facts((0..size).map(|index| {
                CResourceFact::view_token(format!("ambient_observer_{index}"), Vec::new())
            }));
        let expected = context.observable_composition();
        let assumptions = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                let observed = context.observable_facts_assuming_valid(&assumptions);
                let [Proposition::CResourceComposition(composition)] = observed.as_slice() else {
                    panic!("one owner and a live borrow expose their composition");
                };
                assert!(std::sync::Arc::ptr_eq(
                    &composition.storage,
                    &expected.storage
                ));
            }
        });
        assert!(work <= 256, "one-owner borrow queries N={size}: {work}");
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work == costs[0]),
        "one-owner borrow query costs: {costs:?}"
    );
}

/// A base with N stated aliases (`q_i == b`, as a function requiring N
/// parameters equal to one it owns) must not cost N² to validate: every
/// alias's related roots are the same recorded-equality class, so walking
/// it once per alias re-walked one N-member class N times
/// (`bugs/call-step-grows-with-stated-pointer-aliases.md`).
#[test]
fn owned_range_validity_is_linear_in_stated_aliases_of_its_base() {
    let parameter = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
    };
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            let owned = parameter(41_000);
            let assumptions = (0..size).fold(PureFactContext::new(), |assumptions, index| {
                assumptions.assume_condition(
                    ConditionTerm::pointer_equal(parameter(41_100 + index as u64), owned.clone()),
                    true,
                )
            });
            let context = ResourceContext::new().unchecked_with_facts(
                [41_001, 41_002, 41_000]
                    .map(|id| CResourceFact::own_memory(memory_range(parameter(id), 0, 4))),
            );
            let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.validity_error(&assumptions)
            });
            assert!(error.is_none(), "size-{size} owned ranges should be valid");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(6),
            "validity is superlinear in the base's stated aliases: {samples:?}"
        );
    }
}
