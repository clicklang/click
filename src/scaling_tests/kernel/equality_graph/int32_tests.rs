// Scaling tests of `src/kernel/equality_graph/int32_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn unsigned_congruence_registration_and_late_merges_scale_with_touched_uses() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                for i in 0..size {
                    let (a, b) = (var(i), var(i + size));
                    let (left, right) = (
                        unsigned_composition(a.clone()),
                        unsigned_composition(b.clone()),
                    );
                    assert!(!graph.are_int32_equal(&left, &right));
                    graph.add_int32_equality(&a, &b);
                    assert!(graph.are_int32_equal(&left, &right));
                }
            })
        });
        assert!(work < 1000 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 10_000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn fact_transport_graph_queries_scale_without_building_the_legacy_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let source = ConditionTerm::signed_less_than(sum(var(0)), var(size + 2));
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let target = ConditionTerm::signed_less_than(sum(var(index)), var(size + 2));
                assert!(context.condition_matches(&source, &target));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn resolved_four_byte_load_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let memory = intern_c_memory(
            CMemory::new()
                .with_block("resolved-int32-scale", 4)
                .store(pointer.clone(), CValue::Int32(sum(var(0)))),
        );
        let load = Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
            4,
            &memory,
        ));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(context.memory_loads_proven_equal(&load, &sum(var(index))));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn two_resolved_four_byte_load_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let pointer = |offset| Pointer {
            block: "two-resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let memory = intern_c_memory(
            CMemory::new()
                .with_block("two-resolved-int32-scale", 8)
                .store(pointer(0), CValue::Int32(sum(var(0))))
                .store(pointer(4), CValue::Int32(sum(var(size)))),
        );
        let load = |offset| {
            Bitvector32Term::Variable(load_variable_for_cell_with_origin(
                &memory,
                &pointer(offset),
                crate::kernel::LoadKind::Bits32,
                4,
                &memory,
            ))
        };
        let (left, right) = (load(0), load(4));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(context.memory_loads_proven_equal(&left, &right));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn direct_composite_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let resource = |value| CResource::Composite {
            name: "indexed-value-scale".into(),
            arguments: vec![CValue::Int32(sum(value)).into()].into(),
        };
        let left = resource(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(
                    crate::kernel::memory_provenance::c_resources_directly_match(
                        &left,
                        &resource(var(index)),
                        &context,
                    )
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn resource_instance_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let schema =
            ResourceFieldSchema::new(vec![("stamp".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let instance = |value| {
            CResource::Instance(
                ResourceInstance::new(
                    Variable(6200),
                    "instance-value-scale".into(),
                    vec![CValue::Int32(sum(value)).into()].into(),
                    schema.clone(),
                    vec![CValue::Int32(Bitvector32Term::Constant(3)).into()].into(),
                )
                .unwrap(),
            )
        };
        let left = instance(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(
                    crate::kernel::memory_provenance::c_resources_directly_match(
                        &left,
                        &instance(var(index)),
                        &context,
                    )
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn typed_int32_value_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let left = CValue::Int32(sum(var(0)));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = CValue::Int32(sum(var(index)));
                assert!(crate::kernel::reasoning::memory_resolution::c_values_proven_equal_for_memory_resolution(
                    &left, &right, &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn certified_int32_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let left = sum(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let goal = Proposition::ConditionIs(eq(&left, &sum(var(index))), true);
                assert!(crate::kernel::PureFactContext::settles_exactly(
                    &context, &goal,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn graph_equal_addend_matching_scales_without_the_legacy_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let fixed = var(size + 2);
        let last = var(size + 3);
        let left = Bitvector32Term::add(Bitvector32Term::add(var(0), fixed.clone()), last.clone());
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = Bitvector32Term::add(
                    var(index),
                    Bitvector32Term::add(fixed.clone(), last.clone()),
                );
                assert!(context.bitvector_add_terms_proven_equal(&left, &right));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn int32_context_insertion_and_forks_scale_with_indexed_work() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let ((context, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context.assume_condition(eq(&var(i), &var(i + 1)), true);
                    assert!(context.equality_graph.are_int32_equal(&var(0), &var(i + 1)));
                }
                context
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 300 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1200 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let branch = context
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert!(
                    branch
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
                assert!(
                    !context
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
            })
        });
        assert!(work < 300, "size={size}, fork work={work}");
        assert!(
            map_work < 1200 * logarithm,
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
fn scalar_support_tracking_does_not_compare_unrelated_snapshot_contents_across_arenas() {
    fn sample(size: usize) -> (PureFactContext, usize) {
        std::thread::spawn(move || {
            let _session = VerificationSession::enter();
            let address = Pointer {
                block: "selected".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut memory = CMemory::new().with_block("selected", 4);
            for i in 0..size {
                memory = memory.with_block(format!("unrelated-{i}"), 4);
            }
            let memory = intern_c_memory(
                memory.store(address.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
            );
            let load = Bitvector32Term::MemoryLoad(
                memory,
                Box::new(address),
                crate::kernel::LoadKind::Bits32,
            );
            crate::instrumentation::measure_deterministic_work(|| {
                PureFactContext::new()
                    .assume_condition(eq(&load, &Bitvector32Term::Constant(7)), true)
            })
        })
        .join()
        .expect("independent verification arena")
    }
    for size in [16, 64, 256, 1024] {
        // Retain the first context while admitting the same raw load shape in
        // another arena. Global raw-term interning used to compare the two
        // complete, independently allocated snapshots during the second insert.
        let (held, _) = sample(size);
        let (_, work) = sample(size);
        assert!(work < 100, "size={size}, second-arena work={work}");
        drop(held);
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn offset_premise_shallow_decision_and_forks_scale() {
    let add = |v| Bitvector32Term::Add(Box::new(v), Box::new(Bitvector32Term::Constant(1)));
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut parent = PureFactContext::new();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    parent = parent.clone().assume_condition(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(var(i), 4),
                            PointerOffsetTerm::scale_int32(var(i + 1), 4),
                        ),
                        true,
                    );
                }
                for i in 1..=size {
                    assert_eq!(
                        parent.decide_bitvector_equality_shallow(&add(var(0)), &add(var(i))),
                        Some(true)
                    );
                    assert_eq!(parent.decide(&eq(&var(0), &var(i))), Some(true));
                }
                let branch = parent
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert_eq!(
                    branch.decide_bitvector_equality_shallow(&add(var(0)), &add(var(size + 1))),
                    Some(true)
                );
                assert_ne!(
                    parent.decide_bitvector_equality_shallow(&add(var(0)), &add(var(size + 1))),
                    Some(true)
                );
            })
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 150 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
