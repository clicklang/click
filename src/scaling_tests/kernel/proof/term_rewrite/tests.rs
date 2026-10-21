// Scaling tests of `src/kernel/proof/term_rewrite.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn nested_c_folds_and_adt_matches_reserve_actual_nodes_linearly() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Case".into(),
            fields: vec![AlgebraicValueType::C(CType::Int32)],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "FoldMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "FoldMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let mut expression = IntegerTerm::constant_i64(0);
        for index in 0..depth {
            let binding = Variable(10_000 + index as u64);
            let accumulator = Variable(11_000 + index as u64);
            let item = Variable(12_000 + index as u64);
            let fold = Bitvector32Term::RangeFold {
                start: Box::new(Bitvector32Term::Constant(0)),
                end: Box::new(Bitvector32Term::Constant(2)),
                initial: Box::new(Bitvector32Term::Constant(0)),
                accumulator,
                item,
                body: Box::new(Bitvector32Term::Variable(accumulator)),
            };
            let observed = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observe_fold".into(),
                vec![PureFunctionArgument::Value(CValue::Int32(fold))],
            ));
            let body = IntegerTerm::Add(observed.into(), expression.into());
            expression = IntegerTerm::AlgebraicMatch {
                scrutinee: Box::new(AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(Variable(13_000 + index as u64)),
                }),
                arms: vec![AlgebraicIntegerMatchArm { binding_names: Default::default(),
                    variant: "Case".into(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        binding,
                    )))],
                    body: body.into(),
                }],
            };
        }
        let (visits, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let from = Bitvector32Term::Variable(Variable(90_000));
            let to = Bitvector32Term::Constant(0);
            let mut rewrite = TermRewrite::for_bits(&from, &to);
            let _ = rewrite.term(&Term::Integer(expression.clone()));
            rewrite.visits
        });
        assert!(visits >= depth, "nested match traversal was skipped");
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "nested carrier reservation expanded superlinearly: {work:?}"
        );
    }
}

#[test]
fn registered_load_rewrite_keeps_branching_pointer_dag_compact() {
    let source = Variable(3_104_000);
    let source_term = Bitvector32Term::Variable(source);
    let replacement = Bitvector32Term::Constant(9);
    let mut work = Vec::new();
    let mut last_load = None;
    for depth in [8usize, 16, 32, 64] {
        let memory = crate::kernel::intern_c_memory(
            CMemory::new().with_block(format!("branch-{depth}"), 64),
        );
        let block = format!("branch-{depth}");
        let mut load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer {
                block: PointerBlock::Concrete(block.clone()),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(source_term.clone()),
                    byte_width: 4,
                },
            },
            crate::kernel::LoadKind::Bits32,
            4,
        );
        for _ in 0..depth {
            load = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &Pointer {
                    block: PointerBlock::Concrete(block.clone()),
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::Int32Scaled {
                            value: Box::new(Bitvector32Term::Variable(load)),
                            byte_width: 4,
                        }),
                        Box::new(PointerOffsetTerm::Int32Scaled {
                            value: Box::new(Bitvector32Term::Variable(load)),
                            byte_width: 4,
                        }),
                    ),
                },
                crate::kernel::LoadKind::Bits32,
                4,
            );
        }
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(load),
        ));
        let (output, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
            rewrite.enable_registered_load_resolution();
            let output = rewrite.term(&Term::Integer(body.clone()));
            assert!(!rewrite.unsupported_integer_scope);
            assert!(!rewrite.integer_work_exhausted);
            output
        });
        let Term::Integer(IntegerTerm::Machine(machine)) = output else {
            panic!("registered load carrier changed shape")
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("rewritten load expanded into an owned memory tree")
        };
        assert_ne!(*rewritten_load, load);
        let Some((snapshot, pointer)) =
            crate::kernel::eval::registered_load_for_variable(rewritten_load)
        else {
            panic!("rewritten load was not registered")
        };
        assert_eq!(snapshot, memory);
        assert!(
            pointer
                .offset
                .scaled_values()
                .iter()
                .all(|value| matches!(value, Bitvector32Term::Variable(_)))
        );
        last_load = Some(load);
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "registered load DAG rewrite grew superlinearly: {work:?}"
        );
    }

    let load = last_load.expect("branching load was constructed");
    let mut cycle_rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
    cycle_rewrite.enable_registered_load_resolution();
    cycle_rewrite.registered_load_pointer_active.insert(load);
    let _ = cycle_rewrite.bits(&Bitvector32Term::Variable(load));
    assert_eq!(
        cycle_rewrite.refusal(),
        Some(RewriteRefusal::UnsupportedScope)
    );
}

#[test]
fn typed_integer_iota_consumes_the_shared_budget_before_deep_walk() {
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 8,
        smart: 8,
        control: 8,
    };
    let tactic = crate::instrumentation::TacticEvent {
        source_tactic_path: None,
        claim: "integer.typed_iota_budget".into(),
        tactic_index: 0,
        tactic_name: "typed_iota_budget".into(),
        class: "simple".into(),
        statement_index: 0,
        source_index: 0,
    };
    let mut measured_work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let scrutinee_variable = Variable(9960);
        let binding = Variable(9961);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![AlgebraicValueType::Integer],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "BudgetMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "BudgetMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let mut body = IntegerTerm::var(binding);
        for _ in 0..depth {
            body = IntegerTerm::Add(body.into(), IntegerTerm::constant_i64(1).into());
        }
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee_variable),
            }),
            arms: vec![AlgebraicIntegerMatchArm { binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(binding))],
                body: body.into(),
            }],
        };
        let constructor = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
            },
        };
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::new();
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(scrutinee_variable, constructor);
        let ((output, exhausted, visits, work), events) =
            crate::instrumentation::with_tactic_work_limits(limits, || {
                crate::instrumentation::collect(|| {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let mut rewrite = TermRewrite::for_typed_variables(
                        &c_replacements,
                        &integer_replacements,
                        &algebraic_replacements,
                    );
                    let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                        rewrite.integer(&input)
                    });
                    let result = (output, rewrite.integer_work_exhausted, rewrite.visits, work);
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                    );
                    result
                })
            });
        assert!(exhausted, "typed iota must consume the enclosing budget");
        assert!(visits <= 16, "typed iota continued after budget exhaustion");
        assert!(work <= 16, "collector work ignored the enclosing budget");
        assert!(matches!(output, IntegerTerm::AlgebraicMatch { .. }));
        assert!(events.iter().any(|event| matches!(
            event,
            crate::instrumentation::VerificationEvent::TacticWorkBudgetExceeded { .. }
        )));
        measured_work.push(work);
    }
    assert!(measured_work.windows(2).all(|pair| pair[1] <= 16));
}

#[test]
fn integer_fold_rewrite_shared_wrappers_charge_linear_work() {
    let source = Variable(1_040);
    let accumulator = Variable(1_041);
    let item = Variable(1_042);
    let mut samples = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut common = IntegerTerm::var(Variable(1_043));
        for _ in 0..depth {
            let child: SharedIntegerTerm = common.into();
            common = IntegerTerm::Add(child.clone(), child);
        }
        let shared_body: SharedIntegerTerm = common.into();
        let make_fold = |initial| {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::constant_i64(1).into(),
                },
                IntegerTerm::constant_i64(initial),
                accumulator,
                item,
                shared_body.as_ref().clone(),
            )
        };
        let root = IntegerTerm::Add(make_fold(0).into(), make_fold(1).into());
        let renamings = BTreeMap::new();
        let replacement = IntegerTerm::constant_i64(7);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            rewrite.term(&Term::Integer(root))
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "shared fold rewrite work grew superlinearly: {samples:?}"
        );
    }
}

#[test]
fn integer_fold_nested_capture_and_nocapture_work_scales_linearly() {
    fn integer_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn int32_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    let depths = [8, 16, 32, 64];
    let source = Variable(2_100_000);
    let replacement = IntegerTerm::constant_i64(7);
    let mut nocapture_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::var(source);
        for level in 0..depth {
            let accumulator = Variable(2_100_100 + level as u64 * 2);
            let item = Variable(2_100_101 + level as u64 * 2);
            nested = integer_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(accumulator)),
                accumulator,
                item,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let mut free = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free);
        assert!(!free.contains(&source));
        nocapture_work.push(work);
    }

    let integer_source = Variable(2_101_000);
    let integer_accumulator = Variable(2_101_001);
    let c_item = Variable(2_101_002);
    let mut integer_to_c_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::var(integer_source);
        for _ in 0..depth {
            nested = int32_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(integer_accumulator)),
                integer_accumulator,
                c_item,
            );
        }
        let mut integer_to_c_replacement = IntegerTerm::var(integer_accumulator);
        for _ in 0..depth {
            integer_to_c_replacement = IntegerTerm::add(
                integer_to_c_replacement,
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    Bitvector32Term::Variable(c_item),
                )),
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let renamings = BTreeMap::new();
            let mut rewrite = TermRewrite::for_integer_variables(
                integer_source,
                &integer_to_c_replacement,
                false,
                &renamings,
            );
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            item: fresh_item,
            ..
        } = &result
        else {
            unreachable!()
        };
        assert_ne!(*fresh_accumulator, integer_accumulator);
        assert_ne!(*fresh_item, c_item);
        let mut free_integer = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
        assert!(free_integer.contains(&integer_accumulator));
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&result, &mut free_c);
        assert!(free_c.contains(&c_item));
        integer_to_c_work.push(work);
    }

    let c_source = Variable(2_102_000);
    let c_accumulator = Variable(2_102_001);
    let integer_item = Variable(2_102_002);
    let mut c_to_integer_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(c_source),
        ));
        for _ in 0..depth {
            nested = integer_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(c_accumulator)),
                c_accumulator,
                integer_item,
            );
        }
        let mut replacement_value = IntegerTerm::var(c_accumulator);
        for _ in 0..depth {
            replacement_value = IntegerTerm::add(replacement_value, IntegerTerm::constant_i64(1));
        }
        let c_to_integer_replacement = Bitvector32Term::IntegerToMachine {
            value: SharedIntegerTerm::from(replacement_value),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let source_term = Bitvector32Term::Variable(c_source);
            let mut rewrite = TermRewrite::for_bits(&source_term, &c_to_integer_replacement);
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            ..
        } = &result
        else {
            unreachable!()
        };
        assert_ne!(*fresh_accumulator, c_accumulator);
        let mut free_integer = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
        assert!(free_integer.contains(&c_accumulator));
        c_to_integer_work.push(work);
    }

    for samples in [nocapture_work, integer_to_c_work, c_to_integer_work] {
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 4,
                "nested fold rewrite work grew superlinearly: {samples:?}"
            );
        }
    }
}

#[test]
fn checked_fold_collectors_bound_mixed_carrier_payloads_and_opaque_snapshots() {
    fn integer_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn int32_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn memory_snapshot(depth: usize) -> crate::kernel::SharedCMemory {
        let block = PointerBlock::Concrete("checked-fold-opaque".into());
        let mut memory = CMemory::new().with_block(block.clone(), depth as u32 + 1);
        for offset in 0..depth {
            memory = memory.store(
                Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(offset as i64),
                },
                CValue::Int32(Bitvector32Term::Constant(offset as u32)),
            );
        }
        crate::kernel::intern_c_memory(memory)
    }

    // Memory snapshots are opaque to lexical collection. Keep the
    // expression and its carrier payload fixed while changing only the
    // snapshot size; the checked rewrite work must stay unchanged.
    let fixed_source = Variable(3_010_000);
    let fixed_accumulator = Variable(3_010_001);
    let fixed_item = Variable(3_010_002);
    let mut fixed_body = IntegerTerm::var(fixed_source);
    for _ in 0..16 {
        fixed_body = int32_index_fold(
            IntegerTerm::add(fixed_body, IntegerTerm::var(fixed_accumulator)),
            fixed_accumulator,
            fixed_item,
        );
    }
    let mut snapshot_work = Vec::new();
    for snapshot_size in [0usize, 256] {
        let memory = memory_snapshot(snapshot_size);
        let pointer = Pointer {
            block: PointerBlock::Concrete("checked-fold-opaque".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let replacement_payload =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Bits32);
        let replacement = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            replacement_payload,
        ));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    fixed_source,
                    &replacement,
                    false,
                    &renamings,
                );
                let output = rewrite.term(&Term::Integer(fixed_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        assert!(matches!(result.2, Term::Integer(_)));
        snapshot_work.push(work);
    }
    assert_eq!(snapshot_work[0], snapshot_work[1]);

    let mut integer_to_c_work = Vec::new();
    let mut c_to_integer_work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let memory = memory_snapshot(depth);
        let pointer = Pointer {
            block: PointerBlock::Concrete("checked-fold-opaque".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let integer_source = Variable(3_000_000 + depth as u64);
        let mut int32_body = IntegerTerm::var(integer_source);
        let mut integer_accumulators = Vec::new();
        let mut c_items = Vec::new();
        for level in 0..depth {
            let accumulator = Variable(3_001_000 + level as u64 * 2);
            let item = Variable(3_001_001 + level as u64 * 2);
            integer_accumulators.push(accumulator);
            c_items.push(item);
            int32_body = int32_index_fold(
                IntegerTerm::add(int32_body, IntegerTerm::var(accumulator)),
                accumulator,
                item,
            );
        }
        let integer_capture = *integer_accumulators.last().unwrap();
        let c_capture = *c_items.last().unwrap();
        let mut mixed_c_payload = Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        for _ in 0..depth {
            mixed_c_payload = Bitvector32Term::Add(
                Box::new(mixed_c_payload),
                Box::new(Bitvector32Term::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::var(integer_capture)),
                    destination: crate::kernel::MachineIntegerType::Int32,
                }),
            );
            mixed_c_payload = Bitvector32Term::Add(
                Box::new(mixed_c_payload),
                Box::new(Bitvector32Term::Variable(c_capture)),
            );
        }
        let integer_to_c_replacement =
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                mixed_c_payload.clone(),
            ));
        let (result, work, attempts) = {
            let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_checked_simple_budget(10, || {
                    let renamings = BTreeMap::new();
                    let mut rewrite = TermRewrite::for_integer_variables(
                        integer_source,
                        &integer_to_c_replacement,
                        false,
                        &renamings,
                    );
                    let output = rewrite.term(&Term::Integer(int32_body.clone()));
                    (rewrite.integer_work_exhausted, output)
                })
            });
            let attempts = crate::instrumentation::checked_collection_attempts();
            (result, work, attempts)
        };
        assert!(result.0, "low checked budget unexpectedly completed");
        assert!(
            attempts <= 32,
            "collector kept attempting siblings: {attempts}"
        );
        assert!(
            work <= 64,
            "collector kept charging after exhaustion: {work}"
        );

        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    integer_source,
                    &integer_to_c_replacement,
                    false,
                    &renamings,
                );
                let output = rewrite.term(&Term::Integer(int32_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        let Term::Integer(output) = result.2 else {
            unreachable!()
        };
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&output, &mut free_c);
        assert!(!free_c.contains(&integer_source));
        integer_to_c_work.push(work);

        let c_source = Variable(3_002_000 + depth as u64);
        let mut c_to_integer_body =
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(c_source),
            ));
        let mut math_accumulators = Vec::new();
        let mut mixed_c_items = Vec::new();
        for level in 0..depth {
            if level % 2 == 0 {
                let accumulator = Variable(3_003_000 + level as u64 * 2);
                let item = Variable(3_003_001 + level as u64 * 2);
                math_accumulators.push(accumulator);
                c_to_integer_body = integer_index_fold(c_to_integer_body, accumulator, item);
            } else {
                let accumulator = Variable(3_004_000 + level as u64 * 2);
                let item = Variable(3_004_001 + level as u64 * 2);
                mixed_c_items.push(item);
                c_to_integer_body = int32_index_fold(c_to_integer_body, accumulator, item);
            }
        }
        let math_capture = *math_accumulators.last().unwrap();
        let c_item_capture = *mixed_c_items.last().unwrap();
        let mut c_replacement =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Bits32);
        for _ in 0..depth {
            c_replacement = Bitvector32Term::Add(
                Box::new(c_replacement),
                Box::new(Bitvector32Term::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::var(math_capture)),
                    destination: crate::kernel::MachineIntegerType::Int32,
                }),
            );
            c_replacement = Bitvector32Term::Add(
                Box::new(c_replacement),
                Box::new(Bitvector32Term::Variable(c_item_capture)),
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let source = Bitvector32Term::Variable(c_source);
                let mut rewrite = TermRewrite::for_bits_checked(&source, &c_replacement);
                let output = rewrite.term(&Term::Integer(c_to_integer_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        let Term::Integer(output) = result.2 else {
            unreachable!()
        };
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&output, &mut free_c);
        assert!(!free_c.contains(&c_source));
        c_to_integer_work.push(work);
    }
    for samples in [integer_to_c_work, c_to_integer_work] {
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 8 + 64,
                "checked collector work grew too quickly: {samples:?}"
            );
        }
    }
}

#[test]
fn checked_substitution_collector_reuses_registered_load_dag() {
    let source = Variable(3_104_000);
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
        let leaf_pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::IntegerToMachine {
                    value: IntegerTerm::var(source).into(),
                    destination: MachineIntegerType::Int32,
                }),
                byte_width: 4,
            },
        };
        let mut load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &leaf_pointer,
            crate::kernel::LoadKind::Bits32,
            4,
        );
        for _ in 0..depth {
            load = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &Pointer {
                    block: PointerBlock::Concrete("array".into()),
                    offset: PointerOffsetTerm::Variable(load),
                },
                crate::kernel::LoadKind::Bits32,
                4,
            );
        }
        let atom = Proposition::CMemoryLoadable {
            memory: memory.as_ref().clone(),
            base: Pointer {
                block: PointerBlock::Concrete("array".into()),
                offset: PointerOffsetTerm::Variable(load),
            },
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        };
        let mut proposition = atom.clone();
        for _ in 0..depth {
            proposition = Proposition::And(Box::new(proposition), Box::new(atom.clone()));
        }
        let ((contains_source, nodes, exhausted), measured) =
            crate::instrumentation::measure_deterministic_work(|| {
                let mut collector = IntegerSubstitutionVariableCollector::checked();
                collector.collect(&proposition);
                (
                    collector.carriers.integer.contains(&source),
                    collector.carriers.nodes,
                    collector.exhausted(),
                )
            });
        assert!(
            contains_source,
            "registered pointer carrier was not collected"
        );
        assert!(!exhausted, "collector exhausted at depth {depth}");
        assert!(nodes > depth, "collector skipped the selected pointer DAG");
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "registered-load collector expanded a shared DAG: {work:?}"
        );
    }
}

#[test]
fn native_unsigned_offset_projection_checks_full_width_bounds_and_scopes() {
    let index = Bitvector32Term::Variable(Variable(989_100));
    let native = PointerOffsetTerm::Int64Scaled {
        value: Box::new(index.clone()),
        byte_width: 4,
        unsigned: true,
    };
    let narrow = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::uint32_from_64(index.clone())),
        byte_width: 4,
    };
    let bound = ConditionTerm::uint64_less_equal(
        index.clone(),
        Bitvector32Term::UInt64Constant(1_073_741_823),
    );
    let projection = |condition, truth| {
        let conditions = HashMap::from([(condition, truth)]);
        let mut rewrite = TermRewrite::for_conditions(&conditions);
        let result = rewrite.offset(&native);
        assert!(rewrite.refusal().is_none());
        result
    };
    for (condition, truth) in [
        (bound.clone(), true),
        (
            ConditionTerm::uint64_less_than(
                index.clone(),
                Bitvector32Term::UInt64Constant(1_073_741_824),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_greater_equal(
                Bitvector32Term::UInt64Constant(1_073_741_823),
                index.clone(),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_greater_than(
                index.clone(),
                Bitvector32Term::UInt64Constant(1_073_741_823),
            ),
            false,
        ),
        (
            ConditionTerm::uint64_greater_equal(
                index.clone(),
                Bitvector32Term::UInt64Constant(1_073_741_824),
            ),
            false,
        ),
    ] {
        assert_eq!(projection(condition, truth), narrow);
    }
    for (condition, truth) in [
        (bound.clone(), false),
        (
            ConditionTerm::signed_less_equal(
                Bitvector32Term::uint32_from_64(index.clone()),
                Bitvector32Term::Constant(1_073_741_823),
            ),
            true,
        ),
        (
            ConditionTerm::int64_signed_less_equal(
                index.clone(),
                Bitvector32Term::Int64Constant(1_073_741_823),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_less_equal(
                index.clone(),
                Bitvector32Term::UInt64Constant(1u64 << 32),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_less_than(index.clone(), Bitvector32Term::UInt64Constant(0)),
            true,
        ),
        (
            ConditionTerm::uint64_equal(index.clone(), Bitvector32Term::UInt64Constant(1u64 << 32)),
            true,
        ),
    ] {
        assert_eq!(projection(condition, truth), native);
    }
    let conditions = HashMap::from([(bound.clone(), true)]);
    let signed = PointerOffsetTerm::Int64Scaled {
        value: Box::new(index.clone()),
        byte_width: 4,
        unsigned: false,
    };
    let mut rewrite = TermRewrite::for_conditions(&conditions);
    assert_eq!(rewrite.offset(&signed), signed);
    let binder = Proposition::ForAll { name: Default::default(),
        var: Variable(989_100),
        sort: Sort::CMachineInteger(MachineIntegerType::UInt64),
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(native.clone(), narrow.clone()),
            true,
        )),
    };
    assert_eq!(rewrite.proposition(&binder), binder);
    assert!(rewrite.refusal().is_none());
    let goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(native.clone(), narrow),
        true,
    );
    let premise = Proposition::ConditionIs(bound, true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&premise),
            &facts
        )
        .is_ok()
    );
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            &[premise],
            &crate::kernel::proof::ProofFacts::from_ordered(&[])
        )
        .is_err()
    );
    let mut costs = Vec::new();
    let mut preparation_overheads = Vec::new();
    for size in [0, 8, 64, 512] {
        let mut explicit = conditions.clone();
        for offset in 0..size {
            explicit.insert(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(990_000 + offset)),
                    Bitvector32Term::UInt64Constant(123),
                ),
                true,
            );
        }
        let (mut rewrite, prep) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&explicit)
        });
        assert_eq!(prep, 0, "scalar rewrites do not prepare pointer bounds");
        let (_, pointer_prep) = crate::instrumentation::measure_deterministic_work(|| {
            assert_ne!(rewrite.offset(&native), native);
        });
        assert!(pointer_prep > size as usize);
        preparation_overheads.push(pointer_prep - size as usize);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..64 {
                assert_ne!(rewrite.offset(&native), native);
            }
        });
        assert!(rewrite.refusal().is_none());
        costs.push(work);
    }
    assert!(
        preparation_overheads
            .iter()
            .all(|cost| *cost == preparation_overheads[0]),
        "pointer-bound preparation must charge one pass over explicit premises: {preparation_overheads:?}"
    );
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
