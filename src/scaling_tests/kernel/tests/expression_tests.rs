// Scaling tests of `src/kernel/tests/expression_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn wide_equality_bounds_use_incremental_index_and_preserve_branches() {
    for size in [16usize, 64, 256, 1024] {
        let start = crate::persistent::persistent_node_allocations();
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                OldConditionTerm::uint64_equal(
                    OldMachineTerm::Variable(Variable(1000 + i as u64)),
                    OldMachineTerm::uint64_constant(i as u64),
                ),
                true,
            );
        }
        let allocations = crate::persistent::persistent_node_allocations() - start;
        assert!(
            allocations < 80 * size * (size.ilog2() as usize + 1),
            "{size}: {allocations}"
        );
        let target = OldMachineTerm::Variable(Variable(1000));
        let bound =
            OldConditionTerm::uint64_less_equal(target.clone(), OldMachineTerm::uint64_constant(1));
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&bound));
        assert_eq!(answer, Some(true));
        assert!(
            work <= 16,
            "unrelated equalities inflated query work: {size}: {work}"
        );
        let original = facts.clone();
        let equality = OldConditionTerm::uint64_equal(target, OldMachineTerm::uint64_constant(0));
        let changed = facts.assume_condition(equality, false);
        assert!(changed.is_inconsistent());
        assert_eq!(changed.decide(&bound), Some(true));
        assert_eq!(original.decide(&bound), Some(true));
    }
}

#[test]
fn loadable_object_provenance_lookup_ignores_unrelated_external_pointers() {
    let external = |variable| {
        Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(variable)), 4),
        )
    };
    let target = external(31_070);
    let loadable = |base| Proposition::MemoryLoadable {
        point: Default::default(),
        memory: SymbolicMemory::new(),
        base,
        bytes: (OldMachineTerm::constant(4)).into(),
        wide: false,
    };

    let samples = [4usize, 16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(loadable(target.clone()));
            for index in 0..size {
                assumptions =
                    assumptions.assume_proposition(loadable(external(32_000 + index as u64)));
            }
            let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .memory_loadable_candidates_for_object(&target)
                    .count()
            });
            assert_eq!(count, 1);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "object-provenance lookup scanned unrelated external pointers: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn exact_signed_constant_bound_lookup_ignores_unrelated_facts() {
    let value = OldMachineTerm::Variable(Variable(87_901));
    let query = OldConditionTerm::signed_greater_than(value.clone(), OldMachineTerm::constant(1));
    let mut samples = Vec::new();
    for size in [64, 256, 1024] {
        let mut assumptions = PureFactContext::new().assume_condition(
            OldConditionTerm::signed_greater_equal(value.clone(), OldMachineTerm::constant(2)),
            true,
        );
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                OldConditionTerm::signed_greater_equal(
                    OldMachineTerm::Variable(Variable(90_000 + index)),
                    OldMachineTerm::constant(2),
                ),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions
                .selected_for_test()
                .decide_selected_condition(&query)
        });
        assert_eq!(result, Some(true));
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
}

#[test]
fn exact_signed_mirror_normalization_ignores_unrelated_facts() {
    let value = OldMachineTerm::Variable(Variable(87_910));
    let premise = Proposition::condition_is(
        OldConditionTerm::signed_less_than(OldMachineTerm::constant(1), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::signed_greater_than(value, OldMachineTerm::constant(1)),
        true,
    );
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut premises = vec![premise.clone()];
        for index in 0..size {
            premises.push(Proposition::condition_is(
                OldConditionTerm::signed_greater_equal(
                    OldMachineTerm::Variable(Variable(91_000 + index)),
                    OldMachineTerm::constant(2),
                ),
                true,
            ));
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                std::slice::from_ref(&premise),
                &facts,
            )
        });
        assert!(result.is_ok());
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
    {
        let costs = samples.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 16);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn resource_object_provenance_does_not_scan_same_raw_block() {
    let pointer = |id| {
        Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::variable(Variable(895_000 + id)),
        )
    };
    let target = pointer(0);
    let expression = crate::kernel::program_expression::less_equal(
        crate::kernel::program_expression::variable("pointer"),
        crate::kernel::program_expression::variable("pointer"),
    );
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new_with_equalities(&assumptions);
        for id in 1..=size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(pointer(id), 0u32.into(), 4u32.into(), 1),
            ));
        }
        resources = resources.unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        let state = ExecutionState::new()
            .with_local("pointer", ProgramValue::pointer(target.clone()))
            .with_resource_context(resources);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut budget = ExecutionBudget::for_program_expression(&expression);
            evaluate_program_expression_paths(&state, &expression, &assumptions, &mut budget)
                .unwrap()
        });
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 2000,
        "provenance scanned the raw block: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn stored_pointer_bounds_ignore_unrelated_numeric_classes() {
    for size in [8u64, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(96_311));
        let stored = subobject_pointer(0, 0, 4);
        let memory =
            SymbolicMemory::new().store(field.clone(), ProgramValue::Pointer(stored.clone()));
        let read = OldPointer::from_read(
            stored.address().clone(),
            ProgramType::Int32Pointer,
            &crate::kernel::intern_memory_ref(&memory),
            &field,
        );
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::uint64_equal(
                    OldMachineTerm::Variable(Variable(97_000 + index)),
                    OldMachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointer_provenance_match(&read, &stored)
        });
        assert!(matches);
        assert!(work <= 512, "{size} unrelated classes: {work} work");
    }
}

#[test]
fn narrow_value_range_construction_ignores_unrelated_order_facts() {
    let value = ProgramValue::UInt8(OldMachineTerm::Variable(Variable(986_000)));
    let state = ExecutionState::new().with_local("byte", value);
    let expression = crate::kernel::program_expression::variable("byte");
    for size in [4u64, 16, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for id in 0..size {
            let term = OldMachineTerm::add(
                OldMachineTerm::Variable(Variable(987_000 + id)),
                OldMachineTerm::Variable(Variable(989_000 + id)),
            );
            assumptions = assumptions.assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), term),
                true,
            );
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_program_expression_paths(
                &state,
                &expression,
                &assumptions,
                &mut ExecutionBudget::for_program_expression(&expression),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].outcome,
            ExpressionOutcome::Value(
                state
                    .locals()
                    .get_native("byte")
                    .as_deref()
                    .unwrap()
                    .clone()
            )
        );
        // A `uint8` value is of its own format; reading it files no range.
        assert!(paths[0].facts.is_empty());
        assert!(
            work <= 256,
            "{size} unrelated order facts took {work} units"
        );
    }
}

/// Stage 5, decision D5: a Rust `bool` value of a comparison is the
/// condition, with no path split, so `n` such assignments are one path whose
/// work grows linearly, where C's 0/1 comparison splits into `2^n`.
#[test]
fn rust_bool_values_do_not_split_paths() {
    let mut previous = None;
    for size in [4usize, 8, 16, 32] {
        let mut state = ExecutionState::new()
            .with_local("limit", int32(OldMachineTerm::Variable(Variable(50))));
        let mut statement = program_skip();
        for index in 0..size {
            state = state
                .with_local(
                    format!("a_{index}"),
                    int32(OldMachineTerm::Variable(Variable(100 + index as u64))),
                )
                .with_local(format!("c_{index}"), ProgramValue::bool_constant(false));
            statement = program_seq(
                statement,
                program_assign(
                    format!("c_{index}"),
                    crate::kernel::program_expression::bool_value(
                        crate::kernel::program_expression::less_than(
                            crate::kernel::program_expression::variable(format!("a_{index}")),
                            crate::kernel::program_expression::variable("limit"),
                        ),
                    ),
                ),
            );
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &PureFactContext::new(),
                ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1, "{size} assignments");
        let StatementOutcome::Normal(state) = &paths[0].outcome else {
            panic!("{size}: {:?}", paths[0].outcome);
        };
        let local_native_output_324 = state.locals.get_native("c_0");
        let Some(ProgramValue::Bool(word)) = local_native_output_324.as_deref() else {
            panic!("{size}: `c_0` is a `Bool`");
        };
        assert!(word.bool_cast_operand().is_some(), "{size}: {word:?}");
        if let Some((previous_size, previous_work)) = previous {
            assert!(
                work <= previous_work * 2 * size / previous_size + 64,
                "{previous_size} -> {size}: {previous_work} -> {work}"
            );
        }
        previous = Some((size, work));
    }
}

#[test]
fn unsigned_division_domain_generation_ignores_ambient_facts() {
    for width in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for count in [4_u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let assumptions = (0..count).fold(PureFactContext::new(), |facts, index| {
                facts.assume_condition(
                    OldConditionTerm::equal(
                        OldMachineTerm::Variable(Variable(993_000 + index)),
                        OldMachineTerm::constant(index as u32),
                    ),
                    true,
                )
            });
            let (dividend, divisor) = (Variable(992_001), Variable(992_002));
            let zero = match width {
                MachineIntegerType::UInt32 => OldMachineTerm::constant(0),
                MachineIntegerType::UInt64 => OldMachineTerm::uint64_constant(0),
                _ => unreachable!(),
            };
            let known_zero = assumptions.clone().assume_condition(
                OldConditionTerm::machine_compare(
                    width,
                    CompareRelation::Equal,
                    OldMachineTerm::Variable(divisor),
                    zero,
                ),
                true,
            );
            let mut runs = Vec::new();
            for (assumptions, expected_zero) in [(&assumptions, false), (&known_zero, true)] {
                let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::eval::apply_program_divide(
                        width.symbolic_value(dividend),
                        width.symbolic_value(divisor),
                        vec![].into(),
                        vec![],
                        assumptions,
                    )
                });
                assert_eq!(paths.len(), 1);
                assert!(matches!(paths[0].outcome, ExpressionOutcome::Value(_)));
                assert_eq!(paths[0].obligations.len(), 1);
                let (known_zero, checked_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        paths[0].obligations[0].has_known_zero_divisor(assumptions)
                    });
                assert_eq!(known_zero, expected_zero);
                runs.push((work, checked_work));
            }
            samples.push((count, runs));
        }
        assert!(
            samples.iter().all(|(_, work)| *work == samples[0].1),
            "{width:?}: {samples:?}"
        );
        assert_eq!(samples[0].1[0].0, samples[0].1[1].0, "{width:?}");
    }
}

#[test]
fn unsigned_division_checks_only_an_indexed_operand_guard() {
    let width = MachineIntegerType::UInt32;
    let dividend = Variable(992_311);
    let divisor = Variable(992_312);
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let prefix = (0..count)
            .map(|index| {
                ExecutionPureFact::new(Proposition::condition_is(
                    OldConditionTerm::equal(
                        OldMachineTerm::Variable(Variable(993_000 + index)),
                        OldMachineTerm::constant(0),
                    ),
                    false,
                ))
            })
            .collect::<ExecutionFacts>();
        let guard = OldConditionTerm::equal(
            OldMachineTerm::Variable(divisor),
            OldMachineTerm::constant(0),
        );
        let runs = [None, Some(false), Some(true)].map(|polarity| {
            let mut facts = prefix.clone();
            if let Some(polarity) = polarity {
                facts.push(ExecutionPureFact::new(Proposition::condition_is(
                    guard.clone(),
                    polarity,
                )));
            }
            facts.ensure_indexed();
            let indexed = crate::kernel::execution_facts::indexed_execution_facts();
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::apply_program_divide(
                    width.symbolic_value(dividend),
                    width.symbolic_value(divisor),
                    facts,
                    vec![],
                    &assumptions,
                )
            });
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].obligations.is_empty(), polarity == Some(false));
            assert_eq!(
                crate::kernel::execution_facts::indexed_execution_facts(),
                indexed
            );
            work
        });
        samples.push(runs);
    }
    assert!(
        samples.iter().all(|sample| *sample == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn signed_addition_does_not_walk_the_operands_equality_class() {
    let mut samples = Vec::new();
    for count in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let operand = OldMachineTerm::Variable(Variable(994_001));
        let unrelated = OldMachineTerm::Variable(Variable(994_002));
        for root in [&operand, &unrelated] {
            let mut facts = PureFactContext::new().assume_condition(
                OldConditionTerm::signed_less_than(
                    operand.clone(),
                    OldMachineTerm::constant(i32::MAX as u32),
                ),
                true,
            );
            for index in 0..count {
                facts = facts.assume_condition(
                    OldConditionTerm::equal(
                        root.clone(),
                        OldMachineTerm::Variable(Variable(994_100 + index)),
                    ),
                    true,
                );
            }
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::apply_program_int32_add(
                    operand.clone(),
                    OldMachineTerm::constant(1),
                    vec![].into(),
                    vec![],
                    &facts,
                )
            });
            assert_eq!(paths.len(), 1);
            assert!(matches!(paths[0].outcome, ExpressionOutcome::Value(_)));
            samples.push(work);
        }
    }
    for sample in samples.as_chunks::<2>().0 {
        assert_eq!(sample, &samples[..2], "{samples:?}");
    }
}

#[test]
fn float_cast_refutation_uses_fixed_fact_keys() {
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let operand = OldMachineTerm::Variable(Variable(994_400));
        let cutoff = OldMachineTerm::uint64_constant(2147483648.0_f64.to_bits());
        let condition =
            |operator| OldConditionTerm::float64_compare(operand.clone(), cutoff.clone(), operator);
        let mut obligation = ProofObligation::verification_condition(Proposition::condition_is(
            condition(ComparisonOperator::LessThan),
            true,
        ));
        obligation.float_to_integer_bound = true;
        let facts = (0..count).fold(PureFactContext::new(), |facts, index| {
            facts.assume_condition(
                OldConditionTerm::float64_compare(
                    operand.clone(),
                    OldMachineTerm::uint64_constant(f64::from(index + 2).to_bits()),
                    ComparisonOperator::GreaterThan,
                ),
                true,
            )
        });
        let refuted = facts
            .clone()
            .assume_condition(condition(ComparisonOperator::Equal), true);
        let mut work = Vec::new();
        for (context, expected) in [
            (&facts, None),
            (&refuted, Some(UndefinedBehavior::FloatToIntegerOutOfRange)),
        ] {
            let (result, units) = crate::instrumentation::measure_deterministic_work(|| {
                obligation.known_undefined_behavior(context)
            });
            assert_eq!(result, expected);
            work.push(units);
        }
        samples.push(work);
    }
    assert!(
        samples.iter().all(|sample| sample == &samples[0]),
        "{samples:?}"
    );
}

#[test]
fn signed_shift_requirement_checks_one_bound_as_facts_grow() {
    use crate::kernel::program_expression as expr;

    let operand = OldMachineTerm::Variable(Variable(994_500));
    let state = ExecutionState::new().with_local("n", ProgramValue::Int32(operand.clone()));
    let expression = expr::shift_left(expr::variable("n"), expr::int32_literal(1));
    let fits = OldConditionTerm::signed_shift_result_fits(
        MachineIntegerType::Int32,
        operand.clone(),
        OldMachineTerm::constant(1),
        false,
    );
    for related in [false, true] {
        let samples = [4u32, 16, 64, 256].map(|size| {
            let bound = |value, lower| {
                OldConditionTerm::signed_greater_equal(value, OldMachineTerm::constant(lower))
            };
            let facts = (0..size).fold(
                PureFactContext::new().assume_condition(bound(operand.clone(), 0), true),
                |facts, index| {
                    let variable = if related {
                        operand.clone()
                    } else {
                        OldMachineTerm::Variable(Variable(994_501 + u64::from(index)))
                    };
                    facts.assume_condition(bound(variable, !index), true)
                },
            );
            [None, Some(true), Some(false)].map(|decision| {
                let facts = match decision {
                    Some(value) => facts.clone().assume_condition(fits.clone(), value),
                    None => facts.clone(),
                };
                let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                    evaluate_program_expression_paths(
                        &state,
                        &expression,
                        &facts,
                        &mut ExecutionBudget::for_program_expression(&expression),
                    )
                    .unwrap()
                });
                let [path] = paths.as_slice() else {
                    panic!("expected one shift path, got {paths:?}");
                };
                if decision == Some(false) {
                    assert!(matches!(
                        path.outcome,
                        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)
                    ));
                } else {
                    assert!(matches!(path.outcome, ExpressionOutcome::Value(_)));
                }
                assert_eq!(path.obligations.len(), usize::from(decision.is_none()));
                work
            })
        });
        for sample in &samples[1..] {
            assert!(
                sample
                    .iter()
                    .zip(samples[0])
                    .all(|(work, baseline)| *work <= baseline),
                "{related}: {samples:?}"
            );
        }
    }
}

#[test]
fn checked_difference_guard_uses_one_sign_and_one_comparison_as_facts_grow() {
    use crate::kernel::program_expression as expr;

    let (x, y) = (
        OldMachineTerm::Variable(Variable(994_800)),
        OldMachineTerm::Variable(Variable(994_801)),
    );
    let state = ExecutionState::new()
        .with_local("x", ProgramValue::Int32(x.clone()))
        .with_local("y", ProgramValue::Int32(y.clone()));
    let expression = expr::conditional(
        expr::less_equal(
            expr::variable("x"),
            expr::subtract(expr::int32_literal(i32::MAX as u32), expr::variable("y")),
        ),
        expr::int32_literal(1),
        expr::int32_literal(0),
    );
    let observe = |term| IntegerTerm::from_machine(MachineIntegerType::Int32, term).unwrap();
    let exact = OldConditionTerm::integer_less_equal(
        observe(x),
        IntegerTerm::subtract(
            IntegerTerm::constant_i64(i64::from(i32::MAX)),
            observe(y.clone()),
        ),
    );
    let nonnegative =
        OldConditionTerm::signed_greater_equal(y.clone(), OldMachineTerm::constant(0));
    for related in [false, true] {
        let samples = [4u32, 16, 64, 256].map(|size| {
            let facts = (0..size).fold(
                PureFactContext::new().assume_condition(nonnegative.clone(), true),
                |facts, index| {
                    let value = if related {
                        y.clone()
                    } else {
                        OldMachineTerm::Variable(Variable(994_810 + u64::from(index)))
                    };
                    facts.assume_condition(
                        OldConditionTerm::signed_greater_equal(
                            value,
                            OldMachineTerm::constant(!index),
                        ),
                        true,
                    )
                },
            );
            let facts = facts.assume_condition(exact.clone(), false);
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                evaluate_program_expression_paths(
                    &state,
                    &expression,
                    &facts,
                    &mut ExecutionBudget::for_program_expression(&expression),
                )
                .unwrap()
            });
            let [path] = paths.as_slice() else {
                panic!("expected only the false arm, got {paths:?}");
            };
            assert_eq!(path.outcome, ExpressionOutcome::Value(int32(0)));
            work
        });
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 8),
            "{related}: {samples:?}"
        );
    }
}
