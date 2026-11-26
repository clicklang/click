// Scaling tests of `src/kernel/tests/proof_reasoning_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};

#[test]
fn nested_solve_derivations_keep_rule_temporaries_off_the_recursive_stack() {
    std::thread::Builder::new()
        .name("nested-solve-small-stack".into())
        .stack_size(1792 * 1024)
        .spawn(|| {
            let samples = [1, 2, 4, 8].map(|depth| {
                let variable = Variable(98_000);
                let value = OldMachineTerm::Variable(variable);
                let positive = Proposition::condition_is(
                    OldConditionTerm::signed_less_than(OldMachineTerm::constant(0), value.clone()),
                    true,
                );
                let nonnegative = Proposition::condition_is(
                    OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), value),
                    true,
                );
                // Keep real quantified/atomic work below the connective spine.
                let mut goal = crate::kernel::quantifiers::test_forall(
                    Default::default(),
                    variable,
                    Sort::ProgramInt32,
                    Proposition::Implies(Box::new(positive), Box::new(nonnegative)),
                );
                let truth = Proposition::condition_is(
                    OldConditionTerm::equal(
                        OldMachineTerm::constant(0),
                        OldMachineTerm::constant(0),
                    ),
                    true,
                );
                for _ in 0..depth {
                    goal = Proposition::And(
                        Box::new(truth.clone()),
                        Box::new(Proposition::Implies(
                            Box::new(truth.clone()),
                            Box::new(Proposition::Implies(
                                Box::new(truth.clone()),
                                Box::new(goal),
                            )),
                        )),
                    );
                }
                let assumptions = PureFactContext::new();
                let (proof, planning_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::search::ProofSearch::derive_solve_proposition(
                            &(assumptions),
                            &goal,
                        )
                        .expect("nested quantified proof")
                    });
                let (checked, checking_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        proof.check(&assumptions)
                    });
                assert!(checked);
                (depth, planning_work, checking_work)
            });
            for pair in samples.windows(2) {
                assert!(
                    pair[1].1 <= pair[0].1 * 3 + 16,
                    "planning work: {samples:?}"
                );
                assert!(
                    pair[1].2 <= pair[0].2 * 3 + 16,
                    "checking work: {samples:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn algebraic_constructor_injectivity_ignores_unrelated_facts() {
    let algebraic_type = maybe_int32_type();
    let left = OldMachineTerm::Variable(Variable(89_100));
    let right = OldMachineTerm::Variable(Variable(89_101));
    let goal =
        Proposition::condition_is(OldConditionTerm::equal(left.clone(), right.clone()), true);
    let source = Proposition::Equal(
        Term::Algebraic(
            maybe_constructor(&algebraic_type, "Some", vec![ProgramValue::Int32(left)]).into(),
        ),
        Term::Algebraic(
            maybe_constructor(&algebraic_type, "Some", vec![ProgramValue::Int32(right)]).into(),
        ),
    );
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new().assume_proposition(source.clone());
            for index in 0..size {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            });
            assert!(derivation.is_some());
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "constructor injectivity lookup scaled with unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn function_contract_lookup_ignores_unrelated_pointer_facts() {
    fn contract_fact(name: &str, pointer: OldAddress) -> Proposition {
        Proposition::Predicate {
            name: FunctionContract::predicate_name_for(name),
            arguments: vec![
                Term::ExecutionState(Box::new(ExecutionState::new())),
                Term::ProgramValue(
                    (ProgramValue::typed_pointer(
                        pointer,
                        ProgramType::FunctionPointer(CallbackSignature::from_encoded(90_000)),
                    ))
                    .into(),
                ),
            ],
        }
    }

    let samples = [4, 16, 64, 256]
        .into_iter()
        .map(|size| {
            let target = OldAddress::symbolic_function(Variable(90_001));
            let mut assumptions =
                PureFactContext::new().assume_proposition(contract_fact("Target", target.clone()));
            for index in 0..size {
                assumptions = assumptions.assume_proposition(contract_fact(
                    "Unrelated",
                    OldAddress::symbolic_function(Variable(91_000 + index as u64)),
                ));
            }
            let (contracts, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .function_contract_facts_for(&target)
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>()
            });
            assert_eq!(contracts, vec!["Target".to_string()]);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 == pair[0].1),
        "exact contract lookup must not scan unrelated pointer facts: {samples:?}"
    );
}

#[test]
fn callback_contract_availability_uses_scoped_pointer_equality() {
    let interface_type = ProgramType::FunctionPointer(CallbackSignature::from_encoded(90_000));
    let contract = |name: &str, pointer, state, interface_type| Proposition::Predicate {
        name: FunctionContract::predicate_name_for(name),
        arguments: vec![
            Term::ExecutionState(Box::new(state)),
            Term::ProgramValue((ProgramValue::typed_pointer(pointer, interface_type)).into()),
        ],
    };
    let target = OldAddress::function("callback-target");
    let callback = OldAddress::symbolic_function(Variable(90_011));
    let source = contract(
        "Invoke",
        target.clone(),
        ExecutionState::new(),
        interface_type,
    );
    let required = contract(
        "Invoke",
        callback.clone(),
        ExecutionState::new(),
        interface_type,
    );
    let alias = Proposition::condition_is(
        OldConditionTerm::address_equal(callback.clone(), target),
        true,
    );
    let mut samples = Vec::new();
    for size in [4, 64, 256] {
        let mut context = PureFactContext::new()
            .assume_proposition(source.clone())
            .assume_proposition(alias.clone());
        for index in 0..size {
            context = context.assume_proposition(contract(
                "Invoke",
                OldAddress::symbolic_function(Variable(91_000 + index)),
                ExecutionState::new(),
                interface_type,
            ));
        }
        let ((known, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| context.contains_known(&required))
        });
        assert!(known);
        samples.push((work, map_work));
        assert!(!context.contains_known(&contract(
            "Other",
            callback.clone(),
            ExecutionState::new(),
            interface_type
        )));
        assert!(!context.contains_known(&contract(
            "Invoke",
            callback.clone(),
            ExecutionState::new().with_local("changed", int32(1)),
            interface_type
        )));
        // The contract's name fixes its interface, which a call checks
        // against the callee term's type; pointer equality ignores the type.
        assert!(context.contains_known(&contract(
            "Invoke",
            callback.clone(),
            ExecutionState::new(),
            ProgramType::FunctionPointer(CallbackSignature::from_encoded(90_001))
        )));
        for single in [&source, &alias] {
            let partial = PureFactContext::new().assume_proposition(single.clone());
            assert!(!partial.contains_known(&required));
        }
    }
    assert!(samples[2].0 <= samples[0].0 * 2 + 16, "{samples:?}");
    assert!(samples[2].1 <= samples[0].1 * 3 + 128, "{samples:?}");
    eprintln!("callback contract availability work: {samples:?}");
}

#[test]
fn exact_contradiction_lookup_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::equal(
                        OldMachineTerm::Variable(Variable(100_000 + index as u64)),
                        OldMachineTerm::constant(index as u32),
                    ),
                    true,
                );
            }
            let contradiction_left = OldMachineTerm::Variable(Variable(200_000));
            let contradiction_right = OldMachineTerm::constant(7);
            assumptions = assumptions
                .assume_condition(
                    OldConditionTerm::equal(
                        contradiction_left.clone(),
                        contradiction_right.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_than(contradiction_left, contradiction_right),
                    true,
                );
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(inconsistent);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "exact contradiction lookup is superlinear: {samples:?}"
        );
    }
}

#[test]
fn known_scalar_queries_have_bounded_work_beside_growing_classes() {
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |i| OldMachineTerm::Variable(Variable(991_000 + i));
        let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_condition(OldConditionTerm::equal(var(i), var(i + 1)), true);
            context = context.assume_condition(
                OldConditionTerm::signed_less_than(
                    OldMachineTerm::Variable(Variable(992_000 + i)),
                    OldMachineTerm::constant(i as u32),
                ),
                true,
            );
        }
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.int32_values_known_equal(&sum(var(0)), &sum(var(size))));
            assert!(!context.int32_values_known_equal(&sum(var(0)), &sum(var(size + 1))));
        });
        assert!(work < 128, "size={size}, work={work}");
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    }
}

/// `exact_signed_constant` answers from an index keyed by the term, so what
/// it examines does not grow with the unrelated condition facts beside the
/// one that pins the term. It used to scan every condition fact, uncharged,
/// on each range-membership and offset-equality query that asked it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn exact_signed_constant_is_a_keyed_lookup_among_unrelated_facts() {
    use crate::kernel::assumptions::exact_signed_constant;

    let pinned = OldMachineTerm::Variable(Variable(230_000));
    let reversed = OldMachineTerm::Variable(Variable(230_001));
    let wide = OldMachineTerm::Variable(Variable(230_002));
    let unpinned = OldMachineTerm::Variable(Variable(230_003));
    let mut samples = Vec::new();
    for size in [8_u32, 16, 32, 64] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            let other = OldMachineTerm::Variable(Variable(231_000 + u64::from(index)));
            // Unrelated constant equalities, unrelated order facts, and
            // facts that mention the queried terms without pinning them.
            assumptions = assumptions
                .assume_condition(
                    OldConditionTerm::equal(other.clone(), OldMachineTerm::constant(index)),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_than(pinned.clone(), other.clone()),
                    true,
                )
                .assume_condition(OldConditionTerm::equal(unpinned.clone(), other), false);
        }
        assumptions = assumptions
            .assume_condition(
                OldConditionTerm::equal(pinned.clone(), OldMachineTerm::constant(7)),
                true,
            )
            .assume_condition(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::constant(-3_i32 as u32)),
                    right: Box::new(reversed.clone()),
                },
                true,
            )
            .assume_condition(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(wide.clone()),
                    right: Box::new(OldMachineTerm::int64_constant(1 << 40)),
                },
                true,
            );
        PureFactContext::reset_exact_constant_fact_visits();
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [&pinned, &reversed, &wide, &unpinned]
                .map(|term| exact_signed_constant(term, &assumptions))
        });
        assert_eq!(answers, [Some(7), Some(-3), Some(1 << 40), None]);
        let visits = PureFactContext::exact_constant_fact_visits();
        assert_eq!(
            visits, 3,
            "each pinned term reads its own entry and nothing else at {size} facts"
        );
        samples.push((size, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "exact_signed_constant work must not grow with unrelated facts: {samples:?}"
    );
}

#[test]
fn increment_upper_bound_direct_lookup_ignores_unrelated_order_facts() {
    let value = OldMachineTerm::Variable(Variable(207_200));
    let upper = OldMachineTerm::Variable(Variable(207_201));
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(Variable(207_300 + index as u64)),
                        OldMachineTerm::Variable(Variable(207_400 + index as u64)),
                    ),
                    true,
                );
            }
            assumptions = assumptions.assume_condition(
                OldConditionTerm::signed_less_than(value.clone(), upper.clone()),
                true,
            );
            // Measure the direct rule, not construction or other atomic arms.
            let (step, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.exact_direct_order_step(&value, &upper, true)
            });
            assert!(step.is_some());
            assert_eq!(work, 1, "the first indexed candidate is the direct edge");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(1),
            "direct order lookup depends on ambient facts: {samples:?}"
        );
    }
}

/// Obligation emission is flat in unrelated ambient context.
///
/// The migrated route answers from the exact index and the atomic shape
/// dispatch, so growing the number of unrelated condition facts must not grow
/// the work of deciding whether to emit one structured obligation.
#[test]
fn structured_obligation_emission_scales_flat_in_unrelated_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_equal(
                        OldMachineTerm::Variable(Variable(96_100 + index as u64)),
                        OldMachineTerm::constant(1_000),
                    ),
                    true,
                );
            }
            let structured = Proposition::Implies(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(Variable(96_001)),
                        OldMachineTerm::constant(10),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(Variable(96_002)),
                        OldMachineTerm::constant(10),
                    ),
                    true,
                )),
            );
            let mut obligations = Vec::new();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                add_proof_obligation(&mut obligations, &assumptions, structured).unwrap();
            });
            assert_eq!(obligations.len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "obligation emission grew with unrelated facts: {samples:?}"
        );
    }
}

/// The order query's work does not grow with unrelated ambient propositions.
///
/// The removed collection walked every `prop_facts` entry and ran the prover
/// on each implication antecedent, so unrelated propositions were charged to
/// every order decision.
#[test]
fn order_path_decision_scales_flat_in_unrelated_propositions() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let a = OldMachineTerm::Variable(Variable(97_101));
            let b = OldMachineTerm::Variable(Variable(97_102));
            let c = OldMachineTerm::Variable(Variable(97_103));
            let mut assumptions = PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::signed_less_equal(a.clone(), b.clone()),
                    true,
                )
                .assume_condition(OldConditionTerm::signed_less_equal(b, c.clone()), true);
            for index in 0..size {
                let guard = OldConditionTerm::signed_less_than(
                    OldMachineTerm::Variable(Variable(97_200 + index as u64)),
                    OldMachineTerm::constant(10),
                );
                assumptions = assumptions
                    .assume_condition(guard.clone(), true)
                    .assume_proposition(Proposition::Implies(
                        Box::new(Proposition::condition_is(guard, true)),
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::signed_less_equal(
                                OldMachineTerm::Variable(Variable(97_400 + index as u64)),
                                OldMachineTerm::Variable(Variable(97_600 + index as u64)),
                            ),
                            true,
                        )),
                    ));
            }
            let goal = Proposition::condition_is(OldConditionTerm::signed_less_equal(a, c), true);
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::proves(&(assumptions), &goal)
            });
            assert!(proved);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "order decision grew with unrelated propositions: {samples:?}"
        );
    }
}

#[test]
fn forall_integer_instantiation_work_is_linear_in_nested_binders() {
    std::thread::Builder::new()
        .name("integer-quantifier-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            for capture in [false, true] {
                let mut measurements = Vec::new();
                for depth in [16, 32, 64, 128] {
                    let quantified = nested_integer_forall(depth, capture);
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::proof::fact_reasoning::instantiate_universal(
                            &quantified,
                            &crate::kernel::proof::fact_reasoning::InstanceArgument::Integer(
                                if capture {
                                    IntegerTerm::var(Variable(701))
                                } else {
                                    IntegerTerm::constant_i64(7)
                                },
                            ),
                        )
                        .unwrap_or_else(|_| panic!("nested Integer instantiation"))
                    });
                    measurements.push(work);
                }
                for pair in measurements.windows(2) {
                    assert!(
                        pair[1] <= pair[0] * 3 + 32,
                        "capture={capture}: {measurements:?}"
                    );
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn forall_integer_instantiation_preserves_repeated_squaring_as_a_shared_expression() {
    let binder = Variable(750);
    let mut measurements = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut term = IntegerTerm::var(binder);
        for _ in 0..depth {
            let child: SharedIntegerTerm = term.into();
            term = IntegerTerm::Multiply(child.clone(), child);
        }
        let quantified = crate::kernel::quantifiers::test_forall(
            Default::default(),
            binder,
            Sort::Integer,
            Proposition::Equal(
                Term::Integer(term.into()),
                Term::Integer(IntegerTerm::constant_i64(0).into()),
            ),
        );
        let (instance, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::instantiate_universal(
                &quantified,
                &crate::kernel::proof::fact_reasoning::InstanceArgument::Integer(
                    IntegerTerm::constant_i64(2),
                ),
            )
            .unwrap_or_else(|_| panic!("structural instantiation remains bounded"))
        });
        let Proposition::Equal(Term::Integer(term), _) = &instance else {
            panic!("equality")
        };
        let mut current = term.old_form();
        for _ in 0..depth {
            let IntegerTerm::Multiply(left, right) = current else {
                panic!("instantiation must not evaluate repeated squares")
            };
            assert_eq!(left.id(), right.id(), "substitution preserves sharing");
            current = left.as_ref();
        }
        assert_eq!(current, &IntegerTerm::constant_i64(2));
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{measurements:?}");
    }
}

#[test]
fn forall_integer_instantiation_charges_shared_replacement_only_once() {
    let binder = Variable(751);
    let mut measurements = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut replacement = IntegerTerm::var(Variable(752));
        let mut body = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        for _ in 0..size {
            let child: SharedIntegerTerm = replacement.into();
            replacement = IntegerTerm::Add(child.clone(), child);
            body = Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(binder).into()),
                    Term::Integer(IntegerTerm::constant_i64(0).into()),
                )),
                Box::new(body),
            );
        }
        let quantified = crate::kernel::quantifiers::test_forall(
            Default::default(),
            binder,
            Sort::Integer,
            body,
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::instantiate_universal(
                &quantified,
                &crate::kernel::proof::fact_reasoning::InstanceArgument::Integer(replacement),
            )
            .unwrap_or_else(|_| panic!("shared replacement instantiation"))
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{measurements:?}");
    }
}

#[test]
fn loadability_same_base_span_graph_queries_scale_without_fact_index() {
    let memory = SymbolicMemory::new();
    let base = OldAddress::symbolic(Variable(90_310));
    let var = |id| OldMachineTerm::Variable(Variable(id));
    let bytes = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    for size in [16u64, 64, 256, 512] {
        let fact = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: (bytes(var(0))).into(),
            wide: false,
        };
        let mut context = PureFactContext::new().assume_proposition(fact);
        for index in 0..size {
            context =
                context.assume_condition(OldConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let goal = Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: base.clone(),
                    bytes: (bytes(var(index))).into(),
                    wide: false,
                };
                assert!(context.proves_atomic_without_search(&goal));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn consistent_order_context_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(Variable(95_000 + index as u64)),
                        OldMachineTerm::Variable(Variable(96_000 + index as u64)),
                    ),
                    true,
                );
            }
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(!inconsistent, "unrelated order facts are consistent");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "consistent order contradiction scanning is superlinear: {samples:?}"
        );
    }
}

/// The issue-named fixed-arithmetic curve: one overflow decision whose
/// operands have exact bounds, while unrelated order facts grow. The interval
/// index answers from exact endpoint bounds, so the decision must not rescan
/// the growing context.
#[test]
fn fixed_overflow_decision_scales_near_linearly_with_unrelated_order_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let x = OldMachineTerm::Variable(Variable(94_001));
            let y = OldMachineTerm::Variable(Variable(94_002));
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_equal(
                        OldMachineTerm::Variable(Variable(94_100 + index as u64)),
                        OldMachineTerm::constant(1_000),
                    ),
                    true,
                );
            }
            for term in [x.clone(), y.clone()] {
                assumptions = assumptions
                    .assume_condition(
                        OldConditionTerm::signed_greater_equal(
                            term.clone(),
                            OldMachineTerm::constant(0),
                        ),
                        true,
                    )
                    .assume_condition(
                        OldConditionTerm::signed_less_equal(term, OldMachineTerm::constant(1_000)),
                        true,
                    );
            }
            let (decision, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.decide(&OldConditionTerm::signed_add_overflows(x, y))
            });
            assert_eq!(decision, Some(false));
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "fixed overflow decision is superlinear: {samples:?}"
        );
    }
}

/// `x_k = x_(k-1) + 1` executed as C: the k-th add's overflow decision must
/// not grow with the increments before it. The value once carried every
/// increment as a node, so each decision ranged a k-deep term and the chain
/// was quadratic. The decision is still made: an unbounded base is refused.
#[test]
fn increment_chain_add_work_does_not_grow_with_earlier_increments() {
    let base = OldMachineTerm::Variable(Variable(95_001));
    let bounded = PureFactContext::new()
        .assume_condition(
            OldConditionTerm::signed_greater_equal(base.clone(), OldMachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            OldConditionTerm::signed_less_equal(base.clone(), OldMachineTerm::constant(1_000_000)),
            true,
        );
    let state = ExecutionState::new();
    let increment = |value: OldMachineTerm, assumptions: &PureFactContext| {
        let expression = crate::kernel::program_expression::add(
            ProgramExpression::Value(ProgramValue::Int32(value)),
            crate::kernel::program_expression::int32_literal(1),
        );
        crate::instrumentation::measure_deterministic_work(|| {
            evaluate_program_expression_paths(
                &state,
                &expression,
                assumptions,
                &mut ExecutionBudget::default(),
            )
            .expect("an increment should evaluate")
        })
    };
    let mut value = base.clone();
    let mut samples = Vec::new();
    for length in 1..=256 {
        let (paths, work) = increment(value, &bounded);
        let [path] = paths.as_slice() else {
            panic!("increment {length} of a bounded base should not split: {paths:?}");
        };
        let ExpressionOutcome::Value(ProgramValue::Int32(next)) = &path.outcome else {
            panic!(
                "increment {length} should produce an int32: {:?}",
                path.outcome
            );
        };
        value = next.clone();
        if [16, 64, 256].contains(&length) {
            samples.push((length, work));
        }
    }
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(2)),
        "an increment's add work grows with the chain before it: {samples:?}"
    );
    let (paths, _) = increment(value, &PureFactContext::new());
    assert!(
        paths.iter().any(|path| matches!(
            path.outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)
        )),
        "an unbounded base must still owe the overflow"
    );
}

/// The issue-named quantified-match curve: one query answered by
/// instantiating one guarded quantified fact, while unrelated quantified
/// facts about other memory blocks grow.
#[test]
fn quantified_fact_query_scales_near_linearly_with_unrelated_quantified_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let memory = SymbolicMemory::new();
            let data = OldAddress {
                base: "quantified-data".into(),
                offset: OldAddressOffset::Constant(0).into(),
            };
            let fact_index = Variable(94_500);
            let target_index = Variable(94_501);
            let length = OldMachineTerm::Variable(Variable(94_502));
            let guarded_fact = forall_int32(
                fact_index,
                Proposition::Implies(
                    Box::new(Proposition::And(
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::signed_less_equal(
                                OldMachineTerm::constant(0),
                                OldMachineTerm::Variable(fact_index),
                            ),
                            true,
                        )),
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::signed_less_than(
                                OldMachineTerm::Variable(fact_index),
                                length.clone(),
                            ),
                            true,
                        )),
                    )),
                    Box::new(Proposition::condition_is(
                        OldConditionTerm::equal(
                            OldMachineTerm::read_named(
                                ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                                Box::new(data.offset_by_int32_elements(OldMachineTerm::Variable(
                                    fact_index,
                                ))),
                                crate::kernel::LoadKind::Int32,
                            ),
                            OldMachineTerm::constant(7),
                        ),
                        true,
                    )),
                ),
            );
            let mut assumptions = PureFactContext::new().assume_proposition(guarded_fact);
            for index in 0..size {
                let unrelated_index = Variable(95_000 + index as u64 * 2);
                let unrelated = OldAddress {
                    base: format!("quantified-unrelated-{index}").into(),
                    offset: OldAddressOffset::Constant(0).into(),
                };
                assumptions = assumptions.assume_proposition(forall_int32(
                    unrelated_index,
                    Proposition::Implies(
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::signed_less_equal(
                                OldMachineTerm::constant(0),
                                OldMachineTerm::Variable(unrelated_index),
                            ),
                            true,
                        )),
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::equal(
                                OldMachineTerm::read_named(
                                    ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                                    Box::new(unrelated.offset_by_int32_elements(
                                        OldMachineTerm::Variable(unrelated_index),
                                    )),
                                    crate::kernel::LoadKind::Int32,
                                ),
                                OldMachineTerm::constant(9),
                            ),
                            true,
                        )),
                    ),
                ));
            }
            assumptions = assumptions
                .assume_condition(
                    OldConditionTerm::signed_less_equal(
                        OldMachineTerm::constant(0),
                        OldMachineTerm::Variable(target_index),
                    ),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(target_index),
                        length,
                    ),
                    true,
                );
            let target = Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: data.offset_by_int32_elements(OldMachineTerm::Variable(target_index)),
                bytes: (OldMachineTerm::constant(4)).into(),
                wide: false,
            };
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::proves(&(assumptions), &target)
            });
            assert!(!proved, "quantified value facts grant no loadability");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "quantified fact query is superlinear: {samples:?}"
        );
    }
}

/// The issue-named long-order-path curve: deciding `first < last` across a
/// chain of strict order facts must cost work proportional to the returned
/// path, not path length times ambient fact count.
#[test]
fn long_order_path_decision_scales_near_linearly_with_path_length() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(Variable(96_000 + index as u64)),
                        OldMachineTerm::Variable(Variable(96_001 + index as u64)),
                    ),
                    true,
                );
            }
            let (decision, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.decide(&OldConditionTerm::signed_less_than(
                    OldMachineTerm::Variable(Variable(96_000)),
                    OldMachineTerm::Variable(Variable(96_000 + size as u64)),
                ))
            });
            assert_eq!(decision, Some(true), "the chain proves its endpoints");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "long order path decision is superlinear: {samples:?}"
        );
    }
}

/// The dominant real shape of the order-conflict residue: loads compared
/// against constants. An owned-vector profile showed 13,343 of 20,777 deep
/// comparisons were Load~Const with zero successes. A consistent context of
/// unrelated load-versus-constant order facts must not pay a comparison per
/// pair of facts.
#[test]
fn theory_capable_order_endpoints_scale_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                let cell = OldAddress {
                    base: format!("arg-memory-{index}").into(),
                    offset: OldAddressOffset::Constant(0).into(),
                };
                let load = OldMachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
                    Box::new(cell),
                    crate::kernel::LoadKind::Int32,
                );
                assumptions = assumptions.assume_condition(
                    OldConditionTerm::signed_less_than(
                        load,
                        OldMachineTerm::constant(index as u32),
                    ),
                    true,
                );
            }
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(!inconsistent, "unrelated load-bound facts are consistent");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "theory-capable order scanning is superlinear: {samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn direct_constant_lookup_ignores_unrelated_condition_facts() {
    let var = |id| OldMachineTerm::Variable(Variable(id));
    for size in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(var(97_000), var(97_001)), true)
            // Direct lookup requires the endpoint to be stated; equality-chain
            // refusal is covered separately below.
            .assume_condition(OldConditionTerm::equal(var(97_000), 7u32.into()), true);
        for index in 0..size {
            context = context
                .assume_condition(
                    OldConditionTerm::equal(var(100_000 + index), 9u32.into()),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_equal(var(200_000 + index), 4u32.into()),
                    true,
                );
        }
        PureFactContext::reset_condition_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                context.bitvector_constant_from_direct_equalities(&var(97_000)),
                Some(7)
            );
            assert_eq!(
                context.bitvector_constant_from_direct_equalities(&var(300_000)),
                None
            );
        });
        let visits = PureFactContext::condition_fact_visits();
        assert!(visits <= 4, "size={size}, visits={visits}, work={work}");
        assert!(work <= 12, "size={size}, work={work}");
        let start = std::time::Instant::now();
        for _ in 0..2048 {
            std::hint::black_box(context.bitvector_constant_from_direct_equalities(&var(97_000)));
            std::hint::black_box(context.bitvector_constant_from_direct_equalities(&var(300_000)));
        }
        eprintln!(
            "direct constant lookup: size={size}, visits={visits}, work={work}, 4096 queries={:?}",
            start.elapsed()
        );
    }
}

#[test]
fn direct_constant_lookup_declines_chains_until_the_endpoint_is_stated() {
    let var = |id| OldMachineTerm::Variable(Variable(400_000 + id));
    for size in [16u64, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(OldConditionTerm::equal(var(index), var(index + 1)), true);
        }
        context = context.assume_condition(OldConditionTerm::equal(var(size), 7u32.into()), true);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.bitvector_constant_from_direct_equalities(&var(0))
        });
        assert_eq!(result, None);
        assert!(work <= 12, "size={size}, refusal work={work}");
        let explicit = context.assume_condition(OldConditionTerm::equal(var(0), 7u32.into()), true);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            explicit.bitvector_constant_from_direct_equalities(&var(0))
        });
        assert_eq!(result, Some(7));
        assert!(work <= 12, "size={size}, explicit work={work}");
    }
}

/// The guarded-implication index selects `defined(e) implies a == b` facts
/// by the consequent's operands: a goal naming `a` finds the one guarded
/// equality about `a`, and the lookup's work does not grow with unrelated
/// guarded equalities. An implication under an ordinary condition is not
/// indexed: applying it stays an explicit `apply(fact)`.
#[test]
fn guarded_implication_lookup_is_keyed_by_consequent_operands() {
    for shared in [false, true] {
        let guarded = |index: u64| {
            let old = OldMachineTerm::Variable(Variable(98_000 + index));
            let delta = OldMachineTerm::Variable(Variable(98_500 + index));
            let new = OldMachineTerm::Variable(Variable(99_000 + index));
            Proposition::Implies(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Add,
                        left: Box::new(old.clone()),
                        right: Box::new(delta.clone()),
                    },
                    false,
                )),
                Box::new(Proposition::condition_is(
                    {
                        let condition = OldConditionTerm::equal(
                            new,
                            binary_node!(Int32, Add, Box::new(old), Box::new(delta)),
                        );
                        if shared {
                            crate::kernel::machine_integer::comparison::retained_arithmetic_comparison(&condition).unwrap()
                        } else {
                            condition
                        }
                    },
                    true,
                )),
            )
        };
        let goal = Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(99_000)),
                OldMachineTerm::constant(1),
            ),
            true,
        );
        let bound = |value: u32| {
            Proposition::condition_is(
                OldConditionTerm::signed_less_than(
                    OldMachineTerm::Variable(Variable(97_900)),
                    OldMachineTerm::constant(value),
                ),
                true,
            )
        };
        let ordinary_guard = Proposition::Implies(Box::new(bound(10)), Box::new(goal.clone()));
        let samples = [16, 32, 64, 128]
            .into_iter()
            .map(|size| {
                let mut facts = vec![guarded(0), ordinary_guard.clone()];
                facts.extend((1..size).map(guarded));
                let facts = crate::kernel::proof::PureFactStore::from_ordered(&facts);
                let exports = crate::kernel::KernelTermExport::machine_export_count();
                let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.guarded_implications_mentioning(&goal)
                });
                assert_eq!(
                    crate::kernel::KernelTermExport::machine_export_count(),
                    exports
                );
                assert_eq!(selected, vec![guarded(0)]);
                assert!(work > 0, "the lookup charges the buckets it visits");
                (size, work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
                "guarded-equality lookup grew with unrelated facts: {samples:?}"
            );
        }
    }
}

/// Substituting a quantifier's binder into a state it does not occur in
/// rewrites the state once; every later substitution of that variable into
/// that state is a memo hit, whatever the replacement.
#[test]
fn state_substitution_of_an_absent_variable_is_memoized() {
    let mut memory = SymbolicMemory::new();
    for index in 0..64 {
        memory = memory.with_block(format!("retained_state-memo-{index}"), 4);
    }
    let absent = Variable(434_000);
    let (_, first) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
            &memory,
            absent,
            &OldMachineTerm::constant(1),
        )
    });
    let (_, second) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
            &memory,
            absent,
            &OldMachineTerm::constant(2),
        )
    });
    assert!(
        first >= 64,
        "the first substitution walks the state: {first}"
    );
    assert!(second <= 2, "the repeat is a memo hit: {second}");
}

#[test]
fn uint64_arithmetic_constant_queries_ignore_unrelated_context() {
    let x = OldMachineTerm::Variable(Variable(990_000));
    let y = OldMachineTerm::Variable(Variable(990_001));
    let low_word_only = PureFactContext::new().assume_proposition(Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(x.clone()),
            right: Box::new(OldMachineTerm::constant(1)),
        },
        true,
    ));
    assert_eq!(
        crate::kernel::assumptions::exact_sixty_four_bit_constant(&x, true, &low_word_only),
        None
    );
    let mut prior = None;
    for size in [4, 16, 64] {
        // Keep term-bridge imports cold at every sample size.
        crate::kernel::clear_machine_observation_memo();
        let mut facts = PureFactContext::new()
            .assume_proposition(Proposition::condition_is(
                OldConditionTerm::uint64_equal(
                    x.clone(),
                    OldMachineTerm::uint64_constant(u64::MAX),
                ),
                true,
            ))
            .assume_proposition(Proposition::condition_is(
                OldConditionTerm::uint64_equal(y.clone(), OldMachineTerm::uint64_constant(2)),
                true,
            ));
        for index in 0..size {
            facts = facts.assume_proposition(Proposition::condition_is(
                OldConditionTerm::uint64_equal(
                    OldMachineTerm::Variable(Variable(991_000 + index)),
                    OldMachineTerm::uint64_constant(index),
                ),
                true,
            ));
        }
        let cases = [
            (
                OldMachineTerm::uint64_divide(x.clone(), y.clone()),
                Some(u64::MAX / 2),
            ),
            (
                OldMachineTerm::uint64_remainder(x.clone(), y.clone()),
                Some(1),
            ),
            (
                OldMachineTerm::uint64_bitwise_and(x.clone(), y.clone()),
                Some(2),
            ),
            (
                OldMachineTerm::uint64_bitwise_or(x.clone(), y.clone()),
                Some(u64::MAX),
            ),
            (
                OldMachineTerm::uint64_bitwise_xor(x.clone(), y.clone()),
                Some(u64::MAX - 2),
            ),
            (OldMachineTerm::uint64_bitwise_not(x.clone()), Some(0)),
            (
                OldMachineTerm::uint64_shift_left(x.clone(), OldMachineTerm::constant(63)),
                Some(1 << 63),
            ),
            (
                OldMachineTerm::uint64_logical_shift_right(x.clone(), OldMachineTerm::constant(63)),
                Some(1),
            ),
            (
                OldMachineTerm::uint64_divide(x.clone(), OldMachineTerm::uint64_constant(0)),
                None,
            ),
            (
                OldMachineTerm::uint64_remainder(x.clone(), OldMachineTerm::uint64_constant(0)),
                None,
            ),
            (
                OldMachineTerm::uint64_logical_shift_right(x.clone(), OldMachineTerm::constant(64)),
                None,
            ),
        ];
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (term, expected) in cases {
                assert_eq!(facts.wide_constant_from_equalities(&term), expected);
                assert_eq!(
                    crate::kernel::assumptions::exact_sixty_four_bit_constant(&term, true, &facts,),
                    expected.and_then(|bits| i64::try_from(bits).ok())
                );
            }
        });
        assert!(work > 0);
        if let Some(old) = prior {
            assert_eq!(work, old);
        }
        prior = Some(work);
    }
}

#[test]
fn wide_constant_arithmetic_work_scales_with_selected_expression() {
    let variable = OldMachineTerm::Variable(Variable(993_000));
    let facts = PureFactContext::new().assume_proposition(Proposition::condition_is(
        OldConditionTerm::uint64_equal(variable.clone(), OldMachineTerm::uint64_constant(9)),
        true,
    ));
    let mut prior = None;
    for size in [4, 16, 64] {
        let mut expression = variable.clone();
        for _ in 0..size {
            expression = OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Divide,
                left: Box::new(expression),
                right: Box::new(OldMachineTerm::uint64_constant(1)),
            };
        }
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.wide_constant_from_equalities(&expression)
        });
        assert_eq!(value, Some(9));
        if let Some(old) = prior {
            assert!(work <= old * 5, "work grew from {old} to {work}");
        }
        prior = Some(work);
    }
}

#[test]
fn pointer_association_selected_guard_work_ignores_ambient_facts() {
    let i = OldMachineTerm::Variable(Variable(198201));
    let defined = Proposition::condition_is(
        OldConditionTerm::signed_add_overflows(i.clone(), OldMachineTerm::constant(4)),
        false,
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::address_offset_equal(
            OldAddressOffset::Add(
                Box::new(OldAddressOffset::scale_int32(i.clone(), 1)),
                Box::new(OldAddressOffset::Constant(4)),
            )
            .into(),
            OldAddressOffset::scale_int32(OldMachineTerm::add(i, OldMachineTerm::constant(4)), 1)
                .into(),
        ),
        true,
    );
    let mut prior = None;
    for count in [0, 4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut ambient = vec![defined.clone()];
        ambient.extend((0..count).map(|n| {
            Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(199000 + n)),
                    OldMachineTerm::constant(n as u32),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&ambient);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                std::slice::from_ref(&defined),
                &facts,
            )
        });
        assert!(result.is_ok());
        assert!(work > 0);
        if let Some(old) = prior {
            assert_eq!(work, old);
        }
        prior = Some(work);
    }
}

/// `(p + i) + 4 == p + (i + 4)` at a full-width unsigned index, from its
/// one selected bound `to_integer(i) + 4 <= 18446744073709551615`. The
/// guard is one exact lookup: the work stays the same as unrelated facts
/// grow, and as bounds of the same shape on other indices grow, and the
/// association is refused without its own bound.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn uint64_pointer_association_selected_guard_work_ignores_other_facts() {
    let i = OldMachineTerm::Variable(Variable(198301));
    let goal_condition = OldConditionTerm::address_offset_equal(
        OldAddressOffset::Add(
            Box::new(OldAddressOffset::scale_int64(i.clone(), 1, true)),
            Box::new(OldAddressOffset::Constant(4)),
        ),
        OldAddressOffset::scale_int64(
            OldMachineTerm::uint64_add(i, OldMachineTerm::uint64_constant(4)),
            1,
            true,
        ),
    );
    let goal = Proposition::condition_is(goal_condition.clone(), true);
    let bound_of = |condition: &OldConditionTerm| {
        Proposition::condition_is(
            condition
                .pointer_offset_uint64_association_guard()
                .expect("a full-width association has a guard"),
            true,
        )
    };
    let bound = bound_of(&goal_condition);
    let other_bound = |n: u64| {
        let j = OldMachineTerm::Variable(Variable(199500 + n));
        bound_of(&OldConditionTerm::address_offset_equal(
            OldAddressOffset::Add(
                Box::new(OldAddressOffset::scale_int64(j.clone(), 1, true)),
                Box::new(OldAddressOffset::Constant(4)),
            ),
            OldAddressOffset::scale_int64(
                OldMachineTerm::uint64_add(j, OldMachineTerm::uint64_constant(4)),
                1,
                true,
            ),
        ))
    };
    for related in [false, true] {
        let mut prior = None;
        for count in [0, 4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut ambient = vec![bound.clone()];
            ambient.extend((0..count).map(|n| {
                if related {
                    other_bound(n)
                } else {
                    Proposition::condition_is(
                        OldConditionTerm::equal(
                            OldMachineTerm::Variable(Variable(199000 + n)),
                            OldMachineTerm::constant(n as u32),
                        ),
                        true,
                    )
                }
            }));
            let facts = crate::kernel::proof::PureFactStore::from_ordered(&ambient);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                    &goal,
                    std::slice::from_ref(&bound),
                    &facts,
                )
            });
            assert!(result.is_ok(), "{related} {count}: {result:?}");
            assert!(work > 0);
            if let Some(old) = prior {
                assert_eq!(work, old, "{related} {count}");
            }
            prior = Some(work);
            // Another index's bound does not regroup this one.
            if related && count > 0 {
                let other = other_bound(0);
                assert!(
                    crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                        &goal,
                        std::slice::from_ref(&other),
                        &facts,
                    )
                    .is_err()
                );
            }
        }
    }
}

#[test]
fn native_loadability_window_query_work_ignores_unrelated_views() {
    let memory = SymbolicMemory::new();
    let root = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0).into(),
    };
    let target = root.offset_by_bytes(1);
    let mut expected = None;
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: root.offset_by_bytes(4 * (index + 1)),
                bytes: crate::kernel::StoredMachineTerm::new(
                    crate::kernel::MachineIntegerType::UInt64,
                    OldMachineTerm::uint64_constant(16),
                ),
                wide: true,
            });
        }
        context = context.assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: root.clone(),
            bytes: crate::kernel::StoredMachineTerm::new(
                crate::kernel::MachineIntegerType::UInt64,
                OldMachineTerm::uint64_constant(16),
            ),
            wide: true,
        });
        // Construct the address index once before measuring hot queries.
        assert!(context.proves_native_memory_loadable(
            &memory,
            &root,
            &OldMachineTerm::uint64_constant(16)
        ));
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                context.proves_native_memory_loadable(
                    &memory,
                    &target,
                    &OldMachineTerm::uint64_constant(15),
                ),
                context.proves_native_memory_loadable(
                    &memory,
                    &target,
                    &OldMachineTerm::uint64_constant(16),
                ),
            )
        });
        assert_eq!(answers, (true, false));
        if let Some(prior) = expected {
            assert_eq!(work, prior);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn native_loadability_prefix_coverage_ignores_unrelated_addresses() {
    let memory = SymbolicMemory::new();
    let base = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0).into(),
    };
    let requested = OldMachineTerm::Variable(Variable(973_103));
    let mut expected = None;
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: base.offset_by_bytes(4 * (index + 1)),
                bytes: crate::kernel::StoredMachineTerm::new(
                    crate::kernel::MachineIntegerType::UInt64,
                    OldMachineTerm::uint64_constant(16),
                ),
                wide: true,
            });
        }
        context = context
            .assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: base.clone(),
                bytes: crate::kernel::StoredMachineTerm::new(
                    crate::kernel::MachineIntegerType::UInt64,
                    OldMachineTerm::uint64_constant(16),
                ),
                wide: true,
            })
            .assume_proposition(Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(
                    requested.clone(),
                    OldMachineTerm::uint64_constant(16),
                ),
                true,
            ));
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                context.proves_native_memory_loadable(&memory, &base, &requested),
                context.proves_native_memory_loadable(
                    &memory,
                    &base,
                    &OldMachineTerm::uint64_constant(17),
                ),
            )
        });
        assert_eq!(proved, (true, false));
        assert!(work > 0);
        if let Some(expected) = expected {
            assert_eq!(work, expected);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn native_loadability_queries_do_not_visit_unrelated_addresses() {
    let memory = SymbolicMemory::new();
    let base = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0).into(),
    };
    let mut expected = None;
    for count in [16, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: OldAddress {
                    base: base.base.clone(),
                    offset: OldAddressOffset::Constant(4 * (index + 1)).into(),
                },
                bytes: crate::kernel::StoredMachineTerm::new(
                    crate::kernel::MachineIntegerType::UInt64,
                    OldMachineTerm::uint64_constant(8),
                ),
                wide: true,
            });
        }
        context = context.assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: crate::kernel::StoredMachineTerm::new(
                crate::kernel::MachineIntegerType::UInt64,
                OldMachineTerm::uint64_constant(8),
            ),
            wide: true,
        });
        // Index construction is setup work. Repeated exact-range queries must
        // stay independent of the other addresses, even on a refusal.
        assert!(context.proves_native_memory_loadable(
            &memory,
            &base,
            &OldMachineTerm::uint64_constant(8)
        ));
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.proves_native_memory_loadable(
                &memory,
                &base,
                &OldMachineTerm::uint64_constant(9),
            )
        });
        assert!(!proved);
        if let Some(expected) = expected {
            assert_eq!(work, expected);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn required_obligation_connective_work_scales_with_goal_not_ambient_facts() {
    let mut work_by_size = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut work_by_ambient = Vec::new();
        for ambient in [8, 32, 128, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let known =
                Proposition::condition_is(OldConditionTerm::Variable(Variable(98000)), true);
            let unknown =
                Proposition::condition_is(OldConditionTerm::Variable(Variable(98001)), true);
            let mut facts = PureFactContext::new().assume_proposition(known.clone());
            for i in 0..ambient {
                facts = facts.assume_proposition(Proposition::condition_is(
                    OldConditionTerm::Variable(Variable(99000 + i)),
                    true,
                ));
            }
            let mut and = known.clone();
            let mut or = unknown.clone();
            for _ in 1..size {
                and = Proposition::And(Box::new(and), Box::new(known.clone()));
                or = Proposition::Or(Box::new(or), Box::new(unknown.clone()));
            }
            // Index construction belongs to context preparation, not each
            // goal query. Live lowering has already initialized this index.
            facts.build_stated_proposition_index();
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    required_obligation_is_exactly_discharged(&facts, &and),
                    required_obligation_is_exactly_discharged(&facts, &or),
                )
            });
            assert_eq!(answers, (true, false));
            work_by_ambient.push(work);
        }
        assert!(
            work_by_ambient.windows(2).all(|pair| pair[0] == pair[1]),
            "unrelated facts affected work: {work_by_ambient:?}"
        );
        work_by_size.push(work_by_ambient[0]);
    }
    assert!(
        work_by_size
            .windows(2)
            .all(|pair| pair[1] <= 2 * pair[0] + 4),
        "connective work grew faster than the goal: {work_by_size:?}"
    );
}

#[test]
fn restricting_model_support_ignores_unselected_scalar_graph_edges() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = maybe_int32_type();
        let model = |id| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(id)),
        };
        let equality = Proposition::Equal(
            Term::Algebraic(model(97600).into()),
            Term::Algebraic(model(97601).into()),
        );
        let mut context = PureFactContext::new().assume_proposition(equality.clone());
        for i in 0..size {
            context = context.assume_condition(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(100000 + 2 * i)),
                    OldMachineTerm::Variable(Variable(100001 + 2 * i)),
                ),
                true,
            );
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.restricted_to_facts(&[], std::slice::from_ref(&equality))
        });
        assert!(selected.contains_known(&equality));
        assert!(!selected.contains_known(&Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(100000)),
                OldMachineTerm::Variable(Variable(100001)),
            ),
            true
        )));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 8),
        "restriction reconstructed ambient edges: {samples:?}"
    );
}

#[test]
fn call_input_retention_does_not_derive_memory_or_scan_unrelated_facts() {
    let memory = SymbolicMemory::new();
    let base = OldAddress {
        base: "retention_data".into(),
        offset: OldAddressOffset::Constant(0).into(),
    };
    let held = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: 8u32.into(),
        wide: false,
    };
    let derived = Proposition::MemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(1u32.into()),
        bytes: 4u32.into(),
        wide: false,
    };
    let known = Proposition::condition_is(
        OldConditionTerm::equal(OldMachineTerm::Variable(Variable(990_000)), 1u32.into()),
        true,
    );
    let missing = Proposition::condition_is(
        OldConditionTerm::equal(OldMachineTerm::Variable(Variable(990_001)), 1u32.into()),
        true,
    );
    let disjunction = Proposition::Or(Box::new(known.clone()), Box::new(missing.clone()));
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut assumptions = PureFactContext::new()
            .assume_proposition(held.clone())
            .assume_proposition(known.clone());
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(991_000 + index)),
                    0u32.into(),
                ),
                true,
            );
        }
        // Shared indexes initialize once from admitted fact deltas. Keep
        // that preparation separate from repeated retention lookups, as in
        // the existing stated-proposition-index scaling regressions.
        assumptions.build_stated_proposition_index();
        let Proposition::ConditionIs(condition, _) = &missing else {
            unreachable!()
        };
        assert_eq!(
            assumptions.difference_decision(condition.old_form(), &[]),
            None
        );
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let retain = |goal| {
                crate::kernel::reasoning::path_facts::call_input_fact_is_already_known(
                    &assumptions,
                    goal,
                )
            };
            assert!(retain(&held));
            assert!(retain(&disjunction));
            assert!(!retain(&missing));
            assert!(!retain(&derived), "retention must not redo range coverage");
        });
        samples.push((size, work));
    }
    let baseline = samples[0].1;
    for (size, work) in &samples {
        let allowance = baseline + 32 * ((*size / 4) as usize).ilog2() as usize;
        assert!(
            *work <= allowance,
            "retention grew with unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn finite_forall_requested_prefix_has_constant_work_across_domain_sizes() {
    let mut samples = Vec::new();
    for width in [16, 1024, 1_000_000, 1_000_000_000] {
        let k = Variable(92_112);
        let goal = forall_int32(
            k,
            Proposition::Implies(
                Box::new(int32_half_open_bound(
                    &OldMachineTerm::Variable(k),
                    0,
                    width,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Constant(true),
                    true,
                )),
            ),
        );
        let (instances, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::finite_forall_goal_instances(&goal, false)
                .unwrap()
                .take(2)
                .collect::<Vec<_>>()
        });
        assert_eq!(
            instances
                .iter()
                .map(|(values, _)| values.clone())
                .collect::<Vec<_>>(),
            vec![vec![0], vec![1]]
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn equality_aware_pointer_fact_queries_ignore_unrelated_facts_and_old_states() {
    let target = OldAddress::symbolic_function(Variable(122_000));
    let alias = OldAddress::symbolic_function(Variable(122_001));
    let fact = |pointer: OldAddress, state: ExecutionState| Proposition::Predicate {
        name: FunctionContract::predicate_name_for("Selected"),
        arguments: vec![
            Term::ExecutionState(Box::new(state)),
            Term::ProgramValue(
                (ProgramValue::typed_pointer(
                    pointer,
                    ProgramType::FunctionPointer(CallbackSignature::from_encoded(122_000)),
                ))
                .into(),
            ),
        ],
    };
    let goal = fact(alias.clone(), ExecutionState::new());
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let mut context =
            PureFactContext::new().assume_proposition(fact(target.clone(), ExecutionState::new()));
        for index in 0..size {
            context = context.assume_proposition(fact(
                OldAddress::symbolic_function(Variable(123_000 + index)),
                ExecutionState::new(),
            ));
            // Same predicate and pointer, but different memory versions must
            // not turn a selected query into a scan of state history.
            context = context.assume_proposition(fact(
                target.clone(),
                ExecutionState::new()
                    .with_memory(SymbolicMemory::new().with_block(format!("epoch-{index}"), 4)),
            ));
        }
        context = context.assume_condition(
            OldConditionTerm::AddressEqual(Box::new(target.clone()), Box::new(alias.clone())),
            true,
        );
        assert!(context.contains_known(&goal)); // warm selected registration
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert!(context.contains_known(&goal));
                assert_eq!(context.function_contract_facts_for(&alias).count(), 1);
            }
        });
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] == pair[0]),
        "selected pointer predicate work grew with unrelated facts: {samples:?}"
    );
}

/// One shape of related facts for [`decide_work_over_related_facts`]: the
/// facts at size `n`, and queries with their expected answers.
type RelatedFacts = fn(usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>);

/// The deterministic work and fuel one fresh context's decisions spend.
fn decide_work_over_related_facts(shape: RelatedFacts, n: usize) -> (usize, usize) {
    let (facts, queries) = shape(n);
    crate::instrumentation::take_decision_fuel_peak();
    let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
        for (query, expected) in &queries {
            assert_eq!(facts.decide(query), *expected, "{query:?} at size {n}");
        }
    });
    (work, crate::instrumentation::take_decision_fuel_peak())
}

fn related_variable(id: usize) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(91_000 + id as u64))
}

/// `x0 < x1 < ... < xn`, asked both ways along the chain and against an
/// unrelated value.
fn related_order_chain(n: usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>) {
    let mut facts = PureFactContext::new();
    for index in 0..n {
        facts = facts.assume_condition(
            OldConditionTerm::signed_less_than(
                related_variable(index),
                related_variable(index + 1),
            ),
            true,
        );
    }
    let (first, last, other) = (
        related_variable(0),
        related_variable(n),
        related_variable(n + 1),
    );
    // The difference graph refutes the reversed chain only within its
    // per-query edge limit; past it the reversal is left undecided, and a
    // proof states an intermediate bound.
    let reversed = (n <= crate::kernel::difference_graph::EDGE_LIMIT).then_some(false);
    let queries = vec![
        (
            OldConditionTerm::signed_less_than(first.clone(), last.clone()),
            Some(true),
        ),
        (
            OldConditionTerm::signed_less_than(last.clone(), first),
            reversed,
        ),
        (OldConditionTerm::signed_less_than(last, other), None),
    ];
    (facts, queries)
}

/// `x0 <= x1 <= ... <= xn <= x0`: a cycle, so every member equals every
/// other.
fn related_order_cycle(n: usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>) {
    let mut facts = PureFactContext::new();
    for index in 0..=n {
        let next = if index == n { 0 } else { index + 1 };
        facts = facts.assume_condition(
            OldConditionTerm::signed_less_equal(related_variable(index), related_variable(next)),
            true,
        );
    }
    let (first, last, other) = (
        related_variable(0),
        related_variable(n),
        related_variable(n + 1),
    );
    let queries = vec![
        (
            OldConditionTerm::signed_less_equal(last.clone(), first.clone()),
            Some(true),
        ),
        (
            OldConditionTerm::signed_less_than(first, last.clone()),
            Some(false),
        ),
        (OldConditionTerm::signed_less_than(last, other), None),
    ];
    (facts, queries)
}

/// Two equality classes `x == a1 == ... == an` and `y == b1 == ... == bn`,
/// with one order fact between two members.
fn related_equality_classes(n: usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>) {
    let (x, y) = (related_variable(0), related_variable(1));
    let mut facts = PureFactContext::new();
    for index in 0..n {
        facts = facts
            .assume_condition(
                OldConditionTerm::equal(x.clone(), related_variable(10 + 2 * index)),
                true,
            )
            .assume_condition(
                OldConditionTerm::equal(y.clone(), related_variable(11 + 2 * index)),
                true,
            );
    }
    let (a, b) = (
        related_variable(10 + 2 * (n - 1)),
        related_variable(11 + 2 * (n - 1)),
    );
    facts = facts.assume_condition(OldConditionTerm::signed_less_than(a, b), true);
    let other = related_variable(10 + 2 * n);
    let queries = vec![
        (
            OldConditionTerm::signed_less_than(x.clone(), y.clone()),
            Some(true),
        ),
        (
            OldConditionTerm::signed_less_equal(y.clone(), x.clone()),
            Some(false),
        ),
        (OldConditionTerm::signed_less_than(y, other), None),
    ];
    (facts, queries)
}

/// `s0 < s1 < ... < sn` with each `si = v_2i + v_2i+1`: an order chain whose
/// endpoints are sums, which the walk files by their equality-graph class.
fn related_sum_order_chain(n: usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>) {
    let sum = |index: usize| {
        OldMachineTerm::add(related_variable(2 * index), related_variable(2 * index + 1))
    };
    let mut facts = PureFactContext::new();
    for index in 0..n {
        facts = facts.assume_condition(
            OldConditionTerm::signed_less_than(sum(index), sum(index + 1)),
            true,
        );
    }
    // Within the difference graph's per-query edge limit the chain is
    // proved; past it the query is left undecided.
    let chained = (n <= crate::kernel::difference_graph::EDGE_LIMIT).then_some(true);
    let queries = vec![
        (OldConditionTerm::signed_less_than(sum(0), sum(n)), chained),
        (
            OldConditionTerm::signed_less_than(sum(0), related_variable(10_000)),
            None,
        ),
    ];
    (facts, queries)
}

/// Two equality classes `x == v_i` and `y == w_i`, with one disequality
/// between their last members.
fn related_disequal_classes(n: usize) -> (PureFactContext, Vec<(OldConditionTerm, Option<bool>)>) {
    let (x, y) = (related_variable(0), related_variable(1));
    let mut facts = PureFactContext::new();
    for index in 0..n {
        facts = facts
            .assume_condition(
                OldConditionTerm::equal(x.clone(), related_variable(10 + 2 * index)),
                true,
            )
            .assume_condition(
                OldConditionTerm::equal(y.clone(), related_variable(11 + 2 * index)),
                true,
            );
    }
    let (a, b) = (
        related_variable(10 + 2 * (n - 1)),
        related_variable(11 + 2 * (n - 1)),
    );
    facts = facts.assume_condition(OldConditionTerm::equal(a, b), false);
    let queries = vec![
        (OldConditionTerm::equal(x.clone(), y.clone()), Some(false)),
        (OldConditionTerm::signed_less_than(x, y), None),
    ];
    (facts, queries)
}

/// Catches a condition decision whose work grows faster than linearly in
/// facts related to the query:
/// the unrelated-fact scaling tests above cannot see it. Each shape's work
/// and fuel at 64 related facts stay within a linear factor of its work at
/// 16, with headroom for logarithmic indexing.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn decide_work_is_near_linear_in_related_facts() {
    for (name, shape) in [
        ("order chain", related_order_chain as RelatedFacts),
        ("order cycle", related_order_cycle as RelatedFacts),
        ("equality classes", related_equality_classes as RelatedFacts),
        // A node that is a sum once read every order fact: 35,208 units at
        // 64 facts.
        ("sum order chain", related_sum_order_chain as RelatedFacts),
        // Finding the disequality between the classes once read every pair
        // of their members' spellings: 450,466 units at 128 members.
        (
            "disequal equality classes",
            related_disequal_classes as RelatedFacts,
        ),
    ] {
        // Both sizes are past the difference graph's per-query edge limit
        // (32), so a chain query costs the limit at either size and the
        // comparison measures the growth with the facts, not the step from
        // a chain the graph follows whole to one it cuts off.
        let (small_work, small_fuel) = decide_work_over_related_facts(shape, 64);
        let (large_work, large_fuel) = decide_work_over_related_facts(shape, 256);
        eprintln!(
            "{name}: work {small_work} -> {large_work}, fuel {small_fuel} -> {large_fuel} at 64 -> 256 facts"
        );
        assert!(
            large_work <= small_work * 8 + 64,
            "{name}: decision work grew from {small_work} to {large_work} for 4x the related facts"
        );
        assert!(large_fuel < crate::instrumentation::DECISION_FUEL_LIMIT);
    }
}

/// Catches a decision that runs past its fuel, or keeps what a fuel stop
/// left undecided. With no order walk left, deciding along a 16-fact chain
/// reads at most two units of fuel, so one unit stops it: it ends undecided,
/// and the same query on the same facts is then decided under the ordinary
/// fuel.
#[test]
fn a_decision_that_spends_its_fuel_ends_undecided_and_is_not_memoized() {
    let (facts, queries) = related_order_chain(16);
    let (query, expected) = &queries[0];
    let starved = crate::instrumentation::with_decision_fuel(1, || facts.decide(query));
    assert_eq!(starved, None, "one unit of fuel cannot decide the chain");
    assert_eq!(*expected, Some(true));
    assert_eq!(facts.decide(query), *expected);
}

/// Direct interval summaries ignore unrelated conditions, including compound endpoints.
#[test]
fn direct_compound_interval_ignores_unrelated_facts() {
    let variable = |id: u64| OldMachineTerm::Variable(Variable(94_000 + id));
    let x = OldMachineTerm::multiply(variable(0), variable(2));
    let mut visited = Vec::new();
    for size in [16u64, 64, 256] {
        let mut facts = PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_than(x.clone(), variable(1)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(x.clone(), OldMachineTerm::constant(5)),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_greater_than(
                    x.clone(),
                    OldMachineTerm::constant(i32::MIN as u32),
                ),
                true,
            );
        for index in 0..size {
            facts = facts.assume_condition(
                OldConditionTerm::signed_less_than(
                    variable(100 + index),
                    OldMachineTerm::constant(1000),
                ),
                true,
            );
        }
        let (interval, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.indexed_constant_interval(&x)
        });
        visited.push(work);
        assert_eq!(interval, Some((i64::from(i32::MIN) + 1, 5)));
    }
    eprintln!("facts with one side, visits at 16/64/256 unrelated bounds: {visited:?}");
    assert!(
        visited.windows(2).all(|pair| pair[0] == pair[1]),
        "the lookup should visit the same facts at every size: {visited:?}"
    );
}

#[test]
fn integer_match_rewrite_lookup_scales_with_its_selected_sources() {
    for related in [false, true] {
        let mut previous = None;
        for size in [8u64, 16, 32, 64] {
            let ty = maybe_int32_type();
            let model = |id| AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Variable(Variable(id)),
            };
            let sources = (0..size)
                .map(|index| {
                    Proposition::Equal(
                        Term::Algebraic(
                            model(if related { 90_000 } else { 90_000 + index }).into(),
                        ),
                        Term::Algebraic(
                            maybe_constructor(
                                &ty,
                                "Some",
                                vec![ProgramValue::Int32(OldMachineTerm::Variable(Variable(
                                    100_000 + index,
                                )))],
                            )
                            .into(),
                        ),
                    )
                })
                .collect::<Vec<_>>();
            let facts = crate::kernel::proof::PureFactStore::from_ordered(&sources);
            let matched = crate::kernel::IntegerTerm::AlgebraicMatch {
                scrutinee: Box::new(model(90_000)),
                arms: vec![
                    crate::kernel::AlgebraicIntegerMatchArm {
                        binding_names: Default::default(),
                        variant: "None".into(),
                        bindings: vec![],
                        body: crate::kernel::IntegerTerm::constant_i64(0).into(),
                    },
                    crate::kernel::AlgebraicIntegerMatchArm {
                        binding_names: Default::default(),
                        variant: "Some".into(),
                        bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                            OldMachineTerm::Variable(Variable(200_000)),
                        ))],
                        body: crate::kernel::IntegerTerm::constant_i64(1).into(),
                    },
                ],
            };
            let goal = Proposition::condition_is(
                OldConditionTerm::IntegerEqual(
                    matched.into(),
                    crate::kernel::IntegerTerm::constant_i64(1).into(),
                ),
                true,
            );
            let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.algebraic_equalities_mentioning(&goal)
            });
            assert_eq!(selected.len(), if related { size as usize } else { 1 });
            assert!(selected.contains(&sources[0]));
            if let Some(previous) = previous {
                assert!(
                    work <= previous * 5 / 2 + 16,
                    "related={related}, size={size}: {previous} -> {work}"
                );
            }
            previous = Some(work);
        }
    }
}
