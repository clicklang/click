use super::*;

#[test]
fn iterated_exposure_preserves_the_frame_without_admission_or_normalization() {
    for unfold_clause in [false, true] {
        for axis in ["owners", "aliases", "same-block aliases", "range premises"] {
            let mut samples = Vec::new();
            let mut preparation = Vec::new();
            for count in [4_u64, 16, 64] {
                let _session = crate::kernel::VerificationSession::enter();
                let base = Address {
                    base: AddressBase::Heap(9_970_000),
                    offset: AddressOffset::Constant(0),
                };
                let guards = Address {
                    base: "local:iterated-exposure-guards".into(),
                    offset: AddressOffset::Constant(0),
                };
                let template = IteratedMemory::new(
                    "cells",
                    base.clone(),
                    4,
                    1,
                    0,
                    1,
                    0u32.into(),
                    4u32.into(),
                    IteratedGuard::new(guards.clone(), ProgramType::Int32, 4, true, 0u32.into()),
                )
                .unwrap();
                let mut facts = PureFactContext::new();
                let mut owners = Vec::new();
                for index in 0..count {
                    if axis == "owners" {
                        owners.push(ResourceFact::own_memory(MemoryRange::new(
                            base.clone(),
                            (32 + index as u32 * 2).into(),
                            (33 + index as u32 * 2).into(),
                        )));
                    } else if axis != "range premises" {
                        let alias = if axis == "aliases" {
                            Address::symbolic(Variable(9_980_000 + index))
                        } else {
                            Address {
                                base: base.base.clone(),
                                offset: AddressOffset::Variable(Variable(9_980_000 + index)),
                            }
                        };
                        facts = facts.assume_condition(
                            ConditionTerm::address_equal(base.clone(), alias),
                            true,
                        );
                    }
                }
                // A retained owner and its supported observation share the data
                // block. Neither its identity nor its dependency may be rebuilt.
                let retained = ResourceFact::own_memory(MemoryRange::new(
                    base.clone(),
                    200u32.into(),
                    201u32.into(),
                ));
                owners.push(retained.clone());
                let (resources, inserted) = ResourceContext::new_with_equalities(&facts)
                    .unchecked_with_facts_and_occurrences(owners);
                let retained_source = inserted.last().unwrap().1;
                let memory = SymbolicMemory::new()
                    .with_block(guards.base.clone(), 16)
                    .initialize_scalar_array(
                        &guards,
                        ProgramType::Int32,
                        4,
                        ProgramValue::Int32(0u32.into()),
                        false,
                    )
                    .unwrap();
                let (resources, observed) = resources
                    .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                        retained_source,
                        &retained,
                        [ResourceFact::view_memory(MemoryRange::new(
                            base.clone(),
                            200u32.into(),
                            201u32.into(),
                        ))],
                        &memory,
                    );
                let view = observed[0].1;
                let resources = resources.unchecked_with_facts([
                    ResourceFact::own_memory(template.guard_range()),
                    ResourceFact::own(Resource::iterated(template.clone())),
                ]);
                resources.synchronize_memory_equalities(&facts);
                let state = ExecutionState::new()
                    .with_memory(memory)
                    .with_resource_context(resources);
                if unfold_clause && axis == "range premises" {
                    for premise in 0..count {
                        let var = Variable(9_990_000);
                        let index = OldMachineTerm::Variable(var);
                        let lower = ConditionTerm::signed_less_equal(1u32.into(), index.clone());
                        let upper = ConditionTerm::signed_less_than(
                            index.clone(),
                            (32 + premise as u32).into(),
                        );
                        let cell = guard_cell_value(&state, &template, &index, &facts).unwrap();
                        facts = facts.assume_proposition(crate::kernel::quantifiers::test_forall(
                            Default::default(),
                            var,
                            Sort::ProgramInt32,
                            Proposition::Implies(
                                Box::new(Proposition::And(
                                    Box::new(Proposition::condition_is(lower, true)),
                                    Box::new(Proposition::condition_is(upper, true)),
                                )),
                                Box::new(Proposition::condition_is(
                                    ConditionTerm::equal(cell, 0u32.into()),
                                    true,
                                )),
                            ),
                        ));
                    }
                    assert!(
                        prepare_iterated_clause_unfold(&state, &template, &facts).is_err(),
                        "a different range is not the explicit whole-range premise"
                    );
                }
                if unfold_clause {
                    // Whole-clause unfolding's explicit whole-range premise: a selected
                    // element's known value alone does not prove every guard.
                    let var = Variable(9_990_000);
                    let index = OldMachineTerm::Variable(var);
                    let lower = ConditionTerm::signed_less_equal(0u32.into(), index.clone());
                    let upper = ConditionTerm::signed_less_than(index.clone(), 4u32.into());
                    let hypotheses = facts
                        .clone()
                        .assume_condition(lower.clone(), true)
                        .assume_condition(upper.clone(), true);
                    let value = guard_cell_value(&state, &template, &index, &hypotheses).unwrap();
                    facts = facts.assume_proposition(crate::kernel::quantifiers::test_forall(
                        Default::default(),
                        var,
                        Sort::ProgramInt32,
                        Proposition::Implies(
                            Box::new(Proposition::And(
                                Box::new(Proposition::condition_is(lower, true)),
                                Box::new(Proposition::condition_is(upper, true)),
                            )),
                            Box::new(Proposition::condition_is(
                                ConditionTerm::Compare {
                                    format: MachineIntegerType::Int32,
                                    relation: CompareRelation::Equal,
                                    left: Box::new(value),
                                    right: Box::new(0u32.into()),
                                },
                                true,
                            )),
                        ),
                    ));
                }
                let range = if unfold_clause {
                    template.covering_range().unwrap()
                } else {
                    template.element_range(&1u32.into())
                };
                let step = if unfold_clause {
                    IteratedStep::UnfoldClause {
                        template: template.clone(),
                    }
                } else {
                    IteratedStep::UnfoldSlot {
                        template: template.clone(),
                        index: 1u32.into(),
                    }
                };
                let prepared = if unfold_clause {
                    let (prepared, work) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            prepare_iterated_clause_unfold(&state, &template, &facts).unwrap()
                        });
                    preparation.push(work);
                    Some(prepared)
                } else {
                    None
                };
                let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "iterated footprint exposure",
                    );
                    let next = match prepared {
                        Some(prepared) => state.clone().with_resource_context(prepared.install()),
                        None => apply_iterated_step(&state, &step, &facts).unwrap(),
                    };
                    assert!(
                        next.resources()
                            .satisfies_fact(&ResourceFact::own_memory(range), &facts)
                    );
                    next
                });
                assert_eq!(
                    next.resources().owned_fact_for_occurrence(retained_source),
                    Some(&retained)
                );
                assert!(next.resources().view_fact_for_occurrence(view).is_some());
                let removed = next
                    .resources()
                    .clone()
                    .without_exact_representation_for_occurrence(retained_source)
                    .unwrap();
                assert!(removed.view_fact_for_occurrence(view).is_none());
                assert!(
                    state
                        .resources()
                        .contains_exact_representation(&ResourceFact::own(Resource::iterated(
                            template
                        )))
                );
                assert!(apply_iterated_step(&next, &step, &facts).is_err());
                samples.push(work);
            }
            eprintln!(
                "iterated exposure unfold_clause={unfold_clause}, {axis}: {samples:?}; guard preparation={preparation:?}"
            );
            assert!(
                preparation.iter().all(|work| *work <= preparation[0] + 32),
                "unfold_clause guard preparation {axis}: {preparation:?}"
            );
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 64),
                "{unfold_clause}, {axis}: {samples:?}"
            );
        }
    }
}

#[test]
fn indexed_slot_selection_ignores_other_clauses_at_the_same_base() {
    let template = |lower: u32| {
        IteratedMemory::new(
            "slots",
            Address::symbolic(Variable(8_000)),
            4,
            2,
            0,
            2,
            lower.into(),
            (lower + 2).into(),
            IteratedGuard::new(
                Address::symbolic(Variable(8_001)),
                ProgramType::Int32,
                4,
                true,
                0u32.into(),
            ),
        )
        .unwrap()
    };
    let selected = template(0);
    let missing = template(1);
    let held = ResourceFact::own(Resource::iterated(selected.with_hole(0u32.into())));
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let resources = (1..=size).fold(
            ResourceContext::new().unchecked_with_fact(held.clone()),
            |resources, i| {
                resources
                    .unchecked_with_fact(ResourceFact::own(Resource::iterated(template(2 * i))))
            },
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(resources.owned_iterated_clause(&selected), Ok(&held));
            assert!(resources.owned_iterated_clause(&missing).is_err());
        });
        samples.push(work);
        let ambiguous =
            resources.unchecked_with_fact(ResourceFact::own(Resource::iterated(selected.clone())));
        assert!(ambiguous.owned_iterated_clause(&selected).is_err());
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] + 8),
        "{samples:?}"
    );
}
