//! Checked local creation of a memory-backed counted population.
//!
//! This is an allocation rule, not definitional equality of two population
//! states. The new head must replace its actual owned body, and its invariant
//! must already follow from the input facts at the proposed population size.

use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn check(
    definition: &CCompositeResourceDefinition,
    before: &CState,
    before_facts: &ProofFacts,
    selected: &CResourceFact,
    after: &CState,
    after_facts: &ProofFacts,
) -> Result<Option<Vec<CheckedResourceDeltaProof>>, String> {
    let Some(added) = after
        .counted_populations
        .single_insertion_from(&before.counted_populations)
    else {
        return Ok(None);
    };
    if !definition.is_counted_population() || added.family_observation_marker {
        return Ok(None);
    }
    let CResource::Composite { name, arguments } = selected.resource() else {
        return Ok(None);
    };
    let assumptions = before_facts.assumptions();
    if added.name != *name
        || added.arguments != *arguments
        || selected.owned_quantity_term() != Some(&added.count)
        || !selected.has_proven_positive_quantity(assumptions)
    {
        // Other rewrites may materialize a zero ledger entry on finalization.
        // They remain subject to the existing definitional rewrite checker.
        return Ok(None);
    }
    if definition.recursive
        || definition.parameters().len() != arguments.len()
        || definition.condition.is_some()
        || definition.matched.is_some()
        || definition.instance_schema.is_some()
        || !definition.children.is_empty()
        || !definition.witnesses.is_empty()
        || !definition.resource_parameters().is_empty()
        || definition.contains().is_empty()
    {
        return Err("local population initialization requires an unconditional memory body".into());
    }
    if before.has_counted_population_unary_pointer_alias(name, arguments, assumptions)? {
        return Err("cannot initialize an existing resource population".into());
    }
    if before.population_access != Default::default() {
        return Err("close the open population body before initializing a population".into());
    }
    if before
        .resources()
        .has_population_head_alias(name, arguments, assumptions)?
    {
        return Err("population initialization cannot duplicate an existing resource".into());
    }

    // All roots outside this resource exchange and the one ledger insertion
    // must remain unchanged. Clones retain persistent roots, not state history.
    let mut unchanged = after.clone();
    unchanged.resources = before.resources.clone();
    unchanged.counted_populations = before.counted_populations.clone();
    if unchanged != *before {
        return Err("population initialization changed memory or unrelated execution state".into());
    }

    // Build a declaration-local evaluation environment. Do not copy the
    // enclosing function's locals or its project-wide declaration environment.
    let mut evaluation = CState::new().with_memory(before.memory().clone());
    evaluation.counted_populations = after.counted_populations.clone();
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let value = argument
            .as_c_value()
            .filter(|value| value.c_type() == parameter.c_type())
            .ok_or("population initialization has an invalid argument")?;
        evaluation.locals.set_typed(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
        );
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let mut expected = before.resources().clone();
    let mut body = ResourceContext::new_with_equalities(assumptions);
    for spec in definition.contains() {
        let child = crate::kernel::functions::evaluate_function_resource_spec(
            &evaluation,
            spec,
            assumptions,
            &mut budget,
        )
        .map_err(|_| "cannot evaluate the population's owned body")?
        .map_err(|_| "cannot evaluate the population's owned body")?;
        let CResourceFact::Own(CResource::Memory(range), _) = &child else {
            return Err("local population initialization requires owned memory in its body".into());
        };
        if !range.byte_footprint().1.as_const().is_some_and(|n| n > 0) {
            return Err(
                "local population initialization requires nonempty fixed memory ranges".into(),
            );
        }
        if let Some(ledger) = before.loan_ledger() {
            ledger
                .permits_memory_access_with_assumptions(range, assumptions)
                .map_err(
                    |_| "population initialization requires the owned body free of active borrows",
                )?;
        }
        let (_, source) = expected
            .directly_supporting_owned_entry(&child, assumptions)
            .ok_or("population initialization requires its owned memory body")?;
        if !matches!(source.resource(), CResource::Memory(_))
            || expected.exact_projection_support(source).is_some()
        {
            return Err(
                "population initialization requires independent ownership of its memory body"
                    .into(),
            );
        }
        expected = expected
            .without_fact_incrementally(&child, assumptions)
            .ok_or("population initialization requires its owned memory body")?;
        body = body
            .try_compose_with_facts_delaying_normalization([child], assumptions)
            .map_err(|_| "population initialization has overlapping memory requirements")?;
    }
    let (occurrence, _) = after
        .resources()
        .unique_owned_occurrence_for_fact(selected)
        .ok_or("population initialization requires one new owned population head")?;
    if before
        .resources()
        .owned_fact_for_occurrence(occurrence)
        .is_some()
    {
        return Err("population initialization requires a new resource occurrence".into());
    }
    let residual = after
        .resources()
        .clone()
        .without_checked_fold_projections(occurrence, selected, &body, after.memory(), assumptions)
        .ok_or("population initialization introduced an observation outside its owned body")?
        .without_exact_representation_for_occurrence(occurrence)
        .ok_or("population initialization lost its new population head")?;
    if !expected.same_exchange_from(&residual, before.resources()) {
        return Err(
            "population initialization must consume its body and preserve the remaining resources"
                .into(),
        );
    }

    let singleton =
        ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(selected.clone());
    evaluation.resources = body.clone();
    let obligations = crate::kernel::functions::evaluate_resource_population_fact_propositions(
        &singleton,
        std::slice::from_ref(definition),
        &evaluation,
        assumptions,
        true,
    )
    .ok_or("cannot evaluate the population invariant at its initial quantity")?;
    let mut allowed = Vec::new();
    for obligation in obligations {
        if !crate::kernel::api::contract_certification::certification_proves_proposition(
            assumptions,
            &obligation.proposition,
        ) {
            return Err(format!(
                "population initialization requires {}",
                obligation
                    .source_fact
                    .as_deref()
                    .unwrap_or("its body invariant at the initial quantity")
            ));
        }
        allowed.push(obligation.proposition);
    }
    allowed.extend(body.observable_facts_assuming_valid(assumptions));
    allowed.extend(singleton.observable_facts_assuming_valid(assumptions));
    allowed.push(Proposition::CResourceComposition(body.clone()));
    // Resource containment/loadability follows from the checked body exchange,
    // not from a caller-supplied declaration fact.
    for child in body.facts() {
        allowed.push(Proposition::CResourceContains {
            parent: selected.resource().clone(),
            child: child.resource().clone(),
        });
        let range = child
            .memory_range()
            .expect("the checked body contains only memory");
        allowed.extend(crate::kernel::memory_range_extent_guard_spellings(range));
        let (base, bytes) = range.byte_footprint();
        allowed.push(Proposition::CMemoryLoadable {
            memory: after.memory().clone(),
            base,
            bytes,
        });
    }
    let validated = allowed.iter().fold(assumptions.clone(), |facts, fact| {
        facts.assume_proposition(fact.clone())
    });
    let premises = ResourceDeltaPremises::new(&allowed);
    let mut proofs = Vec::new();
    for fact in after_facts
        .introduced_since(before_facts)
        .ok_or("population initialization facts must extend the input facts")?
    {
        if validated.proves_exact(&fact)
            || resource_composition_is_supported_by(&fact, after.resources(), assumptions)
        {
            continue;
        }
        proofs.push(
            premises
                .prove_with_facts(&fact, &validated)
                .ok_or("population initialization introduced an unproved fact")?,
        );
    }
    Ok(Some(proofs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::*;

    fn fixture() -> (CFunction, CState, CResourceFact, CState) {
        let pointer = Pointer {
            block: "cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let selected = CResourceFact::own_quantity(
            CResource::Composite {
                name: "remaining".into(),
                arguments: vec![CValue::pointer(pointer.clone()).into()].into(),
            },
            Bitvector32Term::Constant(3),
        );
        let body = CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let definition = CCompositeResourceDefinition::counted_population(
            "remaining",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![SpecProposition::Comparison {
                left: SpecExpression::CountedResourceCount {
                    name: "remaining".into(),
                    arguments: vec![Some(SpecExpression::CExpression(c_variable("p")))],
                },
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(3)),
            }],
        );
        let function = c_function(
            CType::Void,
            "test",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let before = CState::new()
            .with_memory(CMemory::new().with_block("cell", 4))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(body));
        let CResource::Composite { arguments, .. } = selected.resource() else {
            unreachable!()
        };
        let exchanged = before
            .resources()
            .clone()
            .without_exact_representation(&before.resources().facts()[0])
            .unwrap()
            .unchecked_with_fact(selected.clone());
        let after = before
            .clone()
            .with_resource_context(exchanged)
            .with_counted_population("remaining", arguments.clone(), Bitvector32Term::Constant(3));
        (function, before, selected, after)
    }

    fn accepts(
        function: &CFunction,
        before: &CState,
        selected: &CResourceFact,
        after: &CState,
    ) -> bool {
        let result = CheckedResourceRewrite::check(
            function,
            before,
            &ProofFacts::default(),
            selected,
            after,
            &ProofFacts::default(),
            &CheckedCallEvents::default(),
        );
        result.is_ok()
    }

    #[test]
    fn population_cleanup_requires_the_entire_positive_population() {
        let (function, body, selected, population) = fixture();
        let exposed = population.clone().with_resource_context(
            population
                .resources()
                .clone()
                .without_exact_representation(&selected)
                .unwrap()
                .unchecked_with_facts(body.resources().facts().iter().cloned()),
        );
        assert!(accepts(&function, &population, &selected, &exposed));
        for quantity in [0, 1, 2, 4] {
            let partial = CResourceFact::own_quantity(
                selected.resource().clone(),
                Bitvector32Term::Constant(quantity),
            );
            let partial_state = population
                .clone()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(partial.clone()));
            assert!(
                !accepts(&function, &partial_state, &partial, &exposed),
                "quantity {quantity} must not recover a population of three"
            );
        }
        let CResource::Composite { name, arguments } = selected.resource() else {
            unreachable!()
        };
        // Inventing a restoration scope cannot turn a destructive unfold
        // into a valid borrow: an opening must retain its membership units.
        for quantity in [0, 1, 3] {
            let member = CResourceFact::own_quantity(
                selected.resource().clone(),
                Bitvector32Term::Constant(quantity),
            );
            let input = population
                .clone()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(member.clone()));
            let output = input
                .clone()
                .with_resource_context(
                    input
                        .resources()
                        .clone()
                        .without_exact_representation(&member)
                        .unwrap()
                        .unchecked_with_facts(body.resources().facts().iter().cloned()),
                )
                .open_population_body(name.clone(), arguments.clone())
                .unwrap();
            assert!(
                !accepts(&function, &input, &member, &output),
                "an opening must retain its {quantity} units"
            );
        }
        let open = population
            .clone()
            .open_population_body(name.clone(), arguments.clone())
            .unwrap();
        let mut exposed_open = exposed.clone();
        exposed_open.population_access = open.population_access.clone();
        assert!(!accepts(&function, &open, &selected, &exposed_open));
    }

    #[test]
    fn local_population_initialization_certifies_only_the_owned_body_exchange() {
        let (function, before, selected, after) = fixture();
        assert!(accepts(&function, &before, &selected, &after));
        let (occurrence, _) = after
            .resources()
            .unique_owned_occurrence_for_fact(&selected)
            .unwrap();
        let body_view = before.resources().facts()[0].core().unwrap();
        let projected = after.clone().with_resource_context(
            after
                .resources()
                .clone()
                .unchecked_with_supported_facts_from_occurrence_with_memory(
                    occurrence,
                    &selected,
                    [body_view],
                    after.memory(),
                ),
        );
        assert!(accepts(&function, &before, &selected, &projected));
        let unrelated_view = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: "other".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let forged_projection = after.clone().with_resource_context(
            after
                .resources()
                .clone()
                .unchecked_with_supported_facts_from_occurrence_with_memory(
                    occurrence,
                    &selected,
                    [unrelated_view],
                    after.memory(),
                ),
        );
        assert!(!accepts(&function, &before, &selected, &forged_projection));
        let retained = after.clone().with_resource_context(
            after
                .resources()
                .clone()
                .unchecked_with_facts(before.resources().facts().to_vec()),
        );
        assert!(
            !accepts(&function, &before, &selected, &retained),
            "must consume the memory body"
        );
        let absent = before.clone().with_resource_context(ResourceContext::new());
        assert!(
            !accepts(&function, &absent, &selected, &after),
            "must own the memory body"
        );
        let changed_memory = after
            .clone()
            .with_memory(CMemory::new().with_block("other", 4));
        assert!(!accepts(&function, &before, &selected, &changed_memory));
        let extra = after.clone().with_counted_population(
            "other",
            vec![].into(),
            Bitvector32Term::Constant(9),
        );
        assert!(
            !accepts(&function, &before, &selected, &extra),
            "only the selected population may be allocated"
        );
        let CResource::Composite { arguments, .. } = selected.resource() else {
            unreachable!()
        };
        for count in [0, 1, 4] {
            let existing = before.clone().with_counted_population(
                "remaining",
                arguments.clone(),
                Bitvector32Term::Constant(count),
            );
            assert!(
                !accepts(&function, &existing, &selected, &after),
                "existing count {count} cannot be reset"
            );
        }
    }

    #[test]
    fn local_population_initialization_does_not_assume_its_invariant() {
        let (function, before, selected, after) = fixture();
        let CResource::Composite { arguments, .. } = selected.resource() else {
            unreachable!()
        };
        let wrong_selected =
            CResourceFact::own_quantity(selected.resource().clone(), Bitvector32Term::Constant(2));
        let wrong_resources = before
            .resources()
            .clone()
            .without_exact_representation(&before.resources().facts()[0])
            .unwrap()
            .unchecked_with_fact(wrong_selected.clone());
        let wrong_after = after
            .with_resource_context(wrong_resources)
            .with_counted_population("remaining", arguments.clone(), Bitvector32Term::Constant(2));
        assert!(
            !accepts(&function, &before, &wrong_selected, &wrong_after),
            "body requires count three"
        );
        let false_fact = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
        let (_, before, selected, after) = fixture();
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &ProofFacts::default(),
                &selected,
                &after,
                &ProofFacts::default().with_fact(false_fact),
                &CheckedCallEvents::default()
            )
            .is_err()
        );
    }

    fn proposed_fold(before: &CState, selected: &CResourceFact) -> CState {
        let CResource::Composite { name, arguments } = selected.resource() else {
            unreachable!()
        };
        let body = before
            .resources()
            .facts()
            .iter()
            .find(|fact| fact.is_own() && matches!(fact.resource(), CResource::Memory(_)))
            .unwrap()
            .clone();
        let resources = before
            .resources()
            .clone()
            .without_exact_representation(&body)
            .unwrap()
            .unchecked_with_fact(selected.clone());
        before
            .clone()
            .with_resource_context(resources)
            .with_counted_population(
                name.clone(),
                arguments.clone(),
                selected.owned_quantity_term().unwrap().clone(),
            )
    }

    #[test]
    fn local_population_initialization_refuses_live_borrows_including_aliases() {
        for aliased in [false, true] {
            let (function, before, selected, _) = fixture();
            let owned = before.resources().facts()[0].clone();
            let range = owned.memory_range().unwrap();
            let borrowed_pointer = if aliased {
                Pointer::symbolic(Variable(780_001))
            } else {
                range.base().clone()
            };
            let borrowed = CResourceFact::own_memory(CMemoryRange::new(
                borrowed_pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ));
            let backing = ResourceContext::new()
                .unchecked_with_fact(borrowed.clone())
                .unique_owned_occurrence_for_fact(&borrowed)
                .unwrap()
                .0;
            let ledger = crate::kernel::loans::LoanLedger::new();
            let lender = ledger.fresh_participant().unwrap();
            let reader = ledger.fresh_participant().unwrap();
            let opening = ledger.lend(lender, reader, backing, borrowed).unwrap();
            let ledger = ledger.apply(&opening.transition).unwrap();
            let facts = if aliased {
                ProofFacts::default().with_fact(Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(range.base().clone(), borrowed_pointer),
                    true,
                ))
            } else {
                ProofFacts::default()
            };
            let before = before.with_loan_ledger(Some(ledger));
            let after = proposed_fold(&before, &selected);
            let error = CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &after,
                &facts,
                &CheckedCallEvents::default(),
            )
            .err()
            .expect("an active memory loan forbids initialization");
            assert!(error.contains("free of active borrows"), "{error}");
            let cleanup = after.clone().with_resource_context(
                after
                    .resources()
                    .clone()
                    .without_exact_representation(&selected)
                    .unwrap()
                    .unchecked_with_facts(before.resources().facts().iter().cloned()),
            );
            let error = CheckedResourceRewrite::check(
                &function,
                &after,
                &facts,
                &selected,
                &cleanup,
                &facts,
                &CheckedCallEvents::default(),
            )
            .err()
            .expect("an active memory loan forbids population cleanup");
            assert!(error.contains("free of active borrows"), "{error}");
        }
    }

    #[test]
    fn local_population_initialization_refuses_ledgerless_aliased_heads() {
        for owned_head in [false, true] {
            let (function, before, selected, _) = fixture();
            let pointer = before.resources().facts()[0]
                .memory_range()
                .unwrap()
                .base()
                .clone();
            let alias = Pointer::symbolic(Variable(780_002));
            let resource = CResource::Composite {
                name: "remaining".into(),
                arguments: vec![CValue::pointer(alias.clone()).into()].into(),
            };
            let head = if owned_head {
                CResourceFact::own(resource)
            } else {
                CResourceFact::View(resource)
            };
            let facts = ProofFacts::default().with_fact(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer, alias),
                true,
            ));
            let resources = before.resources().clone().unchecked_with_fact(head);
            let before = before.with_resource_context(resources);
            let after = proposed_fold(&before, &selected);
            let error = CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &after,
                &facts,
                &CheckedCallEvents::default(),
            )
            .err()
            .expect("an alias head prevents a second allocation even without a ledger row");
            assert!(error.contains("duplicate an existing resource"), "{error}");
        }
    }

    #[test]
    fn local_population_initialization_refuses_open_populations_and_empty_bodies() {
        let (function, before, selected, _) = fixture();
        let before = before
            .with_counted_population("other", Vec::new().into(), Bitvector32Term::Constant(1))
            .open_population_body("other".into(), Vec::new().into())
            .unwrap();
        let after = proposed_fold(&before, &selected);
        let error = CheckedResourceRewrite::check(
            &function,
            &before,
            &ProofFacts::default(),
            &selected,
            &after,
            &ProofFacts::default(),
            &CheckedCallEvents::default(),
        )
        .err()
        .expect("first allocation cannot capture an open population body");
        assert!(error.contains("close the open population body"), "{error}");

        let (_, before, selected, after) = fixture();
        let definition = CCompositeResourceDefinition::counted_population(
            "remaining",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![],
            vec![],
        );
        let function = c_function(
            CType::Void,
            "bodyless",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let error = CheckedResourceRewrite::check(
            &function,
            &before,
            &ProofFacts::default(),
            &selected,
            &after,
            &ProofFacts::default(),
            &CheckedCallEvents::default(),
        )
        .err()
        .expect("this allocation rule does not mint bodyless credits");
        assert!(error.contains("unconditional memory body"), "{error}");
    }

    #[test]
    fn local_population_initialization_ignores_unrelated_populations() {
        let mut samples = Vec::new();
        for size in [0, 32, 512] {
            let (function, mut before, selected, _) = fixture();
            for index in 0..size {
                let pointer = Pointer {
                    block: format!("other-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                before = before.with_counted_population(
                    "remaining",
                    vec![CValue::pointer(pointer.clone()).into()].into(),
                    Bitvector32Term::Constant(3),
                );
                let resources = before
                    .resources()
                    .clone()
                    .unchecked_with_fact(CResourceFact::own(CResource::Composite {
                        name: "remaining".into(),
                        arguments: vec![CValue::pointer(pointer).into()].into(),
                    }));
                before = before.with_resource_context(resources);
            }
            let CResource::Composite { arguments, .. } = selected.resource() else {
                unreachable!()
            };
            let exchanged = before
                .resources()
                .clone()
                .without_exact_representation(&before.resources().facts()[0])
                .unwrap()
                .unchecked_with_fact(selected.clone());
            let after = before
                .clone()
                .with_resource_context(exchanged)
                .with_counted_population(
                    "remaining",
                    arguments.clone(),
                    Bitvector32Term::Constant(3),
                );
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                accepts(&function, &before, &selected, &after)
            });
            assert!(accepted);
            samples.push(work);
        }
        assert!(
            samples[2] <= samples[0] * 2 + 256,
            "initialization must inspect its delta, not the frame: {samples:?}"
        );
    }
}
