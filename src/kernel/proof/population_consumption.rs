//! A contract's single-unit consumption committed before C return.
//!
//! This produces a candidate open state, never an invariant assumption. The
//! caller must check restoration and record the combined close as one event.
use super::*;

pub(super) fn prepare(
    function: &CFunction,
    entry: &CState,
    before: &CState,
    selected: &CResourceFact,
    facts: &ProofFacts,
) -> Result<CState, String> {
    use crate::kernel::{CCountedPopulation, CResourceTerm, CResourceTransferRole};
    let CResource::Composite { name, arguments } = selected.resource() else {
        return Err("consuming close requires a counted resource".into());
    };
    let definition = function
        .composite_resource_definition(name)
        .filter(|definition| definition.is_counted_population())
        .ok_or("consuming close requires a counted resource")?;
    let assumptions = facts.assumptions();
    let (name, arguments, count) = before
        .counted_population_proven_equal(name, arguments, assumptions)
        .ok_or("consuming close requires an active population")?;
    if !before.population_body_is_open(&name, &arguments, assumptions) {
        return Err("consuming close requires an open population body".into());
    }
    if before
        .population_effects
        .committed_consumptions
        .get(&name, &arguments, false)
        .is_some()
    {
        return Err(format!(
            "Requires an unfulfilled `consumes {name}(...)` clause"
        ));
    }
    // The first slice deliberately admits one unconditional, explicit unit
    // effect. Borrow clauses do not grant consumption; a produced replacement
    // or several consumptions need a more general partial-effect rule.
    let same_family = |spec: &&CResourceSpec| {
        matches!(spec.term(),
        CResourceTerm::Composite { name: candidate, .. } if candidate == &name)
    };
    if function
        .resource_ensures()
        .iter()
        .filter(same_family)
        .any(|spec| spec.role() == CResourceTransferRole::Produce)
    {
        return Err(
            "consuming close does not yet support producing the same resource family".into(),
        );
    }
    let mut effects = function
        .resource_requires()
        .iter()
        .filter(same_family)
        .filter(|spec| spec.role() == CResourceTransferRole::Consume);
    let effect = effects
        .next()
        .filter(|spec| spec.guard().is_none())
        .ok_or_else(|| format!("Requires `consumes {name}(...)`"))?;
    if effects.next().is_some() {
        return Err("consuming close requires one unambiguous single-unit consumption".into());
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let declared = crate::kernel::functions::evaluate_function_resource_spec(
        entry,
        effect,
        assumptions,
        &mut budget,
    )
    .map_err(|_| "cannot evaluate the entry consumption")?
    .map_err(|_| "cannot evaluate the entry consumption")?;
    let CResource::Composite {
        name: declared_name,
        arguments: declared_arguments,
    } = declared.resource()
    else {
        return Err("consuming close requires a direct population consumption".into());
    };
    let declared_key = before
        .counted_population_proven_equal(declared_name, declared_arguments, assumptions)
        .map(|(name, arguments, _)| (name, arguments));
    if declared_key != Some((name.clone(), arguments.clone()))
        || declared.owned_quantity_term() != Some(&Bitvector32Term::Constant(1))
    {
        return Err(format!(
            "Requires a single-unit `consumes {name}(...)` for this population"
        ));
    }
    let unit = CResourceFact::own(CResource::Composite {
        name: name.clone(),
        arguments: arguments.clone(),
    });
    let resources = before
        .resources()
        .clone()
        .without_fact_incrementally(&unit, assumptions)
        .ok_or_else(|| format!("Requires {name}(...)"))?;
    let next_count = Bitvector32Term::subtract(count, Bitvector32Term::Constant(1));
    let positive = CResourceFact::own_quantity(unit.resource().clone(), next_count.clone());
    if !positive.has_proven_positive_quantity(assumptions) {
        return Err(format!("Requires count({name}(...)) - 1 > 0"));
    }
    let mut candidate = before
        .clone()
        .with_resource_context(resources)
        .with_counted_population(name.clone(), arguments.clone(), next_count);
    Arc::make_mut(&mut candidate.population_effects)
        .committed_consumptions
        .insert(CCountedPopulation {
            name,
            arguments,
            count: Bitvector32Term::Constant(1),
            family_observation_marker: false,
        });
    // Prove every invariant from the input facts at the decreased count, before
    // ordinary folding can expose any declaration facts. This also checks the
    // shared body's live ownership/loan requirements on the unchanged memory.
    let singleton = ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(unit);
    if let Some(ledger) = before.loan_ledger() {
        let body = crate::kernel::functions::expand_composite_resource_fact(
            &singleton,
            &singleton.facts()[0],
            std::slice::from_ref(definition),
            before.memory(),
            assumptions,
        )
        .ok_or("consuming close requires its owned body")?;
        for child in body.facts() {
            if let Some(range) = child.memory_own_range() {
                ledger
                    .permits_memory_access_with_assumptions(range, assumptions)
                    .map_err(|_| "consuming close requires its body free of active borrows")?;
            }
        }
    }
    let obligations = crate::kernel::functions::evaluate_resource_population_fact_propositions(
        &singleton,
        std::slice::from_ref(definition),
        &candidate,
        assumptions,
        true,
    )
    .ok_or("cannot evaluate the population invariant after consumption")?;
    for obligation in obligations {
        if obligation.is_body_fact
            && !crate::kernel::PureFactContext::settles_exactly(
                assumptions,
                &obligation.proposition,
            )
        {
            return Err(format!(
                "Requires {} after consumption",
                obligation
                    .source_fact
                    .as_deref()
                    .map(|source| {
                        source
                            .split_once(": fact ")
                            .map_or(source, |(_, fact)| fact.trim_end_matches(';'))
                    })
                    .unwrap_or("the population invariant")
            ));
        }
    }
    Ok(candidate)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::*;

    fn fixture(exact_three: bool) -> (CFunction, CState, CState, CResourceFact) {
        let pointer = Pointer {
            block: "cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let arguments: ResourceArguments = vec![CValue::pointer(pointer.clone()).into()].into();
        let unit = CResourceFact::own(CResource::Composite {
            name: "remaining".into(),
            arguments: arguments.clone(),
        });
        let memory = CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
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
                operator: if exact_three {
                    CComparisonOperator::Equal
                } else {
                    CComparisonOperator::GreaterThan
                },
                right: SpecExpression::Value(int32(if exact_three { 3 } else { 0 })),
            }],
        );
        let effect = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::Own,
            "remaining".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Consume,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        let function = c_function(
            CType::Void,
            "test",
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition])
        .with_resource_summary(vec![effect], vec![]);
        let entry = CState::new()
            .with_local("p", CValue::pointer(pointer))
            .with_memory(CMemory::new().with_block("cell", 4))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_quantity(unit.resource().clone(), Bitvector32Term::Constant(2)),
            ))
            .with_counted_population("remaining", arguments.clone(), Bitvector32Term::Constant(3));
        let before = entry
            .clone()
            .with_resource_context(entry.resources().clone().unchecked_with_fact(memory))
            .open_population_body("remaining".into(), arguments)
            .unwrap();
        (function, entry, before, unit)
    }

    #[test]
    fn consuming_close_requires_ownership_contract_invariant_and_a_live_body() {
        let (function, entry, before, unit) = fixture(false);
        let missing_effect = function.clone().with_resource_summary(vec![], vec![]);
        assert!(
            prepare(
                &missing_effect,
                &entry,
                &before,
                &unit,
                &ProofFacts::default()
            )
            .is_err()
        );
        let only_view = before.clone().with_resource_context(
            ResourceContext::new().unchecked_with_fact(unit.core().unwrap()),
        );
        assert!(prepare(&function, &entry, &only_view, &unit, &ProofFacts::default()).is_err());
        let CResource::Composite { name, arguments } = unit.resource() else {
            unreachable!()
        };
        let last = before.clone().with_counted_population(
            name.clone(),
            arguments.clone(),
            Bitvector32Term::Constant(1),
        );
        assert!(prepare(&function, &entry, &last, &unit, &ProofFacts::default()).is_err());
        assert!(prepare(&function, &entry, &entry, &unit, &ProofFacts::default()).is_err());
        let (false_invariant, entry, before, unit) = fixture(true);
        assert!(
            prepare(
                &false_invariant,
                &entry,
                &before,
                &unit,
                &ProofFacts::default()
            )
            .is_err()
        );
    }

    #[test]
    fn consuming_close_preserves_active_memory_borrows() {
        let (function, entry, before, unit) = fixture(false);
        let memory = before
            .resources()
            .facts()
            .iter()
            .find(|fact| fact.memory_own_range().is_some())
            .unwrap()
            .clone();
        let backing = before
            .resources()
            .unique_owned_occurrence_for_fact(&memory)
            .unwrap()
            .0;
        let ledger = crate::kernel::loans::LoanLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(lender, reader, backing, memory).unwrap();
        let before = before.with_loan_ledger(Some(ledger.apply(&opening.transition).unwrap()));
        let error = prepare(&function, &entry, &before, &unit, &ProofFacts::default()).unwrap_err();
        assert!(error.contains("free of active borrows"), "{error}");
    }
    #[test]
    fn consumption_evidence_is_bound_to_its_contract_and_shares_entry_storage() {
        let (function, entry, before, _) = fixture(false);
        let authority = Arc::new(CheckedFunctionEntry {
            caller_state: entry.clone(),
            function: Arc::new(function.clone()),
            arguments: vec![],
            entry_state: entry,
            boundary_transfer: None,
            assumptions: PureFactContext::new(),
            relation_facts: None,
        });
        // Isolate the contract-identity gate; state exchange is covered by the
        // preparation tests and the positive/negative proof fixtures.
        let rewrite = CheckedResourceRewrite {
            before_state: before.clone(),
            after_state: before,
            before_facts: ProofFacts::default(),
            after_facts: ProofFacts::default(),
            definition: function
                .composite_resource_definition("remaining")
                .unwrap()
                .clone(),
            consumption_contract: Some(authority.clone()),
            instance: None,
            selected_children: None,
            load_equalities: vec![],
            delta_proofs: Arc::new(vec![]),
        };
        let wrong_contract = function.clone().with_resource_summary(vec![], vec![]);
        for size in [1, 8, 64] {
            let events = vec![CheckedExecutionEvent::ResourceRewrite(rewrite.clone()); size];
            assert!(events_use_the_function_definitions(&function, &events));
            assert!(!events_use_the_function_definitions(
                &wrong_contract,
                &events
            ));
            for event in events {
                let CheckedExecutionEvent::ResourceRewrite(event) = event else {
                    unreachable!()
                };
                assert!(Arc::ptr_eq(
                    event.consumption_contract.as_ref().unwrap(),
                    &authority
                ));
            }
        }
    }
}
