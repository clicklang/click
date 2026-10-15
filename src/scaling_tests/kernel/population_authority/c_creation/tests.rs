// Scaling tests of `src/kernel/population_authority/c_creation/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn creation_lookup_and_call_transport_ignore_unrelated_events() {
    let sizes = [64_u64, 256, 1024];
    let mut work = Vec::new();
    for size in sizes {
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events.created(PointerBlock::Heap(id));
            events = events.member_created(&PointerBlock::Heap(id), "reference");
            events = events.pending_creation(PointerBlock::Symbolic(Variable(id)));
        }
        let selected = PointerBlock::Heap(size / 2);
        let pending_block = PointerBlock::Symbolic(Variable(10_000 + size));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.created_here(&selected));
            assert_eq!(
                events.establish(&selected, "reference"),
                Err(CreationRefusal::MembersAlreadyExisted)
            );
            assert!(events.establish(&selected, "other").is_ok());
            let callee = events.enter_call();
            assert!(!callee.created_here(&selected));
            assert!(callee.return_to(&events).created_here(&selected));
            let started = events.pending_creation(pending_block.clone());
            let resolved = started
                .enter_call()
                .resolve_pending(&pending_block, Some(PointerBlock::Heap(size)));
            assert!(!resolved.created_here(&PointerBlock::Heap(size)));
            assert!(
                resolved
                    .return_to(&events)
                    .created_here(&PointerBlock::Heap(size))
            );
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn opaque_numeric_batch_work_does_not_grow_with_quantity() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_observable_contract_population(&description, 0)
        .unwrap();
    let facts = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::equal(
            entry.observe_symbolic(&description).unwrap().entry_count,
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let measurements = [2, 64, 1024, 65536].map(|amount| {
        let (after, work) = crate::persistent::measure_persistent_work(|| {
            entry
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    true,
                    &Bitvector32Term::Constant(amount),
                    &facts,
                )
                .unwrap()
                .0
        });
        assert_eq!(
            after.observe_symbolic(&description).unwrap().delta,
            amount as i32
        );
        work
    });
    assert!(measurements[0] > 0, "{measurements:?}");
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}

#[test]
fn opaque_symbolic_birth_composes_numeric_custody_and_scales() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let quantity = Bitvector32Term::Variable(Variable(940_150));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_add_overflows(quantity.clone(), Bitvector32Term::Constant(3)),
            false,
        );
    let work = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        let symbolic = entry
            .checked_member_exchange_quantity(&block, &description, true, &quantity, &assumptions)
            .unwrap()
            .0;
        assert!(matches!(
            symbolic.checked_member_exchange_quantity(
                &block,
                &description,
                true,
                &Bitvector32Term::Constant(3),
                &PureFactContext::new()
            ),
            Err(CreationRefusal::InvalidQuantity)
        ));
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            let born = symbolic
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &Bitvector32Term::Constant(3),
                    &assumptions,
                )
                .unwrap()
                .0;
            let observed = born.observe_symbolic(&description).unwrap();
            assert_eq!(observed.delta, 3);
            assert_eq!(
                observed.combined_delta(),
                Some((
                    true,
                    Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(3))
                ))
            );
            assert_eq!(
                born.imported_member_delta_since_entry(&description),
                observed.combined_delta()
            );
            let retired = born
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &quantity,
                    &assumptions,
                )
                .unwrap()
                .0;
            let remaining = retired.observe_symbolic(&description).unwrap();
            assert_eq!(remaining.delta, 3, "numerical custody survives retirement");
            assert_eq!(remaining.symbolic_delta, None);
            assert!(retired.owns_population_member(&description));
            assert_eq!(
                retired.0.opaque_holders.get(&retired.0.opaque_actor),
                born.0
                    .opaque_holders
                    .get(&born.0.opaque_actor)
                    .map(|rights| rights - 1)
                    .as_ref()
            );
            let child = born.enter_call();
            let sent = child
                .transfer_call_fact(&born, &child, &description, true)
                .unwrap()
                .transfer_call_fact(&born, &child, &description, false)
                .unwrap();
            // A numerical fragment can be passed and spent independently of the
            // caller's framed symbolic batch and two other numerical members.
            let spent = sent
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(1),
                    &assumptions,
                )
                .unwrap()
                .0;
            assert_eq!(spent.observe_symbolic(&description).unwrap().delta, 2);
            let returned = spent
                .transfer_call_fact(&child, &born, &description, true)
                .unwrap()
                .finish_call(&born)
                .unwrap();
            let restored = returned
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(2),
                    &assumptions,
                )
                .unwrap()
                .0;
            assert_eq!(
                restored
                    .observe_symbolic(&description)
                    .unwrap()
                    .combined_delta(),
                Some((true, quantity.clone()))
            );
            assert!(restored.owns_population_member(&description));
            assert!(matches!(
                restored.checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(1),
                    &assumptions
                ),
                Err(CreationRefusal::MissingMembers)
            ));
            let wrong = Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(1));
            assert!(
                restored
                    .transfer_call_fact_quantity(
                        &born,
                        &child,
                        &description,
                        false,
                        &wrong,
                        &assumptions
                    )
                    .is_err()
            );
            let lent = restored
                .transfer_call_fact(&born, &child, &description, true)
                .unwrap();
            assert!(matches!(
                lent.checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &Bitvector32Term::Constant(1),
                    &assumptions
                ),
                Err(CreationRefusal::MissingAuthority)
            ));
        });
        work
    });
    assert!(work[0] > 0);
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 256),
        "mixed batch work scanned unrelated populations: {work:?}"
    );
}

#[test]
fn opaque_symbolic_batch_transfer_work_ignores_unrelated_populations() {
    let quantity = Bitvector32Term::Variable(Variable(940_131));
    let description = member_description(PointerBlock::ExternalArgument);
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    for born_batch in [false, true] {
        let mut work = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut entry = CreationEvents::new();
            for index in 0..size {
                let unrelated = ResourceDescription::new(
                    format!("unrelated-{index}"),
                    description.arguments().to_vec().into(),
                    description.schema().clone(),
                );
                entry = entry
                    .import_opaque_contract_population_inner(
                        &unrelated,
                        0,
                        Some(Bitvector32Term::Constant(0)),
                        None,
                        None,
                    )
                    .unwrap();
            }
            entry = entry
                .import_opaque_contract_population_inner(
                    &description,
                    0,
                    Some(if born_batch {
                        Bitvector32Term::Constant(0)
                    } else {
                        quantity.clone()
                    }),
                    (!born_batch).then(|| quantity.clone()),
                    None,
                )
                .unwrap();
            let (returned, measured) = crate::instrumentation::measure_deterministic_work(|| {
                let child = entry.enter_call();
                let authority = child
                    .transfer_call_fact(&entry, &child, &description, true)
                    .unwrap();
                let held = if born_batch {
                    authority
                        .checked_member_exchange_quantity(
                            &PointerBlock::ExternalArgument,
                            &description,
                            true,
                            &quantity,
                            &assumptions,
                        )
                        .unwrap()
                        .0
                } else {
                    authority
                        .transfer_call_fact_quantity(
                            &entry,
                            &child,
                            &description,
                            false,
                            &quantity,
                            &assumptions,
                        )
                        .unwrap()
                };
                held.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &quantity,
                    &assumptions,
                )
                .unwrap()
                .transfer_call_fact(&child, &entry, &description, true)
                .unwrap()
                .finish_call(&entry)
                .unwrap()
            });
            assert!(returned.owns_population_member(&description));
            work.push(measured);
        }
        assert!(work[3] <= work[0] * 2 + 32, "born={born_batch}: {work:?}");
    }
}

#[test]
fn opaque_population_lookup_and_exchange_ignore_unrelated_imports() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(950_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events
                .import_opaque_contract_population_inner(
                    &description_at(id),
                    1,
                    Some(Bitvector32Term::Constant(3)),
                    None,
                    None,
                )
                .unwrap();
        }
        let selected = description_at(size / 2);
        let neighbor = description_at(size / 2 + 1);
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.owns_population_authority(&selected));
            assert_eq!(events.observe_symbolic(&selected).unwrap().delta, 0);
            let (spent, _) = events
                .checked_member_exchange(&PointerBlock::ExternalArgument, &selected, false)
                .unwrap();
            assert_eq!(spent.observe_symbolic(&selected).unwrap().delta, -1);
            assert_eq!(spent.observe_symbolic(&neighbor).unwrap().delta, 0);
            assert!(spent.spent_imported_member_since(&events, &selected));
            assert!(!spent.spent_imported_member_since(&events, &neighbor));
            assert!(
                spent
                    .enter_proof_entry()
                    .owns_population_authority(&selected)
            );
            assert!(!spent.enter_call().owns_population_authority(&selected));
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn opaque_transfer_and_finish_index_scale_with_selected_population() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(970_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut entry = CreationEvents::new();
        for id in 0..size {
            entry = entry
                .import_opaque_contract_population(&description_at(id), 1)
                .unwrap();
        }
        let selected = description_at(size / 2);
        let child = entry.enter_call();
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            let sent = child
                .transfer_call_fact(&entry, &child, &selected, true)
                .unwrap()
                .transfer_call_fact(&entry, &child, &selected, false)
                .unwrap();
            assert_eq!(
                sent.finish_call(&entry),
                Err(CreationRefusal::OutstandingOwnership)
            );
            let returned = sent
                .transfer_call_fact(&child, &entry, &selected, true)
                .unwrap()
                .transfer_call_fact(&child, &entry, &selected, false)
                .unwrap()
                .finish_call(&entry)
                .unwrap();
            assert!(returned.owns_population_authority(&selected));
            assert!(returned.owns_population_member(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 40, "{work:?}");
}

#[test]
fn checked_empty_lookup_scales_over_unrelated_retired_populations() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let mut events = CreationEvents::new();
        for id in 0..size {
            let block = PointerBlock::Heap(990_000 + id);
            let description = member_description(block.clone());
            events = events.created(block.clone());
            events = events.checked_establish(&block, &description).unwrap().0;
            events = events.checked_retire(&block, &description).unwrap().0;
            events = events.retired(&block).unwrap();
        }
        let selected = member_description(PointerBlock::Heap(990_000 + size / 2));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.checked_empty_population(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 10, "{work:?}");
}

#[test]
fn count_alias_lookup_does_not_scan_unrelated_authority_heads() {
    let description = member_description(PointerBlock::ExternalArgument);
    let [AlgebraicValue::C(CValue::Pointer(anchor))] = description.arguments() else {
        panic!("pointer anchor")
    };
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(9_850_101))),
            byte_width: 4,
        },
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(CValue::pointer(alias.clone())))],
    };
    let equal = PureFactContext::new()
        .assume_proposition(crate::kernel::pointer_origin_fact(
            CValue::pointer(alias.clone()),
            CValue::Pointer(anchor.clone()),
        ))
        .assume_condition(
            ConditionTerm::pointer_equal(alias, anchor.pointer().clone()),
            true,
        );
    let samples = [64usize, 256, 1024].map(|size| {
        let events = CreationEvents::new()
            .import_opaque_contract_population_inner(
                &description,
                2,
                Some(Bitvector32Term::Constant(7)),
                None,
                None,
            )
            .unwrap();
        let mut resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
            CResource::PopulationAuthority(description.clone()),
        ));
        for index in 0..size {
            let other =
                member_description(PointerBlock::Symbolic(Variable(9_860_000 + index as u64)));
            resources = resources
                .unchecked_with_fact(CResourceFact::own(CResource::PopulationAuthority(other)));
        }
        let mut state = CState::new()
            .with_population_creation_tracking()
            .with_resource_context(resources);
        Arc::make_mut(&mut state.population_effects).creation = Some(events);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &state,
                &count,
                &equal,
                &BTreeMap::new(),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        });
        assert_eq!(paths[0].value, CValue::Int32(Bitvector32Term::Constant(7)));
        work
    });
    assert!(samples[0] > 0, "lookup must charge its work: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 128),
        "authority alias lookup must grow at most logarithmically: {samples:?}"
    );
}

#[test]
fn exact_symbolic_births_use_numeric_custody_and_scale() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let quantity = Bitvector32Term::Variable(Variable(990_001));
    let samples = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("exact-unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(991_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        facts = facts.assume_condition(
            ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(1_000_000_000)),
            true,
        );
        PureFactContext::reset_exact_constant_fact_visits();
        let (born, work) = crate::instrumentation::measure_deterministic_work(|| {
            let first = entry
                .checked_member_exchange_quantity(&block, &description, true, &quantity, &facts)
                .unwrap()
                .0;
            first
                .checked_member_exchange_quantity(&block, &description, true, &quantity, &facts)
                .unwrap()
                .0
        });
        assert_eq!(PureFactContext::exact_constant_fact_visits(), 2);
        assert_eq!(
            born.observe_symbolic(&description).unwrap().delta,
            2_000_000_000
        );
        assert!(
            born.0
                .opaque_imports
                .get(&description)
                .unwrap()
                .symbolic_delta
                .is_none()
        );
        assert!(
            born.checked_member_exchange_quantity(&block, &description, true, &quantity, &facts,)
                .is_err(),
            "a third billion must not wrap the population"
        );
        let child = born.enter_call();
        let sent = child
            .transfer_call_fact(&born, &child, &description, true)
            .unwrap()
            .transfer_call_fact_quantity(&born, &child, &description, false, &quantity, &facts)
            .unwrap();
        let spent = sent
            .checked_member_exchange_quantity(&block, &description, false, &quantity, &facts)
            .unwrap()
            .0;
        let returned = spent
            .transfer_call_fact(&child, &born, &description, true)
            .unwrap()
            .finish_call(&born)
            .unwrap();
        assert_eq!(
            returned.observe_symbolic(&description).unwrap().delta,
            1_000_000_000
        );
        assert!(returned.owns_population_member(&description));
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn opaque_repeated_symbolic_births_compose_and_return_without_scanning_unrelated_state() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let first_quantity = Bitvector32Term::Variable(Variable(992_001));
    let second_quantity = Bitvector32Term::Variable(Variable(992_002));
    let total = Bitvector32Term::add(first_quantity.clone(), second_quantity.clone());
    let samples = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("repeated-symbolic-unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(993_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        for quantity in [&first_quantity, &second_quantity] {
            facts = facts.assume_condition(
                ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
                true,
            );
        }
        let child = entry.enter_call();
        let authorized = child
            .transfer_call_fact(&entry, &child, &description, true)
            .unwrap();
        let first = authorized
            .checked_member_exchange_quantity(&block, &description, true, &first_quantity, &facts)
            .unwrap()
            .0;
        assert_eq!(
            first
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .unwrap_err(),
            CreationRefusal::InvalidQuantity,
            "nonnegative quantities alone do not establish a non-wrapping total"
        );
        let current = Bitvector32Term::add(Bitvector32Term::Constant(0), first_quantity.clone());
        facts = facts.assume_condition(
            ConditionTerm::signed_add_overflows(current, second_quantity.clone()),
            false,
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let born = first
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .unwrap()
                .0;
            assert_eq!(
                born.observe_symbolic(&description).unwrap().symbolic_delta,
                Some((true, total.clone()))
            );
            assert_eq!(
                born.0.opaque_holders.get(&child.0.opaque_actor),
                Some(&2),
                "the coalesced batch is one right beside the authority"
            );
            assert_eq!(
                born.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &first_quantity,
                    &facts,
                )
                .unwrap_err(),
                CreationRefusal::InvalidQuantity,
                "a coalesced batch cannot silently split"
            );
            let sent = born
                .transfer_call_fact_quantity(&child, &entry, &description, false, &total, &facts)
                .unwrap();
            assert!(
                sent.checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .is_err(),
                "authority alone cannot extend another actor's batch"
            );
            assert_eq!(
                sent.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &total,
                    &facts,
                )
                .unwrap_err(),
                CreationRefusal::MissingMembers
            );
            let returned = sent
                .transfer_call_fact(&child, &entry, &description, true)
                .unwrap()
                .finish_call(&entry)
                .unwrap();
            assert!(returned.owns_population_authority(&description));
            assert!(returned.owns_population_member(&description));
            assert_eq!(
                returned
                    .observe_symbolic(&description)
                    .unwrap()
                    .symbolic_delta,
                Some((true, total.clone()))
            );
            facts = facts.assume_condition(
                ConditionTerm::signed_greater_equal(total.clone(), Bitvector32Term::Constant(0)),
                true,
            );
            assert!(
                returned
                    .checked_member_exchange_quantity(
                        &block,
                        &description,
                        false,
                        &first_quantity,
                        &facts,
                    )
                    .is_err(),
                "a whole batch cannot be partially retired"
            );
            let consumer = returned.enter_call();
            assert!(
                consumer
                    .checked_member_exchange_quantity(&block, &description, false, &total, &facts,)
                    .is_err(),
                "consumption requires transferred authority"
            );
            let authorized = consumer
                .transfer_call_fact(&returned, &consumer, &description, true)
                .unwrap()
                .transfer_call_fact_quantity(
                    &returned,
                    &consumer,
                    &description,
                    false,
                    &total,
                    &facts,
                )
                .unwrap();
            let spent = authorized
                .checked_member_exchange_quantity(&block, &description, false, &total, &facts)
                .unwrap()
                .0;
            assert_eq!(
                spent.observe_symbolic(&description).unwrap().symbolic_delta,
                None
            );
            assert_eq!(
                spent.0.opaque_holders.get(&consumer.0.opaque_actor),
                Some(&1)
            );
            assert!(
                spent
                    .checked_member_exchange_quantity(&block, &description, false, &total, &facts,)
                    .is_err(),
                "retirement cannot be repeated"
            );
            let finished = spent
                .transfer_call_fact(&consumer, &returned, &description, true)
                .unwrap()
                .finish_call(&returned)
                .unwrap();
            assert!(finished.owns_population_authority(&description));
            assert!(!finished.owns_population_member(&description));
        });
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn imported_named_consumption_counts_identities_and_ignores_unrelated_state() {
    let anchor = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let description = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    );
    let member = |identity| {
        ResourceInstance::new(
            Variable(identity),
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap()
    };
    let left = member(996_001);
    let right = member(996_002);
    let work = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("unrelated-named-{index}"),
                description.arguments().to_vec().into(),
                schema.clone(),
            );
            entry = entry.import_observable_named_authority(&unrelated).unwrap();
        }
        let entry = entry
            .import_observable_named_authority(&description)
            .unwrap();
        let count = entry.observe_symbolic(&description).unwrap().entry_count;
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            assert!(
                entry
                    .enter_call()
                    .checked_imported_instance_consumption(&left)
                    .is_err(),
                "an actor without authority cannot record a death"
            );
            let one = entry.checked_imported_instance_consumption(&left).unwrap();
            assert_eq!(
                one,
                entry.checked_imported_instance_consumption(&left).unwrap(),
                "rechecking one checked rewrite has a stable successor identity"
            );
            assert_eq!(
                one.observe_symbolic(&description).unwrap().symbolic_delta,
                Some((false, Bitvector32Term::Constant(1)))
            );
            assert_eq!(
                one.checked_imported_instance_consumption(&left)
                    .unwrap_err(),
                CreationRefusal::MissingMembers
            );
            let two = one.checked_imported_instance_consumption(&right).unwrap();
            let observed = two.observe_symbolic(&description).unwrap();
            assert_eq!(observed.entry_count, count);
            assert_eq!(observed.entry_owned_members, 2);
            assert_eq!(
                two.0
                    .opaque_imports
                    .get(&description)
                    .unwrap()
                    .owned_members,
                0,
                "a numeric lower bound does not grant member custody"
            );
            assert_eq!(
                observed.symbolic_delta,
                Some((false, Bitvector32Term::Constant(2)))
            );
            assert!(
                !two.owns_population_member(&description),
                "named deaths grant no anonymous custody"
            );
            assert_eq!(
                entry.0.opaque_holders.get(&entry.0.opaque_actor),
                two.0.opaque_holders.get(&two.0.opaque_actor)
            );
        });
        work
    });
    assert!(work[0] > 0);
    for (index, sample) in work.iter().enumerate() {
        assert!(*sample <= work[0] + 96 * index, "{work:?}");
    }
}

#[test]
fn imported_named_lifecycle_keeps_entry_bounds_and_scales_with_unrelated_imports() {
    for wildcard in [false, true] {
        let anchor = CValue::pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        });
        let schema =
            ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let mut scope = ResourceDescription::new(
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
        );
        if wildcard {
            scope = scope.with_population_arity(2).unwrap();
        }
        let member = |identity, tag| {
            let mut arguments = vec![anchor.clone().into()];
            if wildcard {
                arguments.push(int32(tag).into());
            }
            ResourceInstance::new(
                Variable(identity),
                "ticket".into(),
                arguments.into(),
                schema.clone(),
                vec![int32(7).into()].into(),
            )
            .unwrap()
        };
        let born = member(997_001, 7);
        let first = member(997_002, 7);
        let second = member(997_003, 7);
        let exact = ResourceDescription::from_instance(&first);
        let work = [16, 64, 256].map(|size| {
            let mut entry = CreationEvents::new();
            for index in 0..size {
                let unrelated = ResourceDescription::new(
                    format!("other-{index}"),
                    scope.arguments().to_vec().into(),
                    schema.clone(),
                );
                entry = entry.import_observable_named_authority(&unrelated).unwrap();
            }
            let entry = entry.import_observable_named_authority(&scope).unwrap();
            let count = entry.observe_symbolic(&scope).unwrap().entry_count;
            let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(count.clone(), Bitvector32Term::Constant(1)),
                false,
            ));
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                assert!(
                    entry
                        .checked_imported_instance_exchange(&born, true, &PureFactContext::new())
                        .is_err()
                );
                assert!(
                    entry
                        .enter_call()
                        .checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                let one = entry
                    .checked_imported_instance_exchange(&born, true, &assumptions)
                    .unwrap();
                assert_eq!(
                    one,
                    entry
                        .checked_imported_instance_exchange(&born, true, &assumptions)
                        .unwrap()
                );
                assert!(
                    one.checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                assert!(!one.owns_population_member(&scope));
                let zero = one.checked_imported_instance_consumption(&born).unwrap();
                assert_eq!(
                    zero.observe_symbolic(&scope).unwrap().combined_delta(),
                    None
                );
                assert_eq!(
                    zero.observe_symbolic(&scope).unwrap().entry_owned_members,
                    0,
                    "a born occurrence is not an entry occurrence"
                );
                assert!(zero.checked_imported_instance_consumption(&born).is_err());
                assert!(
                    zero.checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                let spent = zero
                    .checked_imported_instance_consumption(&first)
                    .unwrap()
                    .checked_imported_instance_consumption(&second)
                    .unwrap();
                let observed = spent.observe_symbolic(&scope).unwrap();
                assert_eq!(observed.entry_count, count);
                assert_eq!(observed.entry_owned_members, 2);
                assert_eq!(
                    observed.combined_delta(),
                    Some((false, Bitvector32Term::Constant(2)))
                );
                if wildcard {
                    let exact_count = spent
                        .observe_exact_member(&exact, &PureFactContext::new())
                        .unwrap();
                    assert_eq!(exact_count.delta, -2);
                    assert_eq!(exact_count.entry_owned_members, 2);
                    assert_eq!(
                        spent
                            .observe_exact_member(
                                &ResourceDescription::from_instance(&member(997_004, 8)),
                                &PureFactContext::new()
                            )
                            .unwrap()
                            .delta,
                        0
                    );
                }
                assert_eq!(
                    entry.0.opaque_holders.get(&entry.0.opaque_actor),
                    spent.0.opaque_holders.get(&spent.0.opaque_actor)
                );
            });
            work
        });
        assert!(work[0] > 0);
        for (index, sample) in work.iter().enumerate() {
            assert!(*sample <= work[0] + 160 * index, "{work:?}");
        }
    }
}

#[test]
fn imported_named_death_receipts_are_indexed_beside_growing_related_members() {
    let anchor = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let description = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    );
    let member = |identity| {
        ResourceInstance::new(
            Variable(identity),
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap()
    };
    let work = [16, 64, 256].map(|size| {
        let mut state = CreationEvents::new()
            .import_observable_named_authority(&description)
            .unwrap();
        for index in 0..size {
            state = state
                .checked_imported_instance_consumption(&member(999_001 + index))
                .unwrap();
        }
        let (next, work) = crate::persistent::measure_persistent_work(|| {
            state
                .checked_imported_instance_consumption(&member(999_999))
                .unwrap()
        });
        assert_eq!(
            next.observe_symbolic(&description)
                .unwrap()
                .entry_owned_members,
            size as u32 + 1
        );
        assert!(
            next.consumed_imported_instance(&description, Variable(999_001))
                .is_some()
        );
        work
    });
    assert!(work[0] > 0);
    for (index, sample) in work.iter().enumerate() {
        assert!(*sample <= work[0] + 64 * index, "{work:?}");
    }
}
