use super::*;

#[test]
fn quantity_exchange_net_certification_scales_beside_unrelated_populations() {
    let samples = [(2, 16), (64, 64), (65536, 256)].map(|(amount, unrelated)| {
        let pointer = CValue::typed_pointer(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::Int32Pointer,
        );
        let description = ResourceDescription::new(
            "member".into(),
            vec![pointer.clone().into()].into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        );
        let authority = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
        let resource = CResource::Composite {
            name: "member".into(),
            arguments: vec![pointer.clone().into()].into(),
        };
        let member = CResourceFact::own_quantity(resource, Bitvector32Term::Constant(amount));
        let mut entry = CState::new()
            .with_population_creation_tracking()
            .with_local("p", pointer)
            .with_resource_context(
                ResourceContext::new().unchecked_with_facts([authority.clone(), member.clone()]),
            )
            .import_opaque_population_quantity(&authority, &member)
            .unwrap();
        for index in 1..=unrelated {
            let other = ResourceDescription::new(
                "unrelated".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(950_000 + index as u64)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            );
            let authority = CResourceFact::own(CResource::PopulationAuthority(other));
            entry = entry
                .clone()
                .with_resource_context(
                    entry
                        .resources()
                        .clone()
                        .unchecked_with_fact(authority.clone()),
                )
                .import_opaque_population(&authority, 0)
                .unwrap();
        }
        let member_spec = CResourceSpec::composite(
            CResourceAccessMode::Own,
            "member".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
        );
        let authority_spec = CResourceSpec::new(
            CResourceTerm::PopulationAuthority {
                protected: Box::new(CResourceTypeSpec {
                    resource: Box::new(member_spec.clone()),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                population_arity: None,
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        let consumed = CResourceSpec::new(
            member_spec.term().clone(),
            CResourceAccessMode::Own,
            CResourceQuantity::Count(c_int32_literal(amount)),
            CResourceTransferRole::Consume,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        let produced = CResourceSpec::new(
            member_spec.term().clone(),
            CResourceAccessMode::Own,
            CResourceQuantity::Count(c_int32_literal(amount - 1)),
            CResourceTransferRole::Produce,
            CResourceSnapshot::Post,
        )
        .unwrap();
        let function = c_function(
            CType::Void,
            "shrink",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_void_value()),
        )
        .with_resource_summary(
            vec![authority_spec.clone(), consumed],
            vec![authority_spec, produced],
        )
        .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
            "member",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )]);
        assert!(authority_supports_resource_contract(
            function.contract_interface()
        ));
        assert!(!authority_preserves_assumed_resource_contract(
            function.contract_interface()
        ));
        let events = entry.population_effects.creation.as_ref().unwrap();
        let count = events.observe_symbolic(&description).unwrap().entry_count;
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    count.clone(),
                    Bitvector32Term::Constant(amount),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    count,
                    Bitvector32Term::Constant((i32::MAX - 1) as u32),
                ),
                true,
            );
        let (exit, work) = crate::persistent::measure_persistent_work(|| {
            let spent = events
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    false,
                    &Bitvector32Term::Constant(amount),
                    &assumptions,
                )
                .unwrap()
                .0;
            let returned = spent
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    true,
                    &Bitvector32Term::Constant(amount - 1),
                    &assumptions,
                )
                .unwrap()
                .0;
            let mut exit = entry.clone();
            Arc::make_mut(&mut exit.population_effects).creation = Some(returned);
            check_quantity_exchange_at_return(
                &entry,
                &exit,
                function.contract_interface(),
                &assumptions,
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap()
            .unwrap();
            exit
        });
        assert_eq!(
            exit.population_effects
                .creation
                .as_ref()
                .unwrap()
                .observe_symbolic(&description)
                .unwrap()
                .delta,
            -1
        );
        assert!(
            check_quantity_exchange_at_return(
                &entry,
                &entry,
                function.contract_interface(),
                &assumptions,
                &mut ExecutionBudget::beside_live_state()
            )
            .unwrap()
            .is_err(),
            "an unchanged ledger cannot certify the claimed decrement"
        );
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    // Each sample quadruples the indexed population count. Permit bounded
    // tree-path growth while excluding work proportional to either the
    // unrelated population count or the exchanged quantity.
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 96 * index, "{samples:?}");
    }
}

#[test]
fn contained_transfer_frontier_scales_with_selected_depth_and_indexed_definitions() {
    let pointer = Pointer {
        block: "payload".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("payload", 4);
    let assumptions = PureFactContext::new();
    let root = CResourceFact::own_composite("wrapper-0000".into(), vec![CValue::pointer(pointer)]);
    let definition = |name: String, next: Option<String>| {
        CCompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            next.into_iter()
                .map(|next| {
                    CResourceSpec::composite(
                        CResourceAccessMode::Own,
                        next,
                        vec![c_variable("p")],
                        vec![CType::Int32Pointer],
                    )
                })
                .collect(),
            vec![],
        )
    };
    let sample = |depth, unrelated| {
        let mut definitions = (0..depth)
            .map(|index| {
                definition(
                    format!("wrapper-{index:04}"),
                    if index + 1 == depth {
                        None
                    } else {
                        Some(format!("wrapper-{:04}", index + 1))
                    },
                )
            })
            .chain((0..unrelated).map(|index| definition(format!("unrelated-{index:04}"), None)))
            .collect::<Vec<_>>();
        definitions.sort_by(|a, b| a.name().cmp(b.name()));
        let (frontier, work) = crate::instrumentation::measure_deterministic_work(|| {
            population_transfer_frontier(
                std::iter::once(&root),
                &definitions,
                &memory,
                &assumptions,
            )
            .unwrap()
        });
        assert_eq!(frontier.len(), depth);
        work
    };
    let depths = [sample(16, 512), sample(32, 512), sample(64, 512)];
    for pair in depths.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 32,
            "contained transfer rescans ancestors: {depths:?}"
        );
    }
    let frames = [sample(16, 16), sample(16, 64), sample(16, 256)];
    for pair in frames.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 32,
            "contained transfer scans unrelated definitions: {frames:?}"
        );
    }
    let recursive = vec![definition(
        "wrapper-0000".into(),
        Some("wrapper-0000".into()),
    )];
    assert!(
        population_transfer_frontier(std::iter::once(&root), &recursive, &memory, &assumptions)
            .is_err()
    );
}

#[test]
fn boundary_receipt_rejects_other_callers_functions_and_arguments() {
    let caller = CState::new().with_local("kept", int32(7));
    let function = Arc::new(c_function(
        CType::Void,
        "entry_receipt",
        vec![c_parameter("value", CType::Int32)],
        CStatement::Skip,
    ));
    let arguments = vec![CExpression::Value(int32(3))];
    let receipt = capture_checked_boundary_resource_transfer(
        &caller,
        function.clone(),
        &arguments,
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert!(receipt.matches(&caller, &function, &arguments));
    assert_eq!(receipt, receipt.clone());
    let recaptured = capture_checked_boundary_resource_transfer(
        &caller,
        function.clone(),
        &arguments,
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_ne!(receipt, recaptured);
    let other_function = function.as_ref().clone();
    let other_caller = caller.clone().with_local("kept", int32(8));
    let other_arguments = vec![CExpression::Value(int32(4))];
    for (candidate_caller, candidate_function, candidate_arguments) in [
        (&other_caller, function.as_ref(), arguments.as_slice()),
        (&caller, &other_function, arguments.as_slice()),
        (&caller, function.as_ref(), other_arguments.as_slice()),
    ] {
        let result = contract_exit_outcome_with_boundary_transfer(
            candidate_caller,
            candidate_function,
            candidate_arguments,
            CStatementOutcome::Normal(Box::new(caller.clone())),
            Vec::new(),
            &PureFactContext::new(),
            &mut ExecutionBudget::beside_live_state(),
            ResourceTransitionPurpose::FunctionBoundary,
            Some(&receipt),
        )
        .unwrap();
        assert!(
            matches!(result, Err(CRuntimeError::FunctionContract(message))
                if message == "function boundary resource receipt belongs to another entry")
        );
        let deferred = resolve_deferred_contract_exit(
            candidate_caller,
            candidate_function,
            candidate_arguments,
            &CFunctionOutcome::Return {
                value: int32(0),
                state: Box::new(caller.clone()),
            },
            Some(&receipt),
            &PureFactContext::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        assert!(
            matches!(deferred, Err(CRuntimeError::FunctionContract(message))
                if message == "function boundary resource receipt belongs to another entry")
        );
    }
}

#[test]
fn authority_helper_rejects_resource_constructors() {
    let mut interface = CFunctionContractInterface::new(CType::Int32, Vec::new());
    interface.resource_constructors = vec![CResourceSpec::owned_memory(CMemorySegment::new(
        c_int32_literal(0),
        c_int32_literal(0),
        c_int32_literal(1),
    ))];
    assert!(!authority_preserves_resource_contract(&interface));
}
#[test]
fn assumed_authority_contracts_preserve_named_identity_without_lifecycle_rights() {
    assert!(!authority_preserves_assumed_resource_contract(
        &CFunctionContractInterface::new(CType::Void, Vec::new())
    ));
    let mut interface = companion_interface("reference");
    interface
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    interface
        .resource_ensures
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    let identity = Variable::allocate_fresh().unwrap();
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let member = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "ticket".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let named = CResourceSpec::instance(
        identity,
        "member".into(),
        schema.clone(),
        member.clone(),
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Current,
    )
    .unwrap();
    interface.resource_requires.push(named.clone());
    interface.resource_ensures.push(named);
    assert!(authority_preserves_assumed_resource_contract(&interface));
    let mut logical = interface.clone();
    logical
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::Instance);
    logical
        .resource_ensures
        .retain(|spec| spec.family() == ResourceFamily::Instance);
    assert!(
        authority_preserves_assumed_resource_contract(&logical),
        "ordinary named models do not need artificial population authority"
    );
    for role in [
        CResourceTransferRole::Consume,
        CResourceTransferRole::Produce,
    ] {
        let mut changed = interface.clone();
        if role == CResourceTransferRole::Consume {
            let last = changed.resource_requires.last_mut().unwrap();
            *last = last.clone().with_role(role);
            changed.resource_ensures.pop();
        } else {
            changed.resource_requires.pop();
            let last = changed.resource_ensures.last_mut().unwrap();
            *last = last.clone().with_role(role);
        }
        assert!(!authority_preserves_assumed_resource_contract(&changed));
    }
    let mut changed = interface.clone();
    changed.resource_ensures.pop();
    changed.resource_ensures.push(
        CResourceSpec::instance(
            Variable::allocate_fresh().unwrap(),
            "member".into(),
            schema,
            member,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        )
        .unwrap(),
    );
    assert!(!authority_preserves_assumed_resource_contract(&changed));
    interface.resource_ensures.pop();
    assert!(!authority_preserves_assumed_resource_contract(&interface));
}

fn companion_interface(member_family: &str) -> CFunctionContractInterface {
    let member = CResourceSpec::composite(
        CResourceAccessMode::Own,
        member_family.into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(member.clone()),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let memory = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("slot"),
        c_int32_literal(0),
        c_int32_literal(1),
    ));
    let parent = CResourceSpec::instance(
        Variable(991_010),
        "link".into(),
        ResourceFieldSchema::new(vec![("tag".into(), ResourceFieldType::Integer)]).unwrap(),
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            "parent".into(),
            vec![c_variable("slot")],
            vec![CType::Int32Pointer],
        ),
        CResourceTransferRole::Produce,
        CResourceSnapshot::Post,
    )
    .unwrap();
    c_function(
        CType::Void,
        "retain_with_companions",
        vec![],
        CStatement::Skip,
    )
    .with_resource_summary(
        vec![
            memory,
            member.clone().with_role(CResourceTransferRole::Borrow),
            authority.clone(),
        ],
        vec![
            parent,
            member.clone().with_role(CResourceTransferRole::Produce),
            member.with_role(CResourceTransferRole::Borrow),
            authority,
        ],
    )
    .contract_interface()
    .clone()
}

#[test]
fn member_effect_is_independent_of_companion_positions_and_borrowed_survivor() {
    let interface = companion_interface("reference");
    let (produce, selected) = authority_member_effect(&interface).unwrap();
    assert!(produce);
    assert!(
        matches!(selected.term(), CResourceTerm::Composite { name, .. } if name == "reference")
    );
    assert!(authority_supports_resource_contract(&interface));
}

#[test]
fn member_move_admission_requires_two_scoped_authorities_and_one_unchanged_member() {
    let member = |anchor, trailing| {
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            "slot".into(),
            vec![c_variable(anchor), c_variable(trailing)],
            vec![CType::Int32Pointer, CType::Int32Pointer],
        )
    };
    let authority = |anchor| {
        CResourceSpec::new(
            CResourceTerm::PopulationAuthority {
                population_arity: Some(2),
                protected: Box::new(CResourceTypeSpec {
                    resource: Box::new(CResourceSpec::composite(
                        CResourceAccessMode::Own,
                        "slot".into(),
                        vec![c_variable(anchor)],
                        vec![CType::Int32Pointer],
                    )),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap()
    };
    let source = authority("source");
    let destination = authority("destination");
    let interface = c_function(CType::Void, "move", vec![], CStatement::Skip)
        .with_resource_summary(
            vec![
                source.clone(),
                destination.clone(),
                member("source", "p").with_role(CResourceTransferRole::Consume),
            ],
            vec![
                source,
                destination,
                member("destination", "p").with_role(CResourceTransferRole::Produce),
            ],
        )
        .contract_interface()
        .clone();
    assert!(authority_exchanges_member_contract(&interface));
    assert!(authority_supports_resource_contract(&interface));
    assert!(authority_member_effect(&interface).is_none());
    let mut missing = interface.clone();
    missing.resource_requires.remove(1);
    assert!(!authority_supports_resource_contract(&missing));
    let mut changed_member = interface.clone();
    changed_member.resource_ensures[2] =
        member("destination", "q").with_role(CResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&changed_member));
    let mut duplicate = interface.clone();
    duplicate
        .resource_ensures
        .push(duplicate.resource_ensures[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut same_pool = interface.clone();
    same_pool.resource_ensures[2] = member("source", "p").with_role(CResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&same_pool));
    let mut lost_authority = interface;
    lost_authority.resource_ensures.remove(1);
    assert!(!authority_supports_resource_contract(&lost_authority));
}

#[test]
fn family_exchange_admission_requires_both_exact_authorities_and_one_effect_each() {
    let member = |name: &str, arguments: Vec<CExpression>| {
        let types = vec![CType::Int32Pointer; arguments.len()];
        CResourceSpec::composite(CResourceAccessMode::Own, name.into(), arguments, types)
    };
    let authority = |name: &str, arity| {
        CResourceSpec::new(
            CResourceTerm::PopulationAuthority {
                protected: Box::new(CResourceTypeSpec {
                    resource: Box::new(member(name, vec![c_variable("pool")])),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                population_arity: arity,
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap()
    };
    let capacity = authority("capacity", None);
    let item = authority("item", Some(2));
    let interface = c_function(CType::Void, "checkout", vec![], CStatement::Skip)
        .with_resource_summary(
            vec![
                capacity.clone(),
                item.clone(),
                member("capacity", vec![c_variable("pool")])
                    .with_role(CResourceTransferRole::Consume),
            ],
            vec![
                capacity,
                item,
                member("item", vec![c_variable("pool"), c_variable("p")])
                    .with_role(CResourceTransferRole::Produce),
            ],
        )
        .contract_interface()
        .clone();
    assert!(authority_exchanges_member_contract(&interface));
    for index in [0, 1] {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&lost));
    }
    let mut duplicate = interface.clone();
    duplicate
        .resource_requires
        .push(duplicate.resource_requires[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut duplicate = interface.clone();
    duplicate
        .resource_ensures
        .push(duplicate.resource_ensures[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut wrong_anchor = interface;
    wrong_anchor.resource_ensures[2] = member("item", vec![c_variable("other"), c_variable("p")])
        .with_role(CResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&wrong_anchor));
}

#[test]
fn four_effect_exchange_admission_checks_every_scope_quantity_and_exact_identity() {
    let member = |family: &str, anchor: &str, item: bool| {
        let mut arguments = vec![c_variable(anchor)];
        if item {
            arguments.push(c_variable("p"));
        }
        let types = vec![CType::Int32Pointer; arguments.len()];
        CResourceSpec::composite(CResourceAccessMode::Own, family.into(), arguments, types)
    };
    let authority = |family: &str, anchor: &str, item: bool| {
        CResourceSpec::new(
            CResourceTerm::PopulationAuthority {
                population_arity: item.then_some(2),
                protected: Box::new(CResourceTypeSpec {
                    resource: Box::new(member(family, anchor, false)),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap()
    };
    let authorities = vec![
        authority("slot", "source", false),
        authority("slot", "destination", false),
        authority("item", "source", true),
        authority("item", "destination", true),
    ];
    let mut inputs = authorities.clone();
    inputs.extend([
        member("item", "source", true).with_role(CResourceTransferRole::Consume),
        member("slot", "destination", false).with_role(CResourceTransferRole::Consume),
    ]);
    let mut outputs = authorities;
    outputs.extend([
        member("item", "destination", true).with_role(CResourceTransferRole::Produce),
        member("slot", "source", false).with_role(CResourceTransferRole::Produce),
    ]);
    let interface = c_function(CType::Void, "exchange", vec![], CStatement::Skip)
        .with_resource_summary(inputs, outputs)
        .contract_interface()
        .clone();
    assert!(authority_supports_resource_contract(&interface));
    let effects = authority_checked_member_effects(&interface);
    assert_eq!(effects.iter().filter(|(produce, _)| !produce).count(), 2);
    assert_eq!(effects.iter().filter(|(produce, _)| *produce).count(), 2);
    for index in 0..4 {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&lost));
    }
    for index in [4, 5] {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut missing = interface.clone();
        missing.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
    }
    for index in [4, 5] {
        let mut nonunit = interface.clone();
        let original = &nonunit.resource_ensures[index];
        nonunit.resource_ensures[index] = CResourceSpec::new(
            original.term().clone(),
            original.access(),
            CResourceQuantity::Count(c_int32_literal(2)),
            original.role(),
            original.snapshot(),
        )
        .unwrap();
        assert!(!authority_supports_resource_contract(&nonunit));
    }
    let mut changed_item = interface.clone();
    changed_item.resource_ensures[4] = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "item".into(),
        vec![c_variable("destination"), c_variable("q")],
        vec![CType::Int32Pointer; 2],
    )
    .with_role(CResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&changed_item));
    let mut extra = interface.clone();
    extra
        .resource_ensures
        .push(extra.resource_ensures[5].clone());
    assert!(!authority_supports_resource_contract(&extra));
    let mut wrong_anchor = interface;
    wrong_anchor.resource_ensures[5] =
        member("slot", "other", false).with_role(CResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&wrong_anchor));
}

#[test]
fn two_control_births_require_each_scope_return_and_unit_effect() {
    let composite = |name: &str, anchor: &str| {
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            name.into(),
            vec![c_variable(anchor)],
            vec![CType::Int32Pointer],
        )
    };
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(composite("slot", "p")),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let definition = |name: &str| {
        CCompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![authority.clone()],
            vec![],
        )
    };
    let input = |anchor| composite("storage", anchor).with_role(CResourceTransferRole::Consume);
    let output = |anchor| composite("control", anchor).with_role(CResourceTransferRole::Produce);
    let birth = |anchor| composite("slot", anchor).with_role(CResourceTransferRole::Produce);
    let interface = c_function(CType::Void, "pair", vec![], CStatement::Skip)
        .with_resource_summary(
            vec![input("first"), input("second")],
            vec![
                output("first"),
                output("second"),
                birth("first"),
                birth("second"),
            ],
        )
        .with_composite_resource_definitions(vec![definition("storage"), definition("control")])
        .contract_interface()
        .clone();
    assert!(authority_supports_resource_contract(&interface));
    assert_eq!(authority_checked_member_effects(&interface).len(), 2);
    for index in 0..2 {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(authority_two_control_births(&missing).is_none());
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(authority_two_control_births(&lost).is_none());
    }
    for index in 2..4 {
        let mut missing = interface.clone();
        missing.resource_ensures.remove(index);
        assert!(authority_two_control_births(&missing).is_none());
        let mut wrong = interface.clone();
        wrong.resource_ensures[index] = birth("other");
        assert!(authority_two_control_births(&wrong).is_none());
        let mut nonunit = interface.clone();
        let old = &nonunit.resource_ensures[index];
        nonunit.resource_ensures[index] = CResourceSpec::new(
            old.term().clone(),
            old.access(),
            CResourceQuantity::Count(c_int32_literal(2)),
            old.role(),
            old.snapshot(),
        )
        .unwrap();
        assert!(authority_two_control_births(&nonunit).is_none());
    }
    let mut duplicate = interface.clone();
    duplicate.resource_ensures[3] = birth("first");
    assert!(authority_two_control_births(&duplicate).is_none());
    let mut changed_control = interface.clone();
    changed_control.resource_ensures[1] = output("other");
    assert!(authority_two_control_births(&changed_control).is_none());
    let mut extra = interface;
    extra.resource_ensures.push(birth("third"));
    assert!(authority_two_control_births(&extra).is_none());
}

#[test]
fn multiple_member_effects_cannot_pass_as_ordinary_companions() {
    let mut interface = companion_interface("reference");
    let member = interface.resource_ensures[1].clone();
    interface.resource_ensures.push(member);
    assert!(authority_member_effect(&interface).is_none());
    assert!(!authority_supports_resource_contract(&interface));
}

#[test]
fn member_effect_requires_its_own_authority_family() {
    let mut interface = companion_interface("reference");
    interface.resource_ensures[1] = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "different".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    )
    .with_role(CResourceTransferRole::Produce);
    assert!(authority_member_effect(&interface).is_none());
    assert!(!authority_produces_member_contract(&interface));
    assert!(!authority_supports_resource_contract(&interface));
}
#[test]
fn effect_cannot_hide_an_unprotected_composite_birth() {
    let mut interface = companion_interface("reference");
    interface.resource_ensures.push(
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            "unprotected".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
        )
        .with_role(CResourceTransferRole::Produce),
    );
    assert!(!authority_supports_resource_contract(&interface));
}

#[test]
fn neutral_authority_requires_the_exact_borrowed_return() {
    let mut interface = companion_interface("reference");
    interface
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    interface.resource_ensures.clear();
    assert!(!authority_supports_resource_contract(&interface));
}
#[test]
fn resource_expansion_diagnostics_bound_the_named_frontier() {
    let resources = ResourceContext::new().unchecked_with_facts((0..32).map(|id| {
        CResourceFact::own(CResource::Composite {
            name: format!("resource_{id}_{}", "x".repeat(1000)),
            arguments: vec![CValue::pointer(Pointer::null()).into()].into(),
        })
    }));
    let diagnostic = bounded_contract_resource_frontier(&resources);
    assert!(diagnostic.len() < 600);
    assert!(diagnostic.contains("and 24 more clauses"));
    assert!(!diagnostic.contains("ResourceContext"));
    assert!(!diagnostic.contains("MemoryLoad"));
}
