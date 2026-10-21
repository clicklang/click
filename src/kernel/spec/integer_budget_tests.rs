use super::*;
use num_bigint::BigInt;
use num_traits::One;

#[test]
fn deferred_integer_multiply_precharges_product_work_without_active_tactic() {
    // Each operand is individually below the configured setup allowance,
    // while their product is deliberately above it.  This exercises the
    // same configured allowance used during setup, without an active
    // tactic supplying a separate work limit.
    let operand_bits = 1_000usize;
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 10_000,
        smart: 10_000,
        control: 10_000,
    };
    let expression = SpecIntegerExpression::Multiply(
        Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(
            BigInt::one() << operand_bits,
        ))),
        Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(
            BigInt::one() << operand_bits,
        ))),
    );

    let result = crate::instrumentation::with_tactic_work_limits(limits, || {
        evaluate_spec_integer_expression_paths_in(
            SpecScope::unbound(&CState::default(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
    });

    assert_eq!(result, Err(ExecutionLimit::Deadline));
}

#[test]
fn from_machine_requires_c_overflow_path_fact() {
    let left = Variable(31);
    let right = Variable(32);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let expression = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::CExpression(
        c_add(c_variable("left"), c_variable("right")),
    )));

    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&state, None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("symbolic machine addition should produce paths");
    let overflow = ConditionTerm::signed_add_overflows(left_bits, right_bits);
    assert_eq!(paths.len(), 1);
    assert!(
        paths[0]
            .facts
            .contains(&ExecutionPureFact::condition(overflow.clone(), false))
    );
    assert_eq!(paths[0].obligations.len(), 1);
    assert_eq!(
        paths[0].obligations[0].proposition,
        Proposition::ConditionIs(overflow, false)
    );
    assert!(!paths[0].obligations[0].assumable);
}

#[test]
fn integer_existential_scopes_definedness_with_its_witness() {
    fn contains(proposition: &Proposition, wanted: &Proposition) -> bool {
        if proposition == wanted {
            return true;
        }
        match proposition {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                contains(left, wanted) || contains(right, wanted)
            }
            Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
                contains(body, wanted)
            }
            _ => false,
        }
    }

    let left = Variable(701);
    let right = Variable(702);
    let witness = Variable(703);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let body = SpecProposition::ExistsInteger {
        name: "z".to_string(),
        variable: witness,
        body: Box::new(SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::var(witness)),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::FromMachine(Box::new(SpecExpression::CExpression(
                c_add(c_variable("left"), c_variable("right")),
            ))),
        }),
    };

    let paths = lower_spec_proposition_at_state_with_loop_entry_in(
        &state,
        &body,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("the Integer existential should lower");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].facts.is_empty());
    assert!(paths[0].obligations.is_empty());
    let Proposition::Exists {
        var,
        sort: Sort::Integer,
        body,
        ..
    } = &paths[0].proposition
    else {
        panic!("the lowered proposition must retain its Integer existential");
    };
    assert_eq!(*var, witness);
    let overflow = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(left_bits.clone()),
            Box::new(right_bits.clone()),
        ),
        false,
    );
    assert!(
        contains(body, &overflow),
        "the C definedness guard must stay inside the existential body: {body:?}"
    );
    assert!(
        contains(
            body,
            &Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(witness).into(),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        Bitvector32Term::Add(
                            Box::new(Bitvector32Term::Variable(left)),
                            Box::new(Bitvector32Term::Variable(right)),
                        ),
                    ))
                    .into(),
                ),
                true,
            )
        ),
        "the existential body must still compare the selected witness"
    );
}

#[test]
fn from_machine_keeps_signed_and_unsigned_values_distinct() {
    let signed = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        CValue::Int32(Bitvector32Term::Constant(u32::MAX)),
    )));
    let unsigned = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        CValue::UInt32(Bitvector32Term::Constant(u32::MAX)),
    )));
    let evaluate = |expression| {
        evaluate_spec_integer_expression_paths_in(
            SpecScope::unbound(&CState::default(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .unwrap()
        .pop()
        .unwrap()
        .value
    };

    assert_eq!(evaluate(signed), IntegerTerm::constant_i64(-1));
    assert_eq!(
        evaluate(unsigned),
        IntegerTerm::constant(BigInt::from(u32::MAX))
    );
}

#[test]
fn bitvector_substitution_reaches_machine_integer_proposition() {
    let variable = Variable(47);
    let proposition = Proposition::ConditionIs(
        ConditionTerm::integer_equal(
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(variable),
            )),
            IntegerTerm::constant_i64(7),
        ),
        true,
    );
    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
        &proposition,
        variable,
        &Bitvector32Term::Constant(7),
    );
    // Substitution reached inside the machine-backed Integer term. The
    // observation it left behind is decided -- `to_integer(7)` is the
    // mathematical 7, the same Integer the evaluation below produces for
    // the same machine constant -- so the equation against 7 is decided
    // too, by the Integer equality's own smart constructor.
    assert_eq!(
        substituted,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    );

    let expression = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
        CValue::Int32(Bitvector32Term::Constant(7)),
    )));
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&CState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .unwrap();
    assert_eq!(paths[0].value, IntegerTerm::constant_i64(7));
}

#[test]
fn integer_fold_loadable_obligation_keeps_carriers_separate() {
    let shared_id = Variable(71_100);
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
        end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(4)),
    };
    let integer_address = Bitvector32Term::IntegerToMachine {
        value: IntegerTerm::var(shared_id).into(),
        destination: MachineIntegerType::Int32,
    };
    let integer_address_requirement = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(integer_address),
                byte_width: 4,
            },
        },
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let wrapped = integer_range_fold_body_obligation(
        integer_address_requirement,
        &index,
        shared_id,
        shared_id,
    );
    let Proposition::ForAll {
        var: accumulator,
        sort: Sort::Integer,
        body: item_body,
        ..
    } = wrapped
    else {
        panic!("an Integer address must retain its Integer binder");
    };
    assert_eq!(accumulator, shared_id);
    assert!(matches!(
        item_body.as_ref(),
        Proposition::ForAll {
            var,
            sort: Sort::CInt32,
            ..
        } if *var == shared_id
    ));

    let c_address_requirement = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(shared_id)),
                byte_width: 4,
            },
        },
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let wrapped =
        integer_range_fold_body_obligation(c_address_requirement, &index, shared_id, shared_id);
    let Proposition::ForAll {
        var,
        sort: Sort::CInt32,
        ..
    } = wrapped
    else {
        panic!("a C item with the same numeric id must not bind an Integer");
    };
    assert_eq!(var, shared_id);
}

#[test]
fn integer_fold_loadable_obligation_sees_integer_in_registered_pointer() {
    let accumulator = Variable(71_106);
    let item = Variable(71_107);
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::IntegerToMachine {
                value: IntegerTerm::var(accumulator).into(),
                destination: MachineIntegerType::Int32,
            }),
            byte_width: 4,
        },
    };
    let load = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Bits32,
    );
    let requirement = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(load)),
                byte_width: 4,
            },
        },
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
        end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(4)),
    };
    let wrapped = integer_range_fold_body_obligation(requirement, &index, accumulator, item);
    assert!(matches!(
        wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));

    let direct_requirement = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Variable(load),
        },
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let direct_wrapped =
        integer_range_fold_body_obligation(direct_requirement, &index, accumulator, item);
    assert!(matches!(
        direct_wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));
}

#[test]
fn integer_fold_loadable_obligation_keeps_accumulator_for_two_hop_direct_offset() {
    let accumulator = Variable(71_108);
    let item = Variable(71_109);
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
    let inner = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::IntegerToMachine {
                    value: IntegerTerm::var(accumulator).into(),
                    destination: MachineIntegerType::Int32,
                }),
                byte_width: 4,
            },
        },
        crate::kernel::LoadKind::Bits32,
    );
    let outer = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(0)),
                Box::new(PointerOffsetTerm::Variable(inner)),
            ),
        },
        crate::kernel::LoadKind::Bits32,
    );
    let requirement = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Variable(outer),
        },
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let index = IntegerRangeFoldIndex::Int32 {
        start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
        end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(4)),
    };
    let wrapped = integer_range_fold_body_obligation(requirement, &index, accumulator, item);
    assert!(matches!(
        wrapped,
        Proposition::ForAll {
            var,
            sort: Sort::Integer,
            ..
        } if var == accumulator
    ));
}

#[test]
fn fold_body_drops_only_exact_registered_load_definition_conjuncts() {
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load = crate::kernel::eval::load_variable_for_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Bits32,
    );
    let (registered_memory, registered_pointer) =
        crate::kernel::eval::registered_load_for_variable(&load)
            .expect("the load variable must retain its exact descriptor");
    let defining = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(load)),
            Box::new(Bitvector32Term::MemoryLoad(
                registered_memory.clone(),
                Box::new(registered_pointer.clone()),
                crate::kernel::LoadKind::Bits32,
            )),
        ),
        true,
    );
    let loadable = Proposition::CMemoryLoadable {
        memory: registered_memory.as_ref().clone(),
        base: registered_pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let exact = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(defining.clone()),
        Box::new(loadable.clone()),
    ))
    .expect("the viewability conjunct must remain");
    assert!(matches!(exact, Proposition::CMemoryLoadable { .. }));

    let guarded = Proposition::Implies(Box::new(defining), Box::new(loadable.clone()));
    let retained_guard = drop_verified_load_definition_conjuncts(guarded.clone())
        .expect("a guarded definition must remain a guarded obligation");
    assert_eq!(retained_guard, guarded);

    let tampered_pointer = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(load)),
            Box::new(Bitvector32Term::MemoryLoad(
                registered_memory.clone(),
                Box::new(Pointer {
                    offset: PointerOffsetTerm::Constant(4),
                    ..registered_pointer.clone()
                }),
                crate::kernel::LoadKind::Bits32,
            )),
        ),
        true,
    );
    let retained_pointer = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(tampered_pointer),
        Box::new(loadable),
    ))
    .expect("a tampered definition must remain an obligation");
    assert!(matches!(retained_pointer, Proposition::And(_, _)));

    let tampered_memory = crate::kernel::intern_c_memory(CMemory::new().with_block("other", 16));
    let tampered_snapshot = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(load)),
            Box::new(Bitvector32Term::MemoryLoad(
                tampered_memory,
                Box::new(registered_pointer.clone()),
                crate::kernel::LoadKind::Bits32,
            )),
        ),
        true,
    );
    let retained_snapshot = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(tampered_snapshot),
        Box::new(Proposition::CMemoryLoadable {
            memory: registered_memory.as_ref().clone(),
            base: registered_pointer.clone(),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        }),
    ))
    .expect("a tampered snapshot must remain an obligation");
    assert!(matches!(retained_snapshot, Proposition::And(_, _)));

    let unknown = Variable((1u64 << 40) + 123_456_789);
    let unknown_definition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(unknown)),
            Box::new(Bitvector32Term::MemoryLoad(
                registered_memory,
                Box::new(registered_pointer),
                crate::kernel::LoadKind::Bits32,
            )),
        ),
        true,
    );
    let retained_unknown = drop_verified_load_definition_conjuncts(Proposition::And(
        Box::new(unknown_definition),
        Box::new(Proposition::CMemoryLoadable {
            memory: memory.as_ref().clone(),
            base: pointer,
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        }),
    ))
    .expect("an unknown reserved variable must remain an obligation");
    assert!(matches!(retained_unknown, Proposition::And(_, _)));
}

#[test]
fn defined_memory_load_retains_typed_validity_after_dropping_registry_metadata() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let proposition = SpecProposition::Defined(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(CMemory::new()),
        pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
            pointer,
            CType::Int32Pointer,
        )))),
        value_type: CType::Int32,
    });

    let paths = lower_spec_proposition_at_state_with_loop_entry_in(
        &CState::default(),
        &proposition,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("a symbolic load should lower to a definedness obligation");
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        &paths[0].proposition,
        Proposition::CMemoryReadDefined {
            value_type: CType::Int32,
            ..
        }
    ));
    assert!(!matches!(
        &paths[0].proposition,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ));
}

#[test]
fn integer_existential_branch_filters_exact_load_definitions_only() {
    fn contains(proposition: &Proposition, wanted: &Proposition) -> bool {
        if proposition == wanted {
            return true;
        }
        match proposition {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                contains(left, wanted) || contains(right, wanted)
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => contains(body, wanted),
            _ => false,
        }
    }

    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
    let pointer = Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load = crate::kernel::eval::load_variable_for_exact_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Bits32,
        4,
    );
    let (registered_memory, registered_pointer) =
        crate::kernel::eval::registered_load_for_variable(&load)
            .expect("the exact load must have a registry descriptor");
    let defining = |memory: SharedCMemory, pointer: Pointer, variable: Variable| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::MemoryLoad(
                    memory,
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32,
                )),
            ),
            true,
        )
    };
    let exact = defining(registered_memory.clone(), registered_pointer.clone(), load);
    let loadable = Proposition::CMemoryLoadable {
        memory: registered_memory.as_ref().clone(),
        base: registered_pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let marker = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let exact_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(exact.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(exact.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let exact_branch = existential_body_branch(&exact_path);
    assert!(!contains(&exact_branch, &exact));
    assert!(contains(&exact_branch, &loadable));
    assert!(contains(&exact_branch, &marker));

    let tampered_pointer = Pointer {
        offset: PointerOffsetTerm::Constant(4),
        ..registered_pointer.clone()
    };
    let tampered_pointer_definition = defining(registered_memory.clone(), tampered_pointer, load);
    let tampered_pointer_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(
            tampered_pointer_definition.clone(),
        )]
        .into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(tampered_pointer_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let tampered_pointer_branch = existential_body_branch(&tampered_pointer_path);
    assert!(contains(
        &tampered_pointer_branch,
        &tampered_pointer_definition
    ));
    assert!(contains(&tampered_pointer_branch, &loadable));

    let other_memory = crate::kernel::intern_c_memory(CMemory::new().with_block("other", 16));
    let tampered_snapshot_definition = defining(other_memory, registered_pointer.clone(), load);
    let tampered_snapshot_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(
            tampered_snapshot_definition.clone(),
        )]
        .into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(tampered_snapshot_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let tampered_snapshot_branch = existential_body_branch(&tampered_snapshot_path);
    assert!(contains(
        &tampered_snapshot_branch,
        &tampered_snapshot_definition
    ));

    let unknown = Variable((1u64 << 40) + 123_456_789);
    let unknown_definition = defining(registered_memory, registered_pointer, unknown);
    let unknown_path = SpecPropositionPath {
        proposition: marker.clone(),
        facts: vec![ExecutionPureFact::certified(unknown_definition.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(Proposition::And(
            Box::new(unknown_definition.clone()),
            Box::new(loadable.clone()),
        ))],
        introductions: LoweringIntroductions::new(),
    };
    let unknown_branch = existential_body_branch(&unknown_path);
    assert!(contains(&unknown_branch, &unknown_definition));

    // The normalizer does not manufacture a source memory guard. A path
    // carrying only a registered definition therefore retains no
    // CMemoryLoadable evidence and cannot satisfy a missing-guard goal.
    let missing_loadability_path = SpecPropositionPath {
        proposition: marker,
        facts: vec![ExecutionPureFact::certified(exact.clone())].into(),
        obligations: vec![ProofObligation::verification_condition(exact)],
        introductions: LoweringIntroductions::new(),
    };
    let missing_loadability_branch = existential_body_branch(&missing_loadability_path);
    assert!(!contains(&missing_loadability_branch, &loadable));
}

#[test]
fn empty_integer_fold_preserves_shape_without_live_load_obligation() {
    let missing_pointer = Pointer {
        block: PointerBlock::Concrete("missing".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let body = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(CMemory::new()),
        pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
            missing_pointer.clone(),
            CType::Int32Pointer,
        )))),
        value_type: CType::Int32,
    }));
    let expression = SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(4),
            ))),
            end: Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(4),
            ))),
        },
        initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(19))),
        accumulator: Variable(71_101),
        item: Variable(71_102),
        body: Box::new(body),
    };
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&CState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("an empty range still typechecks its body");
    assert_eq!(paths.len(), 1);
    let IntegerTerm::RangeFold { body, .. } = &paths[0].value else {
        panic!("empty fold capture lost the fold shape");
    };
    let IntegerTerm::Machine(machine) = body.as_ref() else {
        panic!("empty fold body lost its symbolic load")
    };
    let load_pointer = match machine.value() {
        Bitvector32Term::MemoryLoad(_, pointer, _) => pointer.as_ref().clone(),
        Bitvector32Term::Variable(load) => crate::kernel::eval::registered_load_for_variable(load)
            .map(|(_, pointer)| pointer)
            .expect("registered symbolic load must retain its pointer"),
        _ => panic!("empty fold body lost its symbolic load"),
    };
    assert_eq!(load_pointer, missing_pointer);
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn nonempty_integer_fold_is_logical_but_checked_reads_remain_scoped() {
    let item = Variable(71_103);
    let pointer = SpecExpression::PointerOffset {
        pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
            Pointer {
                block: PointerBlock::Symbolic(Variable(71_104)),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::Int32Pointer,
        )))),
        elements: Box::new(SpecExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(item),
        ))),
        byte_width: 4,
    };
    let body = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
        memory: SpecMemory::Fixed(CMemory::new()),
        pointer: Box::new(pointer),
        value_type: CType::Int32,
    }));
    let expression = SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(0),
            ))),
            end: Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(4),
            ))),
        },
        initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
        accumulator: Variable(71_105),
        item,
        body: Box::new(body),
    };
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&CState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("a symbolic body load should produce one scoped path");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    let checked = evaluate_spec_integer_expression_paths_in(
        SpecScope::unbound(&CState::default(), None),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::checked(&mut ExecutionBudget::default()),
    )
    .expect("checked fold preserves the binder around read validity");
    assert_eq!(checked.len(), 1);
    assert!(checked[0].obligations.iter().any(|obligation| {
        matches!(obligation.proposition(), Proposition::ForAll {
                var, sort: Sort::CInt32, body,
.. } if *var == item && matches!(body.as_ref(), Proposition::Implies(_, _)))
    }));
}

#[test]
fn integer_to_machine_converts_exact_boundaries_without_wrapping() {
    let cases = [
        (
            MachineIntegerType::Int8,
            BigInt::from(i8::MIN),
            CValue::Int8(Bitvector32Term::Constant(i8::MIN as i32 as u32)),
        ),
        (
            MachineIntegerType::Int16,
            BigInt::from(i16::MIN),
            CValue::Int16(Bitvector32Term::Constant(i16::MIN as i32 as u32)),
        ),
        (
            MachineIntegerType::Int32,
            BigInt::from(i32::MIN),
            CValue::Int32(Bitvector32Term::Constant(i32::MIN as u32)),
        ),
        (
            MachineIntegerType::UInt8,
            BigInt::from(u8::MAX),
            CValue::UInt8(Bitvector32Term::Constant(u8::MAX as u32)),
        ),
        (
            MachineIntegerType::UInt16,
            BigInt::from(u16::MAX),
            CValue::UInt16(Bitvector32Term::Constant(u16::MAX as u32)),
        ),
        (
            MachineIntegerType::UInt32,
            BigInt::from(u32::MAX),
            CValue::UInt32(Bitvector32Term::Constant(u32::MAX)),
        ),
        (
            MachineIntegerType::Int64,
            BigInt::from(i64::MIN),
            CValue::Int64(Bitvector32Term::Int64Constant(i64::MIN)),
        ),
        (
            MachineIntegerType::UInt64,
            BigInt::from(u64::MAX),
            CValue::UInt64(Bitvector32Term::UInt64Constant(u64::MAX)),
        ),
    ];
    for (destination, integer, expected) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(integer))),
            destination,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &CState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .expect("representable Integer constants should convert");
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value, expected);
    }
}

#[test]
fn integer_to_machine_rejects_out_of_range_constants() {
    let cases = [
        (MachineIntegerType::Int8, BigInt::from(i8::MIN) - 1),
        (MachineIntegerType::Int8, BigInt::from(i8::MAX) + 1),
        (MachineIntegerType::Int16, BigInt::from(i16::MAX) + 1),
        (MachineIntegerType::Int32, BigInt::from(i32::MIN) - 1),
        (MachineIntegerType::UInt8, BigInt::from(-1)),
        (MachineIntegerType::UInt16, BigInt::from(u16::MAX) + 1),
        (MachineIntegerType::UInt32, BigInt::from(u32::MAX) + 1),
        (MachineIntegerType::Int64, BigInt::from(i64::MAX) + 1),
        (MachineIntegerType::UInt64, BigInt::from(u64::MAX) + 1),
    ];
    for (destination, integer) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant(integer))),
            destination,
        };
        let result = evaluate_spec_expression_paths_with_loop_entry_in(
            &CState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        );
        assert_eq!(result, Err(ExecutionLimit::Paths));
    }
}

#[test]
fn integer_to_machine_symbolic_values_keep_carrier_and_range_obligations() {
    let variable = Variable(990);
    let value = IntegerTerm::Variable(variable);
    let cases = [
        (
            MachineIntegerType::Int8,
            BigInt::from(i8::MIN),
            BigInt::from(i8::MAX),
        ),
        (
            MachineIntegerType::Int16,
            BigInt::from(i16::MIN),
            BigInt::from(i16::MAX),
        ),
        (
            MachineIntegerType::Int32,
            BigInt::from(i32::MIN),
            BigInt::from(i32::MAX),
        ),
        (
            MachineIntegerType::UInt8,
            BigInt::from(0),
            BigInt::from(u8::MAX),
        ),
        (
            MachineIntegerType::UInt16,
            BigInt::from(0),
            BigInt::from(u16::MAX),
        ),
        (
            MachineIntegerType::UInt32,
            BigInt::from(0),
            BigInt::from(u32::MAX),
        ),
        (
            MachineIntegerType::Int64,
            BigInt::from(i64::MIN),
            BigInt::from(i64::MAX),
        ),
        (
            MachineIntegerType::UInt64,
            BigInt::from(0),
            BigInt::from(u64::MAX),
        ),
    ];
    for (destination, expected_lower, expected_upper) in cases {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(value.clone())),
            destination,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &CState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .expect("symbolic conversion should produce a path");
        assert_eq!(paths.len(), 1);
        assert!(paths[0].facts.is_empty());
        assert!(matches!(
            &paths[0].value,
            CValue::Int8(Bitvector32Term::IntegerToMachine { destination: d, .. }) | CValue::Int16(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::Int32(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::UInt8(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::UInt16(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::UInt32(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::Int64(Bitvector32Term::IntegerToMachine { destination: d, .. })
                | CValue::UInt64(Bitvector32Term::IntegerToMachine { destination: d, .. })
                if *d == destination
        ));
        assert_eq!(paths[0].obligations.len(), 2);
        assert!(
            paths[0]
                .obligations
                .iter()
                .all(|obligation| !obligation.is_assumable())
        );
        let lower = IntegerTerm::constant(expected_lower);
        let upper = IntegerTerm::constant(expected_upper);
        assert!(paths[0].obligations.iter().any(|obligation| {
            *obligation.proposition()
                == Proposition::ConditionIs(
                    ConditionTerm::integer_greater_equal(value.clone(), lower.clone()),
                    true,
                )
        }));
        assert!(paths[0].obligations.iter().any(|obligation| {
            *obligation.proposition()
                == Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(value.clone(), upper.clone()),
                    true,
                )
        }));
    }

    let left = Variable(991);
    let right = Variable(992);
    let state = CState::new()
        .with_local("left", int32(Bitvector32Term::Variable(left)))
        .with_local("right", int32(Bitvector32Term::Variable(right)));
    let expression = SpecExpression::IntegerToMachine {
        value: Box::new(SpecIntegerExpression::FromMachine(Box::new(
            SpecExpression::CExpression(c_add(c_variable("left"), c_variable("right"))),
        ))),
        destination: MachineIntegerType::Int32,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &state,
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
    )
    .expect("child expression effects should be preserved");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].facts.contains(&ExecutionPureFact::condition(
        ConditionTerm::signed_add_overflows(
            Bitvector32Term::Variable(left),
            Bitvector32Term::Variable(right),
        ),
        false,
    )));
    assert_eq!(paths[0].obligations.len(), 3);
    assert!(
        paths[0]
            .obligations
            .iter()
            .all(|obligation| !obligation.is_assumable())
    );
    assert!(
        paths[0]
            .obligations
            .iter()
            .any(|obligation| obligation.proposition()
                == &Proposition::ConditionIs(
                    ConditionTerm::signed_add_overflows(
                        Bitvector32Term::Variable(left),
                        Bitvector32Term::Variable(right)
                    ),
                    false
                ))
    );
}
