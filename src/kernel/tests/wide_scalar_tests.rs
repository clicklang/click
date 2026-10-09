use super::*;
use num_bigint::BigInt;

fn evaluated(expression: CExpression) -> CExpressionOutcome {
    let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        panic!("expected expression evaluation");
    };
    outcome.clone()
}

#[test]
fn wide_scalar_literals_preserve_full_payload_and_exact_integer_observations() {
    for (ty, integer) in [
        (MachineIntegerType::Int128, BigInt::from(i128::MIN)),
        (MachineIntegerType::Int128, BigInt::from(i128::MAX)),
        (MachineIntegerType::Int128, BigInt::from(-1)),
        (MachineIntegerType::UInt128, BigInt::from(u128::MAX)),
        (MachineIntegerType::UInt128, BigInt::from(1u128 << 64)),
        (MachineIntegerType::UInt128, BigInt::from(0)),
    ] {
        let constant = MachineIntegerConstant::from_integer(ty.format(), &integer).unwrap();
        let value = ty.constant_value(constant).unwrap();
        assert_eq!(value.c_type(), ty.c_type());
        assert_eq!(value.byte_width(), 16);
        assert_eq!(ty.c_type().byte_width(), 16);
        assert_eq!(ty.c_type().abi_alignment(), 16);
        assert_eq!(ty.constant_from_value(&value), Some(constant));
        let term = ty.constant_term(constant).unwrap();
        assert_eq!(term.as_const(), None);
        assert_eq!(term.int64_as_const(), None);
        assert_eq!(term.uint64_as_const(), None);
        assert_eq!(
            IntegerTerm::from_machine(ty, term).unwrap().as_const(),
            Some(&integer)
        );
        assert_eq!(
            evaluated(CExpression::Value(value.clone())),
            CExpressionOutcome::Value(value)
        );
    }
    assert_eq!(
        evaluated(c_int128_literal(i128::MIN)),
        evaluated(CExpression::Value(
            MachineIntegerType::Int128
                .constant_value(
                    MachineIntegerConstant::from_signed(
                        MachineIntegerType::Int128.format(),
                        i128::MIN
                    )
                    .unwrap()
                )
                .unwrap()
        ))
    );
    assert_eq!(
        evaluated(c_uint128_literal(u128::MAX)),
        evaluated(CExpression::Value(
            MachineIntegerType::UInt128
                .constant_value(
                    MachineIntegerConstant::from_unsigned(
                        MachineIntegerType::UInt128.format(),
                        u128::MAX
                    )
                    .unwrap()
                )
                .unwrap()
        ))
    );
}

#[test]
fn wide_scalar_locals_declare_assign_and_return_without_word_truncation() {
    for (ty, literal) in [
        (CType::Int128, c_int128_literal(i128::MIN)),
        (CType::UInt128, c_uint128_literal(u128::MAX)),
    ] {
        let CExpressionOutcome::Value(expected) = evaluated(literal.clone()) else {
            unreachable!()
        };
        let statement = c_seq(
            c_declare("wide", ty),
            c_seq(c_assign("wide", literal), c_return(c_variable("wide"))),
        );
        let theorem = prove_c_statement_execution(CState::new(), statement).unwrap();
        let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
            unreachable!()
        };
        let CStatementOutcome::Return { value, state } = outcome else {
            panic!("{outcome:?}");
        };
        assert_eq!(value, &expected);
        assert_eq!(state.locals.get("wide"), Some(&expected));
    }
}

#[test]
fn wide_scalar_symbolic_identity_substitution_and_observation_preserve_type() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let variable = Variable(148_001);
        let value = symbolic_call_result(ty.c_type(), variable);
        let state = CState::new().with_local("wide", value.clone());
        let theorem = prove_c_expression_evaluation(state, c_variable("wide")).unwrap();
        let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
            unreachable!()
        };
        assert_eq!(outcome, &CExpressionOutcome::Value(value.clone()));
        let term = Bitvector32Term::Variable(variable);
        let observation = IntegerTerm::from_machine(ty, term).unwrap();
        let IntegerTerm::Machine(observed) = observation else {
            unreachable!()
        };
        assert_eq!(observed.ty(), ty);
        let (min, max) = ty.format().bounds();
        for integer in [min, max] {
            let constant = MachineIntegerConstant::from_integer(ty.format(), &integer).unwrap();
            let substituted = substitute_bitvector_variable_in_c_value(
                &value,
                variable,
                &ty.constant_term(constant).unwrap(),
            );
            assert_eq!(ty.constant_from_value(&substituted), Some(constant));
            assert_eq!(substituted.c_type(), ty.c_type());
        }
    }
}

#[test]
fn wide_scalar_rejects_legacy_carriers_and_unsupported_arithmetic() {
    let assert_mismatch = |expression| {
        assert_eq!(
            evaluated(expression),
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        )
    };
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let other = if ty == MachineIntegerType::Int128 {
            MachineIntegerType::UInt128
        } else {
            MachineIntegerType::Int128
        };
        let wrong = other
            .constant_term(MachineIntegerConstant::from_unsigned(other.format(), 1).unwrap())
            .unwrap();
        for term in [
            Bitvector32Term::Constant(1),
            Bitvector32Term::Int64Constant(1),
            Bitvector32Term::UInt64Constant(1),
            wrong,
            Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(Variable(148_002))),
                Box::new(Bitvector32Term::Constant(1)),
            ),
        ] {
            assert!(IntegerTerm::from_machine(ty, term.clone()).is_none());
            let value = if ty == MachineIntegerType::Int128 {
                CValue::Int128(term)
            } else {
                CValue::UInt128(term)
            };
            assert_mismatch(CExpression::Value(value));
        }
    }
    for expression in [
        c_add(c_int128_literal(1), c_int128_literal(2)),
        c_multiply(c_uint128_literal(1), c_uint128_literal(2)),
        c_subtract(c_int128_literal(1), c_int128_literal(2)),
    ] {
        assert_mismatch(expression);
    }
    let value = symbolic_call_result(CType::UInt128, Variable(148_003));
    assert_eq!(LoadKind::of_value(&value), Some(LoadKind::UInt128));
    assert_eq!(LoadKind::of_type(CType::UInt128), Some(LoadKind::UInt128));
    assert_eq!(CType::UInt128.pointer_to(), Some(CType::UInt128Pointer));
}

#[test]
fn wide_scalar_truthiness_uses_all_bits_and_retains_symbolic_guards() {
    for (expression, expected) in [
        (c_uint128_literal(0), 1),
        (c_uint128_literal(1u128 << 64), 0),
        (c_uint128_literal(u128::MAX), 0),
        (c_int128_literal(i128::MIN), 0),
        (c_int128_literal(0), 1),
    ] {
        assert_eq!(
            evaluated(c_not(expression)),
            CExpressionOutcome::Value(int32(expected))
        );
    }
    let state = CState::new().with_local(
        "wide",
        symbolic_call_result(CType::UInt128, Variable(148_004)),
    );
    let expression = c_not(c_variable("wide"));
    let paths = evaluate_c_expression_paths(
        &state,
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::for_c_expression(&expression),
    )
    .unwrap();
    assert_eq!(paths.len(), 2);
    for path in paths {
        assert!(matches!(
            path.outcome,
            CExpressionOutcome::Value(CValue::Int32(_))
        ));
        assert!(path.facts.iter().any(|fact| matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), _)
        )));
    }
}

#[test]
fn wide_scalar_boolean_cast_observes_high_bits_without_narrowing() {
    for (input, expected) in [
        (c_uint128_literal(0), 0),
        (c_uint128_literal(1u128 << 64), 1),
        (c_uint128_literal(u128::MAX), 1),
        (c_int128_literal(i128::MIN), 1),
    ] {
        assert_eq!(
            evaluated(c_cast(input, CType::Bool)),
            CExpressionOutcome::Value(CValue::Bool(Bitvector32Term::Constant(expected)))
        );
    }
}

#[test]
fn wide_scalar_observation_work_scales_with_explicit_values() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (observations, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..size)
                .map(|index| {
                    IntegerTerm::from_machine(
                        MachineIntegerType::UInt128,
                        Bitvector32Term::Variable(Variable(149_000 + index)),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>()
        });
        assert_eq!(observations.len(), size as usize);
        assert!(
            work >= size as usize && work <= 32 * size as usize,
            "{size}: {work}"
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn wide_scalar_function_parameters_and_returns_keep_caller_storage() {
    for (ty, argument) in [
        (CType::Int128, c_int128_literal(i128::MIN)),
        (CType::UInt128, c_uint128_literal(u128::MAX)),
    ] {
        let function = c_function(
            ty,
            "wide_identity",
            vec![c_parameter("input", ty)],
            c_return(c_variable("input")),
        );
        let state = CState::new().with_local("caller", int32(99));
        let expected = evaluated(argument.clone());
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function,
            vec![argument],
            PureFactContext::new(),
        )
        .unwrap();
        let Proposition::CFunctionExecutes { outcome, .. } = theorem.proposition() else {
            unreachable!()
        };
        let CFunctionOutcome::Return {
            value,
            state: returned,
        } = outcome
        else {
            panic!("{outcome:?}");
        };
        assert_eq!(CExpressionOutcome::Value(value.clone()), expected);
        assert_eq!(**returned, state);
    }
}

#[test]
fn wide_scalar_root_validation_does_not_scan_legacy_operand_trees() {
    for size in [16, 64, 256, 1024] {
        let mut term = Bitvector32Term::Variable(Variable(148_006));
        for _ in 0..size {
            term = Bitvector32Term::UInt64Add(
                Box::new(term),
                Box::new(Bitvector32Term::UInt64Constant(1)),
            );
        }
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineIntegerType::UInt128.accepts_wide_term(&term)
        });
        assert!(!accepted);
        assert_eq!(work, 1);
    }
}

#[test]
fn wide_cast_widening_preserves_integer_observation_but_narrowing_does_not() {
    for source in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let term = Bitvector32Term::Variable(Variable(149_003));
        let wide =
            Bitvector32Term::machine_integer_cast(source, MachineIntegerType::Int128, term.clone());
        assert_eq!(
            IntegerTerm::from_machine(MachineIntegerType::Int128, wide).unwrap(),
            IntegerTerm::from_machine(source, term).unwrap()
        );
    }
    let term = Bitvector32Term::Variable(Variable(149_004));
    let narrowed = Bitvector32Term::machine_integer_cast(
        MachineIntegerType::UInt128,
        MachineIntegerType::Int64,
        term.clone(),
    );
    let observation = IntegerTerm::from_machine(MachineIntegerType::Int64, narrowed).unwrap();
    assert_ne!(
        observation,
        IntegerTerm::from_machine(MachineIntegerType::UInt128, term).unwrap()
    );
    let IntegerTerm::Machine(machine) = observation else {
        unreachable!()
    };
    assert_eq!(machine.ty(), MachineIntegerType::Int64);
    assert!(matches!(
        machine.value(),
        Bitvector32Term::MachineIntegerCast {
            source: MachineIntegerType::UInt128,
            destination: MachineIntegerType::Int64,
            ..
        }
    ));
}

#[test]
fn wide_cast_runtime_preserves_modulo_policy_and_operand_definedness() {
    assert_eq!(
        evaluated(c_integer_cast_modulo(c_int128_literal(-1), CType::UInt64)),
        evaluated(c_uint64_literal(u64::MAX))
    );
    assert_eq!(
        evaluated(c_integer_cast_modulo(
            c_uint128_literal(u128::MAX),
            CType::Int64
        )),
        evaluated(c_int64_literal(-1))
    );
    assert_eq!(
        evaluated(c_integer_cast_modulo(c_int64_literal(-1), CType::UInt128)),
        evaluated(c_uint128_literal(u128::MAX))
    );
    assert_eq!(
        evaluated(c_cast(c_uint64_literal(u64::MAX), CType::Int128)),
        evaluated(c_int128_literal(i128::from(u64::MAX)))
    );
    assert_eq!(
        evaluated(c_cast(c_int128_literal(-1), CType::UInt64)),
        evaluated(c_uint64_literal(u64::MAX))
    );
    assert!(matches!(
        evaluated(c_cast(c_uint128_literal(u128::MAX), CType::Int64)),
        CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    ));
    assert!(matches!(
        evaluated(c_integer_cast_modulo(
            c_divide(c_int64_literal(1), c_int64_literal(0)),
            CType::Int128
        )),
        CExpressionOutcome::UndefinedBehavior(_)
    ));
    assert!(matches!(
        evaluated(c_integer_cast_modulo(
            c_add(c_int64_literal(i64::MAX), c_int64_literal(1)),
            CType::Int128
        )),
        CExpressionOutcome::UndefinedBehavior(_)
    ));
}

#[test]
fn wide_cast_ordinary_signed_narrowing_keeps_both_range_obligations() {
    let value = CValue::Int128(Bitvector32Term::Variable(Variable(149_005)));
    let mut obligations = Vec::new();
    let result = coerce_c_value_to_type(
        value,
        CType::Int64,
        &mut obligations,
        &PureFactContext::new(),
    )
    .unwrap();
    assert_eq!(result.c_type(), CType::Int64);
    assert_eq!(obligations.len(), 2);
    for kind in [true, false] {
        assert!(
            obligations
                .iter()
                .any(|obligation| match obligation.proposition() {
                    Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(_, _), true) =>
                        kind,
                    Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(_, _), true) => !kind,
                    _ => false,
                })
        );
    }
    let bounds: Vec<_> = obligations
        .iter()
        .map(|obligation| obligation.proposition().clone())
        .collect();
    for provided in 0..=2 {
        let mut assumptions = PureFactContext::new();
        for proposition in &bounds[..provided] {
            let Proposition::ConditionIs(condition, true) = proposition else {
                unreachable!()
            };
            assumptions = assumptions.assume_condition(condition.clone(), true);
        }
        let mut remaining = Vec::new();
        let result = coerce_c_value_to_type(
            CValue::Int128(Bitvector32Term::Variable(Variable(149_005))),
            CType::Int64,
            &mut remaining,
            &assumptions,
        )
        .unwrap();
        assert_eq!(result.c_type(), CType::Int64);
        assert_eq!(remaining.len(), 2 - provided);
    }
    let value = CValue::Int128(Bitvector32Term::Variable(Variable(149_005)));
    assert!(
        MachineIntegerType::Int64
            .convert_modulo_value(value)
            .is_some()
    );
}

#[test]
fn wide_cast_function_argument_widens_and_return_narrows_without_truncating_early() {
    let function = c_function(
        CType::UInt64,
        "wide_cast_call",
        vec![c_parameter("input", CType::Int128)],
        c_return(c_integer_cast_modulo(c_variable("input"), CType::UInt64)),
    );
    let theorem = prove_symbolic_c_function_execution(
        CState::new(),
        function,
        vec![c_int64_literal(-1)],
        PureFactContext::new(),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CFunctionExecutes {
            outcome: CFunctionOutcome::Return {
                value: CValue::UInt64(Bitvector32Term::UInt64Constant(u64::MAX)),
                ..
            },
            ..
        }
    ));
}

#[test]
fn wide_cast_hostile_metadata_and_word_payloads_are_rejected_locally() {
    for term in [
        Bitvector32Term::MachineIntegerCast {
            source: MachineIntegerType::Int64,
            destination: MachineIntegerType::UInt128,
            value: Box::new(Bitvector32Term::Variable(Variable(149_006))),
        },
        Bitvector32Term::MachineIntegerCast {
            source: MachineIntegerType::Int128,
            destination: MachineIntegerType::Int128,
            value: Box::new(Bitvector32Term::Constant(1)),
        },
        Bitvector32Term::MachineIntegerCast {
            source: MachineIntegerType::Int64,
            destination: MachineIntegerType::Int128,
            value: Box::new(Bitvector32Term::UInt64Constant(1)),
        },
        Bitvector32Term::MachineIntegerCast {
            source: MachineIntegerType::Int64,
            destination: MachineIntegerType::Int128,
            value: Box::new(Bitvector32Term::MachineIntegerCast {
                source: MachineIntegerType::Int32,
                destination: MachineIntegerType::Int64,
                value: Box::new(Bitvector32Term::Int64Constant(1)),
            }),
        },
    ] {
        assert!(!MachineIntegerType::Int128.accepts_wide_term(&term));
        assert_eq!(
            evaluated(CExpression::Value(CValue::Int128(term))),
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        );
    }
    assert!(
        MachineIntegerType::Int128
            .convert_modulo_value(CValue::Int64(Bitvector32Term::MachineIntegerConstant(
                MachineIntegerConstant::from_unsigned(
                    MachineIntegerType::UInt128.format(),
                    u128::MAX
                )
                .unwrap()
            )))
            .is_none()
    );
}

#[test]
fn wide_cast_canonicalization_keeps_source_load_width_and_memory_dependencies() {
    let pointer = Pointer {
        block: "wide-cast-source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("wide-cast-source", 4).store(
        pointer.clone(),
        CValue::Int32(Bitvector32Term::Constant((-1i32) as u32)),
    );
    let load =
        Bitvector32Term::MemoryLoad(intern_c_memory(memory), Box::new(pointer), LoadKind::Bits32);
    let wide = Bitvector32Term::machine_integer_cast(
        MachineIntegerType::Int32,
        MachineIntegerType::Int128,
        load,
    );
    assert!(
        crate::kernel::memory_provenance::c_condition_fact_has_memory(&Proposition::ConditionIs(
            ConditionTerm::equal(wide.clone(), Bitvector32Term::Variable(Variable(149_009))),
            true
        ))
    );
    assert_eq!(
        crate::kernel::api::canonicalize_atomic_loads(&wide),
        MachineIntegerType::Int128
            .constant_term(
                MachineIntegerConstant::from_signed(MachineIntegerType::Int128.format(), -1)
                    .unwrap()
            )
            .unwrap()
    );
}

#[test]
fn uint64_to_int64_ordinary_cast_requires_exact_representable_range() {
    let bits = Bitvector32Term::Variable(Variable(149_100));
    let bound = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(
            bits.clone(),
            Bitvector32Term::UInt64Constant(i64::MAX as u64),
        ),
        true,
    );
    let mut obligations = Vec::new();
    let result = coerce_c_value_to_type(
        CValue::UInt64(bits.clone()),
        CType::Int64,
        &mut obligations,
        &PureFactContext::new(),
    )
    .unwrap();
    assert_eq!(result, CValue::Int64(bits.clone()));
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].proposition(), &bound);
    assert_eq!(
        obligations[0].context(),
        Some("int64 narrowing upper bound")
    );
    let assumptions = PureFactContext::new().assume_proposition(bound);
    let mut remaining = Vec::new();
    assert_eq!(
        coerce_c_value_to_type(
            CValue::UInt64(bits.clone()),
            CType::Int64,
            &mut remaining,
            &assumptions
        ),
        Some(result)
    );
    assert!(remaining.is_empty());
    let weaker = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(
            bits.clone(),
            Bitvector32Term::UInt64Constant((i64::MAX as u64) + 1),
        ),
        true,
    );
    let mut remaining = Vec::new();
    coerce_c_value_to_type(
        CValue::UInt64(bits),
        CType::Int64,
        &mut remaining,
        &PureFactContext::new().assume_proposition(weaker),
    )
    .unwrap();
    assert_eq!(remaining.len(), 1);
    for value in [0, 1, i64::MAX as u64] {
        assert_eq!(
            evaluated(c_cast(c_uint64_literal(value), CType::Int64)),
            evaluated(c_int64_literal(value as i64))
        );
    }
    for value in [(i64::MAX as u64) + 1, u64::MAX] {
        assert!(matches!(
            evaluated(c_cast(c_uint64_literal(value), CType::Int64)),
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        ));
        assert_eq!(
            evaluated(c_integer_cast_modulo(c_uint64_literal(value), CType::Int64)),
            evaluated(c_int64_literal(value as i64))
        );
    }
}

#[test]
fn wide_cached_load_canonicalization_preserves_kind_and_all_bits() {
    for signed in [false, true] {
        let pointer = Pointer {
            block: "wide-cached-read".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let bits = if signed {
            Bitvector32Term::Int64Constant(0x1_0000_0001)
        } else {
            Bitvector32Term::UInt64Constant(0x1_0000_0001)
        };
        let value = if signed {
            CValue::Int64(bits.clone())
        } else {
            CValue::UInt64(bits.clone())
        };
        let memory = intern_c_memory(
            CMemory::new()
                .with_block("wide-cached-read", 8)
                .store(pointer.clone(), value),
        );
        let load =
            |kind| Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind);
        assert_eq!(
            crate::kernel::api::canonicalize_atomic_loads(&load(LoadKind::Bits64)),
            bits
        );
        assert_ne!(
            crate::kernel::api::canonicalize_atomic_loads(&load(LoadKind::Bits32)),
            bits
        );
        let overwritten = intern_c_memory(
            memory
                .as_ref()
                .clone()
                .without_possible_aliasing_cells(
                    &pointer.offset_by_bytes(4),
                    4,
                    &PureFactContext::new(),
                )
                .store(
                    pointer.offset_by_bytes(4),
                    CValue::Int32(Bitvector32Term::Constant(0)),
                ),
        );
        let changed =
            Bitvector32Term::MemoryLoad(overwritten, Box::new(pointer.clone()), LoadKind::Bits64);
        assert!(
            !crate::kernel::memory_provenance::wide_loads_have_same_canonical_value(
                &changed,
                &load(LoadKind::Bits64),
                &PureFactContext::new()
            )
        );
    }
}

#[test]
fn wide_cached_load_canonicalization_ignores_unrelated_cells() {
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let pointer = Pointer {
            block: "wide-cached-scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let bits = Bitvector32Term::UInt64Constant(0x1_0000_0001);
        let mut memory = CMemory::new().with_block("wide-cached-scaling", (count + 1) * 8);
        for index in 1..=count {
            memory = memory.store(
                pointer.offset_by_bytes(index * 8),
                CValue::UInt64(Bitvector32Term::UInt64Constant(index as u64)),
            );
        }
        memory = memory.store(pointer.clone(), CValue::UInt64(bits.clone()));
        let load = Bitvector32Term::MemoryLoad(
            intern_c_memory(memory),
            Box::new(pointer),
            LoadKind::Bits64,
        );
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        crate::kernel::memory_provenance::reset_atomic_canonicalization_term_visits();
        let (result, work) = crate::persistent::measure_persistent_work(|| {
            crate::kernel::api::canonicalize_atomic_loads(&load)
        });
        assert_eq!(result, bits);
        samples.push((
            crate::kernel::memory_provenance::atomic_canonicalization_term_visits(),
            work,
        ));
    }
    assert!(
        samples.iter().all(|(visits, _)| *visits == samples[0].0),
        "{samples:?}"
    );
    assert!(samples[2].1 <= samples[0].1 * 4 + 32, "{samples:?}");
}
