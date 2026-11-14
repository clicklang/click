use super::*;
use crate::kernel::VerificationSession;
const FORMATS: [MachineIntegerType; 8] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
];
fn value(format: MachineIntegerType, id: u64) -> SpecExpression {
    SpecExpression::Value(format.value_from_term(MachineTerm::Variable(Variable(id))))
}
fn literal(format: MachineIntegerType, n: i64) -> SpecExpression {
    SpecExpression::Value(format.value_from_term(
        crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap(),
    ))
}
fn input(format: MachineIntegerType, term: &MachineTerm, shared: bool) -> SpecValue {
    if shared {
        KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(term)).into()
    } else {
        format.value_from_term(term.clone()).into()
    }
}
#[test]
fn bitwise_all_promotions_match_native_terms_without_exports() {
    let _session = VerificationSession::enter();
    for a in FORMATS {
        for b in FORMATS {
            let terms = |f: MachineIntegerType| {
                let (lo, hi) = f.format().bounds();
                let mut v = vec![
                    MachineTerm::Variable(Variable(995600)),
                    MachineTerm::opaque_conversion("bits", MachineTerm::Variable(Variable(995601))),
                ];
                if f.format().bits() >= 32 {
                    let one =
                        crate::kernel::machine_integer::range::constant_word(f, &1.into()).unwrap();
                    v.push(MachineTerm::Binary {
                        format: f,
                        op: MachineBinaryOp::Add,
                        left: Box::new(one.clone()),
                        right: Box::new(one),
                    });
                }
                for n in [lo, hi, 0.into(), 1.into()] {
                    v.push(crate::kernel::machine_integer::range::constant_word(f, &n).unwrap());
                }
                v
            };
            for left in terms(a) {
                for right in terms(b) {
                    for (op, native) in [
                        (MachineBinaryOp::BitwiseAnd, BitwiseOperation::And),
                        (MachineBinaryOp::BitwiseOr, BitwiseOperation::Or),
                        (MachineBinaryOp::BitwiseXor, BitwiseOperation::Xor),
                    ] {
                        let expected = apply_program_bitwise_binary(
                            a.value_from_term(left.clone()),
                            b.value_from_term(right.clone()),
                            ExecutionFacts::default(),
                            Vec::new(),
                            &PureFactContext::new(),
                            native,
                        )
                        .pop()
                        .unwrap();
                        let ExpressionOutcome::Value(expected) = expected.outcome else {
                            panic!()
                        };
                        for (l, r) in [(false, false), (true, false), (false, true), (true, true)] {
                            let exports = KernelTermExport::machine_export_count();
                            let result =
                                bitwise::apply(op, &input(a, &left, l), &input(b, &right, r))
                                    .unwrap();
                            assert_eq!(KernelTermExport::machine_export_count(), exports);
                            assert!(result.obligations.is_empty());
                            assert_eq!(
                                SpecValue::Shared(result.value).into_native(),
                                expected,
                                "{a:?}/{b:?} {op:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}
#[test]
fn bitwise_not_and_annotated_narrow_match_native() {
    let _session = VerificationSession::enter();
    for format in FORMATS {
        for term in [
            MachineTerm::Variable(Variable(995602)),
            MachineTerm::opaque_conversion("not", MachineTerm::Variable(Variable(995603))),
            crate::kernel::machine_integer::range::constant_word(format, &0.into()).unwrap(),
        ] {
            for shared in [false, true] {
                let value = input(format, &term, shared);
                let expected = apply_program_bitwise_not(
                    format.value_from_term(term.clone()),
                    ExecutionFacts::default(),
                    Vec::new(),
                )
                .pop()
                .unwrap();
                let exports = KernelTermExport::machine_export_count();
                let result = bitwise_not(&value, None).unwrap();
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert_eq!(
                    ExpressionOutcome::Value(SpecValue::Shared(result).into_native()),
                    expected.outcome
                );
            }
            if format.format().bits() < 32 {
                let operand = SpecExpression::Value(format.value_from_term(term));
                for operation in [
                    SpecExpression::BitwiseNot(Box::new(operand.clone())),
                    SpecExpression::BitwiseAnd(
                        Box::new(operand.clone()),
                        Box::new(operand.clone()),
                    ),
                    SpecExpression::BitwiseOr(
                        Box::new(operand.clone()),
                        Box::new(literal(format, 1)),
                    ),
                    SpecExpression::BitwiseXor(
                        Box::new(operand.clone()),
                        Box::new(literal(format, 1)),
                    ),
                ] {
                    let expression = SpecExpression::NarrowArithmetic(Box::new(operation), format);
                    assert_eq!(evaluate(&expression, false), evaluate(&expression, true));
                }
            }
        }
    }
}
#[test]
fn shared_bitwise_smart_constructors_preserve_native_component_normalization() {
    for format in &FORMATS[..8] {
        let x = value(*format, 993450);
        let zero = literal(*format, 0);
        for expression in [
            SpecExpression::BitwiseAnd(Box::new(x.clone()), Box::new(zero.clone())),
            SpecExpression::BitwiseOr(Box::new(x.clone()), Box::new(zero)),
            SpecExpression::BitwiseAnd(Box::new(x.clone()), Box::new(x.clone())),
            SpecExpression::BitwiseNot(Box::new(SpecExpression::BitwiseNot(Box::new(x.clone())))),
            SpecExpression::BitwiseXor(
                Box::new(SpecExpression::BitwiseXor(
                    Box::new(x.clone()),
                    Box::new(value(*format, 993451)),
                )),
                Box::new(x),
            ),
        ] {
            assert_eq!(
                evaluate(&expression, false),
                evaluate(&expression, true),
                "{format:?}: {expression:?}"
            );
        }
    }
    let format = MachineIntegerType::UInt64;
    let mask = |n| {
        Box::new(SpecExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_constant(n),
        )))
    };
    for operand in [
        value(format, 993452),
        SpecExpression::Value(ProgramValue::UInt64(MachineTerm::opaque_conversion(
            "opaque_bits",
            MachineTerm::Variable(Variable(993453)),
        ))),
    ] {
        for inner in [
            SpecExpression::BitwiseAnd(Box::new(operand.clone()), mask(7)),
            SpecExpression::BitwiseOr(Box::new(operand.clone()), mask(7)),
        ] {
            for expression in [
                SpecExpression::BitwiseAnd(Box::new(inner.clone()), mask(!3)),
                SpecExpression::BitwiseOr(Box::new(inner), mask(15)),
            ] {
                assert_eq!(evaluate(&expression, false), evaluate(&expression, true));
            }
        }
    }
}

#[test]
fn retained_tag_side_facts_use_exact_bounds_without_changing_the_word() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(993460));
    let tag = MachineTerm::Variable(Variable(993461));
    let empty = PureFactContext::new();
    let bounded = empty
        .clone()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), tag.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(tag.clone(), MachineTerm::constant(1)),
            true,
        );
    let clear = empty.clone().assume_condition(
        ConditionTerm::uint64_equal(
            MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1)),
            MachineTerm::uint64_constant(0),
        ),
        true,
    );
    for (case, (inner, context)) in [
        (
            MachineTerm::uint64_bitwise_or(word.clone(), MachineTerm::uint64_from_int32(tag)),
            bounded,
        ),
        (
            MachineTerm::uint64_add(word, MachineTerm::uint64_constant(1)),
            clear,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let expression = SpecExpression::BitwiseAnd(
            Box::new(SpecExpression::Value(ProgramValue::UInt64(inner))),
            Box::new(SpecExpression::Value(ProgramValue::UInt64(
                MachineTerm::uint64_constant(!3),
            ))),
        );
        let baseline = evaluate_with_assumptions(&expression, false, &empty);
        assert!(baseline[0].facts.is_empty());
        for legacy in [false, true] {
            let result = evaluate_with_assumptions(&expression, legacy, &context);
            assert_eq!(result[0].value, baseline[0].value);
            assert_eq!(result[0].facts.len(), 1, "case={case}, legacy={legacy}");
        }
        let shared = evaluate_with_assumptions(&expression, false, &context);
        let native = evaluate_with_assumptions(&expression, true, &context);
        assert_eq!(
            boxed_domain(shared[0].facts.iter().next().unwrap().proposition()),
            boxed_domain(native[0].facts.iter().next().unwrap().proposition())
        );
    }
}

#[test]
fn retained_tag_addition_selects_only_a_true_exact_clear_guard() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(993462));
    let low = MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1));
    let expression = SpecExpression::BitwiseAnd(
        Box::new(SpecExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_add(word, MachineTerm::uint64_constant(1)),
        ))),
        Box::new(SpecExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_constant(!3),
        ))),
    );
    for (guard, truth, expected) in [
        (
            ConditionTerm::uint64_equal(MachineTerm::uint64_constant(0), low.clone()),
            true,
            1,
        ),
        (
            ConditionTerm::uint64_equal(low.clone(), MachineTerm::uint64_constant(0)),
            false,
            0,
        ),
        (
            ConditionTerm::uint64_equal(low, MachineTerm::uint64_constant(1)),
            true,
            0,
        ),
    ] {
        let context = PureFactContext::new().assume_condition(guard, truth);
        for legacy in [false, true] {
            let result = evaluate_with_assumptions(&expression, legacy, &context);
            assert_eq!(
                result[0].facts.len(),
                expected,
                "legacy={legacy}, truth={truth}"
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_bitwise.rs");
}

#[test]
fn nested_bitwise_evaluator_retains_values_and_unsupported_widths_decline() {
    for f in FORMATS {
        let _session = VerificationSession::enter();
        let leaf = || Box::new(value(f, 995620));
        let expression = SpecExpression::BitwiseXor(
            Box::new(SpecExpression::BitwiseNot(Box::new(
                SpecExpression::BitwiseAnd(leaf(), leaf()),
            ))),
            Box::new(SpecExpression::BitwiseOr(leaf(), leaf())),
        );
        let mut execution = ExecutionBudget::new();
        let exports = KernelTermExport::machine_export_count();
        let actual = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&ExecutionState::new(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        assert!(matches!(actual[0].value, SpecValue::Shared(_)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(native_results(actual), evaluate(&expression, true));
    }
    for f in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let x = input(f, &MachineTerm::Variable(Variable(995621)), true);
        assert!(bitwise_not(&x, None).is_none());
        for op in [
            MachineBinaryOp::BitwiseAnd,
            MachineBinaryOp::BitwiseOr,
            MachineBinaryOp::BitwiseXor,
        ] {
            assert!(bitwise::apply(op, &x, &x).is_none());
        }
    }
}

#[test]
fn retained_pointer_masks_admit_alignment_without_exporting_operands() {
    let _session = VerificationSession::enter();
    let f = MachineIntegerType::UInt64;
    let pointer = Pointer::symbolic(Variable(995625));
    let address = MachineTerm::PointerAddress(
        Box::new(pointer.clone()),
        crate::kernel::AddressObjectClass::NONE,
    );
    let masked = bitwise::apply(
        MachineBinaryOp::BitwiseAnd,
        &input(f, &address, true),
        &input(f, &MachineTerm::uint64_constant(7), true),
    )
    .unwrap()
    .value;
    let exports = KernelTermExport::machine_export_count();
    let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
        f,
        CompareRelation::Equal,
        [
            MachineOperandView::Shared(&masked),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(0)),
        ],
    );
    assert_eq!(condition.as_pointer_alignment(), Some((&pointer, 8)));
    let context = PureFactContext::new().assume_condition(condition.clone(), true);
    assert_eq!(
        context
            .pointer_alignment_certificate_decision(&pointer, 4)
            .map(|p| p.0),
        Some(true)
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}
