use super::mixed_width_tests::native_integer;
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
const OPS: [MachineBinaryOp; 2] = [MachineBinaryOp::ShiftLeft, MachineBinaryOp::ShiftRight];
fn input(format: MachineIntegerType, value: &MachineTerm, shared: bool) -> SpecValue {
    if shared {
        KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(value)).into()
    } else {
        format.value_from_term(value.clone()).into()
    }
}

// Compare the guards as mathematical relations, folding polarity and native
// machine comparisons while materializing operands only in this oracle.
fn native_domain(value: &Proposition) -> Proposition {
    use ConditionTerm as C;
    match value {
        Proposition::And(a, b) => {
            Proposition::And(Box::new(native_domain(a)), Box::new(native_domain(b)))
        }
        Proposition::ConditionIs(condition, truth) => {
            if matches!(condition, C::Compare { .. }) {
                let lifted =
                    crate::kernel::machine_integer::comparison::comparison_view(condition, *truth)
                        .unwrap()
                        .integer_proposition();
                return native_domain(&lifted);
            }
            let (a, b, less, negated) = match condition {
                C::IntegerLessThan(a, b) => (a, b, true, !truth),
                C::IntegerGreaterThan(a, b) => (b, a, true, !truth),
                C::IntegerLessEqual(a, b) => (a, b, false, !truth),
                C::IntegerGreaterEqual(a, b) => (b, a, false, !truth),
                _ => return value.clone(),
            };
            let (a, b) = (native_integer(a), native_integer(b));
            let (a, b, less) = if negated { (b, a, !less) } else { (a, b, less) };
            Proposition::ConditionIs(
                if less {
                    C::integer_less_than(a, b)
                } else {
                    C::integer_less_equal(a, b)
                },
                true,
            )
        }
        _ => value.clone(),
    }
}

#[test]
fn c_shifts_match_native_terms_and_independently_typed_count_domains() {
    let _session = VerificationSession::enter();
    let mut execution = ExecutionBudget::new();
    let budget = SpecEvaluation::logical(&mut execution);
    for a in FORMATS {
        for b in FORMATS {
            let mut counts = vec![
                MachineTerm::Variable(Variable(995471)),
                MachineTerm::opaque_conversion(
                    "shift_count",
                    MachineTerm::Variable(Variable(995472)),
                ),
            ];
            for n in [-1i64, 0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 1 << 32] {
                if let Some(word) =
                    crate::kernel::machine_integer::range::constant_word(b, &n.into())
                {
                    counts.push(word);
                }
            }
            let (low, high) = a.format().bounds();
            let mut operands = vec![
                MachineTerm::Variable(Variable(995473)),
                MachineTerm::opaque_conversion(
                    "shift_value",
                    MachineTerm::Variable(Variable(995474)),
                ),
            ];
            for n in [low, high, 0.into(), 1.into()] {
                operands.push(crate::kernel::machine_integer::range::constant_word(a, &n).unwrap());
            }
            for op in OPS {
                for left in &operands {
                    for right in &counts {
                        let mut expected = crate::kernel::eval::apply_spec_machine_arithmetic(
                            op,
                            SpecDivision::Total,
                            &a.value_from_term(left.clone()),
                            &b.value_from_term(right.clone()),
                            &ExecutionFacts::default(),
                            &[],
                        )
                        .unwrap();
                        for o in &mut expected.obligations {
                            o.proposition = native_domain(o.proposition());
                        }
                        let CExpressionOutcome::Value(expected_value) = expected.outcome else {
                            panic!()
                        };
                        for (l, r) in [(false, false), (true, false), (false, true), (true, true)] {
                            let left = input(a, left, l);
                            let right = input(b, right, r);
                            let exports = KernelTermExport::machine_export_count();
                            let mut result =
                                apply_values(Some(op), &left, &right, &budget).unwrap();
                            assert_eq!(KernelTermExport::machine_export_count(), exports);
                            let (crate::kernel::integer_c_value!(expected_word)) = &expected_value
                            else {
                                panic!()
                            };
                            let result_format =
                                MachineIntegerType::from_c_type(expected_value.c_type()).unwrap();
                            if let Some(imported) = KernelTermImport::default()
                                .machine_arithmetic(result_format, expected_word)
                            {
                                assert_eq!(
                                    result.value, imported,
                                    "native shared identity {a:?}/{b:?} {op:?}"
                                );
                            }
                            assert_eq!(
                                SpecValue::Shared(result.value).into_native(),
                                expected_value,
                                "{a:?}/{b:?} {op:?}"
                            );
                            for o in &mut result.obligations {
                                o.proposition = native_domain(o.proposition());
                            }
                            assert_eq!(
                                result.obligations, expected.obligations,
                                "domain {a:?}/{b:?} {op:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn c_shift_evaluator_retains_wide_count_refusals() {
    for op in OPS {
        let left = Box::new(SpecExpression::Value(CValue::Int32(MachineTerm::Variable(
            Variable(995475),
        ))));
        let right = Box::new(SpecExpression::Value(CValue::UInt64(
            MachineTerm::uint64_constant(1 << 32),
        )));
        let expression = if op == MachineBinaryOp::ShiftLeft {
            SpecExpression::ShiftLeft(left, right)
        } else {
            SpecExpression::ShiftRight(left, right)
        };
        let normalize = |mut paths: Vec<SpecExpressionPath>| {
            for path in &mut paths {
                for o in &mut path.obligations {
                    o.proposition = native_domain(o.proposition());
                }
            }
            paths
        };
        assert_eq!(
            normalize(evaluate(&expression, false)),
            normalize(evaluate(&expression, true))
        );
        let mut execution = ExecutionBudget::new();
        let budget = SpecEvaluation::logical(&mut execution);
        let result = apply_values(
            Some(op),
            &CValue::Int32(MachineTerm::constant(1)).into(),
            &CValue::UInt64(MachineTerm::uint64_constant(1 << 32)).into(),
            &budget,
        )
        .unwrap();
        assert!(
            result
                .obligations
                .iter()
                .any(|o| !PureFactContext::new().proves_exact(o.proposition()))
        );
    }
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_shifts.rs");
}
