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
const OPS: [MachineBinaryOp; 5] = [
    MachineBinaryOp::Add,
    MachineBinaryOp::Subtract,
    MachineBinaryOp::Multiply,
    MachineBinaryOp::Divide,
    MachineBinaryOp::Remainder,
];

fn native(format: MachineIntegerType, term: MachineTerm) -> CValue {
    match format {
        MachineIntegerType::Int8 => CValue::Int8(term),
        MachineIntegerType::UInt8 => CValue::UInt8(term),
        MachineIntegerType::Int16 => CValue::Int16(term),
        MachineIntegerType::UInt16 => CValue::UInt16(term),
        _ => wrap(format, term),
    }
}
fn operand(format: MachineIntegerType, value: &MachineTerm, shared: bool) -> SpecValue {
    if shared {
        KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(value)).into()
    } else {
        native(format, value.clone()).into()
    }
}

// Materialize only in the oracle: shared observations deliberately keep an
// opaque operand behind a retained cast rather than a boxed native tree.
pub(super) fn native_integer(value: &SharedIntegerTerm) -> IntegerTerm {
    match value.as_ref() {
        IntegerTerm::Machine(m) => IntegerTerm::from_machine(m.ty(), m.value().clone()).unwrap(),
        IntegerTerm::Add(a, b) => IntegerTerm::add(native_integer(a), native_integer(b)),
        IntegerTerm::Subtract(a, b) => IntegerTerm::subtract(native_integer(a), native_integer(b)),
        IntegerTerm::Multiply(a, b) => IntegerTerm::multiply(native_integer(a), native_integer(b)),
        value => value.clone(),
    }
}
pub(super) fn native_domain(value: &Proposition) -> Proposition {
    match value {
        Proposition::And(a, b) => {
            Proposition::And(Box::new(native_domain(a)), Box::new(native_domain(b)))
        }
        Proposition::Or(a, b) => {
            Proposition::Or(Box::new(native_domain(a)), Box::new(native_domain(b)))
        }
        Proposition::ConditionIs(condition, truth) => {
            let condition = match condition {
                ConditionTerm::IntegerLessEqual(a, b) => {
                    ConditionTerm::integer_less_equal(native_integer(a), native_integer(b))
                }
                ConditionTerm::IntegerGreaterEqual(a, b) => {
                    ConditionTerm::integer_greater_equal(native_integer(a), native_integer(b))
                }
                _ => return boxed_domain(value),
            };
            Proposition::ConditionIs(condition, *truth)
        }
        _ => value.clone(),
    }
}

#[test]
fn mixed_arithmetic_matches_native_terms_and_domains() {
    let _session = VerificationSession::enter();
    for a in FORMATS {
        for b in FORMATS {
            for op in OPS {
                for defined in [false, true] {
                    let mut execution = ExecutionBudget::new();
                    let mut budget = SpecEvaluation::logical(&mut execution);
                    budget.c_definedness = defined;
                    for case in 0..4 {
                        let term = |format: MachineIntegerType, id| match case {
                            0 => MachineTerm::Variable(Variable(id)),
                            1 => MachineTerm::opaque_conversion(
                                "mixed_operand",
                                MachineTerm::Variable(Variable(id)),
                            ),
                            2 => crate::kernel::machine_integer::range::constant_word(
                                format,
                                &0.into(),
                            )
                            .unwrap(),
                            _ => {
                                let high = num_bigint::BigInt::from(1u8)
                                    << (format.format().bits()
                                        - u32::from(format.format().is_signed()))
                                        as usize;
                                let n = if format.format().is_signed() {
                                    -high
                                } else {
                                    high - 1u8
                                };
                                crate::kernel::machine_integer::range::constant_word(format, &n)
                                    .unwrap()
                            }
                        };
                        let left = term(a, 995450);
                        let right = term(b, 995451);
                        let mut expected = crate::kernel::eval::apply_spec_machine_arithmetic(
                            op,
                            if defined {
                                SpecDivision::CDefined
                            } else {
                                SpecDivision::Total
                            },
                            &native(a, left.clone()),
                            &native(b, right.clone()),
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
                        for (l_shared, r_shared) in
                            [(false, false), (true, false), (false, true), (true, true)]
                        {
                            let l = operand(a, &left, l_shared);
                            let r = operand(b, &right, r_shared);
                            let exports = KernelTermExport::machine_export_count();
                            let result = apply_values(Some(op), &l, &r, &budget).unwrap();
                            assert_eq!(KernelTermExport::machine_export_count(), exports);
                            assert_eq!(
                                SpecValue::Shared(result.value).into_native(),
                                expected_value,
                                "{a:?}/{b:?} {op:?} case={case}"
                            );
                            let obligations: Vec<_> = result
                                .obligations
                                .into_iter()
                                .map(|mut o| {
                                    o.proposition = native_domain(o.proposition());
                                    o
                                })
                                .collect();
                            assert_eq!(
                                obligations, expected.obligations,
                                "domain: {a:?}/{b:?} {op:?} case={case} defined={defined}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn mixed_arithmetic_evaluator_preserves_nested_results_and_refusals() {
    for (a, b) in [
        (MachineIntegerType::Int8, MachineIntegerType::UInt16),
        (MachineIntegerType::UInt32, MachineIntegerType::Int64),
        (MachineIntegerType::Int32, MachineIntegerType::UInt64),
    ] {
        let leaf = |format, id| {
            Box::new(SpecExpression::Value(native(
                format,
                MachineTerm::Variable(Variable(id)),
            )))
        };
        let expression = SpecExpression::Add(
            Box::new(SpecExpression::Multiply(leaf(a, 995452), leaf(b, 995453))),
            leaf(a, 995454),
        );
        let normalize = |mut paths: Vec<SpecExpressionPath>| {
            for p in &mut paths {
                for o in &mut p.obligations {
                    o.proposition = native_domain(o.proposition());
                }
            }
            paths
        };
        assert_eq!(
            normalize(evaluate(&expression, false)),
            normalize(evaluate(&expression, true))
        );
    }
    let mut execution = ExecutionBudget::new();
    let budget = SpecEvaluation::logical(&mut execution);
    let left = SpecValue::Native(CValue::Int32(MachineTerm::Variable(Variable(995455))));
    let right = SpecValue::Native(CValue::UInt64(MachineTerm::Variable(Variable(995456))));
    assert!(apply_values(Some(MachineBinaryOp::ShiftLeft), &left, &right, &budget).is_some());
    let wide = SpecValue::Native(CValue::Int128(MachineTerm::Variable(Variable(995457))));
    assert!(apply_values(Some(MachineBinaryOp::Add), &wide, &right, &budget).is_none());
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_mixed_width.rs");
}
