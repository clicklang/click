use super::*;
use crate::kernel::VerificationSession;

const FORMATS: [MachineIntegerType; 4] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
];
const OPS: [MachineBinaryOp; 3] = [
    MachineBinaryOp::Add,
    MachineBinaryOp::Subtract,
    MachineBinaryOp::Multiply,
];

fn input(value: &ProgramValue, shared: bool) -> SpecValue {
    if shared {
        let root =
            KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()));
        root.into()
    } else {
        value.clone().into()
    }
}
fn expression(op: MachineBinaryOp, a: SpecExpression, b: SpecExpression) -> SpecExpression {
    match op {
        MachineBinaryOp::Add => SpecExpression::Add(Box::new(a), Box::new(b)),
        MachineBinaryOp::Subtract => SpecExpression::Subtract(Box::new(a), Box::new(b)),
        MachineBinaryOp::Multiply => SpecExpression::Multiply(Box::new(a), Box::new(b)),
        _ => unreachable!(),
    }
}

#[test]
fn annotated_narrow_results_match_native_modular_arithmetic() {
    let _session = VerificationSession::enter();
    for format in FORMATS {
        let (low, high) = format.format().bounds();
        let mut operands = vec![
            format.value_from_term(MachineTerm::Variable(Variable(995460))),
            format.value_from_term(MachineTerm::opaque_conversion(
                "narrow_operand",
                MachineTerm::Variable(Variable(995461)),
            )),
        ];
        for n in [low.clone(), high.clone(), 0.into(), 1.into()] {
            operands.push(format.value_from_term(
                crate::kernel::machine_integer::range::constant_word(format, &n).unwrap(),
            ));
            operands.push(ProgramValue::Int32(
                crate::kernel::machine_integer::range::constant_word(MachineIntegerType::Int32, &n)
                    .unwrap(),
            ));
        }
        for op in OPS {
            for left in &operands {
                for right in &operands {
                    let expected =
                        crate::kernel::eval::native_narrow_binary(format, op, left, right).unwrap();
                    for (l, r) in [(false, false), (true, false), (false, true), (true, true)] {
                        let left = input(left, l);
                        let right = input(right, r);
                        let exports = KernelTermExport::machine_export_count();
                        let result = narrow::apply(format, op, &left, &right).unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert!(result.obligations.is_empty());
                        assert_eq!(
                            SpecValue::Shared(result.value).into_native(),
                            expected,
                            "{format:?} {op:?}"
                        );
                    }
                }
            }
        }
        let native =
            SpecValue::Native(format.value_from_term(MachineTerm::Variable(Variable(995462))));
        for n in [low - 1u8, high + 1u8] {
            let outside = ProgramValue::Int32(
                crate::kernel::machine_integer::range::constant_word(MachineIntegerType::Int32, &n)
                    .unwrap(),
            )
            .into();
            assert!(narrow::apply(format, MachineBinaryOp::Add, &native, &outside).is_none());
        }
        let different = SpecValue::Native(ProgramValue::Int32(MachineTerm::Variable(Variable(995463))));
        assert!(narrow::apply(format, MachineBinaryOp::Add, &native, &different).is_none());
        assert!(narrow::apply(format, MachineBinaryOp::Divide, &native, &native).is_none());
    }
}

#[test]
fn annotated_narrow_evaluator_retains_nested_results() {
    for format in FORMATS {
        for op in OPS {
            let leaf = SpecExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(995464))),
            );
            let inner = SpecExpression::NarrowArithmetic(
                Box::new(expression(op, leaf.clone(), leaf.clone())),
                format,
            );
            let outer =
                SpecExpression::NarrowArithmetic(Box::new(expression(op, inner, leaf)), format);
            let _session = VerificationSession::enter();
            let mut execution = ExecutionBudget::new();
            let exports = KernelTermExport::machine_export_count();
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::unbound(&ExecutionState::new(), None),
                &outer,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(paths.len(), 1);
            assert!(matches!(paths[0].value, SpecValue::Shared(_)));
            assert_eq!(native_results(paths), evaluate(&outer, true));
        }
    }
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_narrow.rs");
}
