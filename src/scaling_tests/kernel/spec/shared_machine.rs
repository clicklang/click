use super::*;

#[test]
fn unsigned_production_and_single_export_are_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(980000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut expression =
                SpecExpression::Value(CValue::UInt64(Bitvector32Term::Variable(Variable(981000))));
            for _ in 0..size {
                expression = SpecExpression::Add(
                    Box::new(expression),
                    Box::new(SpecExpression::Value(CValue::UInt64(
                        Bitvector32Term::UInt64Constant(1),
                    ))),
                );
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                let term = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                    .unwrap()
                    .unwrap();
                KernelTermExport::default().argument(&term.value).unwrap()
            });
            assert!(
                work <= 16 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn shared_arithmetic_children_are_not_reimported_or_expanded_during_construction() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for size in [16, 64, 256] {
            let mut term = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982000));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Multiply,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    assert_eq!(term.children()[0], term.children()[1]);
                }
            });
            assert!(work <= 4 * size, "size={size}, work={work}");
        }
    }
}

#[test]
fn signed_available_operand_production_is_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(984000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut operand = Bitvector32Term::Variable(Variable(985000));
            for _ in 0..size {
                operand = Bitvector32Term::Binary {
                    format: MachineIntegerType::Int64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(operand),
                    right: Box::new(Bitvector32Term::Int64Constant(1)),
                };
            }
            let expression = SpecExpression::Add(
                Box::new(SpecExpression::Value(CValue::Int64(operand))),
                Box::new(SpecExpression::Value(CValue::Int64(
                    Bitvector32Term::Int64Constant(1),
                ))),
            );
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                let prepared = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                    .unwrap()
                    .unwrap();
                assert_eq!(prepared.obligations.len(), 1);
                KernelTermExport::default()
                    .argument(&prepared.value)
                    .unwrap()
            });
            assert!(
                work <= 32 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn nested_signed_preparation_rejects_before_importing_available_operands() {
    for size in [16, 64, 256] {
        let leaf =
            || SpecExpression::Value(CValue::Int64(Bitvector32Term::Variable(Variable(986000))));
        let mut expression = leaf();
        for _ in 0..size {
            expression = SpecExpression::Add(Box::new(expression), Box::new(leaf()));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            prepare(&expression, &mut SpecEvaluation::logical(&mut execution)).unwrap()
        });
        assert!(result.is_none());
        // The unsigned selection stops on its first signed value. No imports,
        // domains or growing boxed-prefix exports have happened.
        assert_eq!(work, 2 * (size + 1));
    }
}

#[test]
fn a_deferred_operand_rejects_one_preparation_without_importing_prefixes() {
    for size in [16, 64, 256] {
        let mut expression =
            SpecExpression::Value(CValue::UInt64(Bitvector32Term::Variable(Variable(983000))));
        for _ in 0..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(CValue::UInt64(
                    Bitvector32Term::UInt64Constant(1),
                ))),
            );
        }
        let expression = SpecExpression::Add(
            Box::new(expression),
            Box::new(SpecExpression::CExpression(CExpression::Variable(
                "later".into(),
            ))),
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            prepare(&expression, &mut SpecEvaluation::logical(&mut execution)).unwrap()
        });
        assert!(result.is_none());
        // One visit and one interruption checkpoint per source node.
        assert_eq!(work, 2 * (2 * size + 3));
    }
}
