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
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert!(
                work <= 16 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn shared_unsigned_children_are_not_reimported_or_expanded_during_construction() {
    for size in [16, 64, 256] {
        let mut term = KernelTerm::variable(KernelType::C(CType::UInt64), Variable(982000));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                term = KernelTerm::unsigned_binary(
                    MachineIntegerType::UInt64,
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
