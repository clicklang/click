use super::*;
use crate::kernel::{KernelFoldIndex, KernelIntegerOperator, KernelTermExport};

#[test]
fn common_fold_scope_readers_visit_shared_bodies_once_without_exports() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(970000 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let free = KernelTerm::variable(KernelType::Integer, Variable(971000));
            let mut body = free.clone();
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let fold = KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(971001),
                Variable(971002),
                [free.clone(), free.clone(), free.clone(), body],
            )
            .unwrap();
            let exports = KernelTermExport::machine_export_count();
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut variables = BTreeSet::new();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    collect_fold_variables(&fold, mode, &mut variables)
                });
                assert!(
                    work <= 8 * (size + 1) + 64,
                    "mode={mode:?}, size={size}, unrelated={unrelated}, work={work}"
                );
                match mode {
                    FoldVariableRead::IntegerFree | FoldVariableRead::ExpressionFree => {
                        assert_eq!(variables, BTreeSet::from([Variable(971000)]))
                    }
                    FoldVariableRead::IntegerBinders => assert_eq!(
                        variables,
                        BTreeSet::from([Variable(971001), Variable(971002)])
                    ),
                    _ => assert!(variables.is_empty()),
                }
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn common_fold_scope_summaries_share_growing_variable_sets_between_initial_and_body() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let mut body = KernelTerm::variable(KernelType::Integer, Variable(973000));
        for index in 1..size {
            body = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![
                    body,
                    KernelTerm::variable(KernelType::Integer, Variable(973000 + index)),
                ],
            )
            .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        // The initial value is outside both binders even though it is the
        // exact same DAG root as the body. Its variables must remain free.
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            Variable(973000),
            Variable(973001),
            [zero.clone(), zero, body.clone(), body],
        )
        .unwrap();
        let mut variables = BTreeSet::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_fold_variables(&fold, FoldVariableRead::IntegerFree, &mut variables)
        });
        assert_eq!(variables.len(), size as usize);
        assert!(variables.contains(&Variable(973000)));
        assert!(variables.contains(&Variable(973001)));
        costs.push(work);
    }
    for pair in costs.windows(2) {
        assert!(pair[1] <= 6 * pair[0] + 32, "work={costs:?}");
    }
}
