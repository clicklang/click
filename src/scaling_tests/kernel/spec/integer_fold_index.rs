use super::*;
use crate::kernel::VerificationSession;

#[test]
fn deferred_integer_endpoint_handoffs_ignore_bound_dag_size() {
    let samples = [4, 16, 64, 256].map(|size| {
        let _session = VerificationSession::enter();
        let variable = Variable(1011120);
        let mut root = KernelTerm::variable(KernelType::Integer, Variable(1011121));
        for _ in 0..size {
            root =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![root.clone(), root])
                    .unwrap();
        }
        let index = SpecIntegerRangeFoldIndex::Integer {
            start: Box::new(SpecIntegerExpression::Term(IntegerTerm::var(variable))),
            end: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(2))),
        };
        let mut execution_budget = ExecutionBudget::default();
        let mut evaluation = SpecEvaluation::logical(&mut execution_budget);
        evaluation
            .integer_bindings
            .insert(variable, IntegerResult::from_kernel(root.clone()));
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_integer_range_fold_indices_in(
                SpecScope::unbound(&ExecutionState::new(), None),
                &index,
                &PureFactContext::new(),
                &mut evaluation,
            )
            .unwrap()
        });
        let [(index, _, _)] = paths.as_slice() else {
            panic!("one index path")
        };
        assert_eq!(index.bounds[0], root);
        let ((), warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                let value = evaluation
                    .bound_integer_term(&IntegerTerm::var(variable))
                    .unwrap();
                assert_eq!(value.into_kernel(), root);
                assert_eq!(index.clone().bounds[0], root);
            }
        });
        assert!(work > 0 && warm > 0);
        (size, work, warm)
    });
    for (_, work, warm) in samples {
        assert_eq!(work, samples[0].1, "{samples:?}");
        assert_eq!(warm, samples[0].2, "{samples:?}");
    }
}
