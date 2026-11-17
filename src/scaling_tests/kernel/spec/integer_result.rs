use super::*;
use crate::kernel::VerificationSession;

#[test]
fn integer_result_storage_keeps_growing_shared_dags_and_constant_handoffs() {
    let samples = [4, 16, 64, 256].map(|size| {
        let _session = VerificationSession::enter();
        let mut source: SharedIntegerTerm = IntegerTerm::var(Variable(1009710)).into();
        for _ in 0..size {
            source = IntegerTerm::Add(source.clone(), source).into();
        }
        let weak = source.downgrade();
        let (value, cold) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerResult::from(source.clone())
        });
        drop(source);
        assert!(weak.upgrade().is_none(), "size={size}");
        let root = value.clone().into_kernel();
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                assert_eq!(value.clone().into_kernel(), root);
            }
        });
        assert_eq!(warm, 0, "size={size}");
        assert!(!root.has_cached_native_argument());
        (size, cold)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn integer_result_nested_conditionals_do_not_reexport_prefixes() {
    let samples = [8, 32, 128].map(|size| {
        let _session = VerificationSession::enter();
        let mut expression = SpecIntegerExpression::Term(IntegerTerm::var(Variable(1009720)));
        for index in 0..size {
            expression = SpecIntegerExpression::If {
                condition: Box::new(SpecProposition::IntegerComparison {
                    left: SpecIntegerExpression::Term(IntegerTerm::var(Variable(
                        1009730 + index as u64,
                    ))),
                    operator: IntegerComparisonOperator::LessThan,
                    right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                }),
                then_branch: Box::new(expression),
                else_branch: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
            };
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_integer_expression_paths_in(
                SpecScope::unbound(&ExecutionState::new(), None),
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        (size, work)
    });
    eprintln!("Integer result conditional work: {samples:?}");
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn integer_result_fold_assembly_does_not_export_growing_bodies() {
    let samples = [8, 32, 128].map(|size| {
        let _session = VerificationSession::enter();
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        };
        let initial = IntegerResult::from(IntegerTerm::constant_i64(0));
        let mut body = IntegerResult::from(IntegerTerm::var(Variable(1009950)));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for depth in 0..size {
                let old = body.clone().into_kernel();
                body = IntegerResult::range_fold(
                    index.clone(),
                    initial.clone(),
                    Variable(1010000 + 2 * depth as u64),
                    Variable(1010001 + 2 * depth as u64),
                    body,
                );
                assert_eq!(body.clone().into_kernel().children()[3], old);
            }
        });
        (size, work)
    });
    eprintln!("Integer result fold body work: {samples:?}");
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
