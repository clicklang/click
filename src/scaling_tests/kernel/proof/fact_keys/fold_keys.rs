use super::*;
use crate::kernel::{KernelFoldIndex, KernelTerm, MachineBinaryOp};

#[test]
fn common_fold_alpha_keys_scale_with_selected_shared_bodies_without_exports() {
    // A fold's four DAGs must not inflate every scalar key in proof state.
    assert!(std::mem::size_of::<AlphaBitvectorKey>() <= 64);
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = |acc| {
            let mut body = KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Legacy(&MachineTerm::Variable(Variable(acc))),
            );
            for _ in 0..size {
                body = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [body.clone(), body],
                );
            }
            let zero = KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
            );
            KernelFold::new(
                KernelFoldIndex::Int32,
                Variable(acc),
                Variable(acc + 1),
                [zero.clone(), zero.clone(), zero, body],
            )
            .unwrap()
        };
        let a = fold(110);
        let b = fold(120);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| alpha_equivalent(&a, &b));
        assert_eq!(result, Some(true));
        assert!(work <= 100 * size + 200, "size={size}, work={work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn retained_integer_fold_keys_scale_without_native_exports() {
    use crate::kernel::proof::{
        OutcomeProofState, ProofBranch, ProofBranchState, ProofObject, ProofObligation,
        PropositionObligation, PureFactStore,
    };

    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = |accumulator| {
            let variable = KernelTerm::variable(KernelType::Integer, Variable(accumulator));
            let mut body = variable.clone();
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }

            let guard = KernelTerm::integer_comparison(
                IntegerComparisonOperator::LessEqual,
                [variable.clone(), body.clone()],
            )
            .unwrap();
            let body = KernelTerm::integer_if_raw([guard, variable, body]);
            let zero = KernelTerm::integer_literal(0.into());
            KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(accumulator),
                Variable(accumulator + 1),
                [zero.clone(), zero.clone(), zero, body],
            )
            .unwrap()
        };
        let root = KernelTerm::integer_comparison(
            IntegerComparisonOperator::Equal,
            [fold(310).into_term(), fold(410).into_term()],
        )
        .unwrap();
        let goal = Proposition::condition_is(
            crate::kernel::StoredConditionTerm::from_root(root.clone()).unwrap(),
            true,
        );
        let samples = [0, 16, 64, 256].map(|unrelated| {
            let facts = PureFactStore::from_ordered(
                &(0..unrelated)
                    .map(|index| Proposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                    })
                    .collect::<Vec<_>>(),
            );
            let proof = TestProof::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(goal.clone(), ())),
                    ProofBranchState {
                        facts,
                        execution: None,
                    },
                ),
            );
            let exports = KernelTermExport::integer_export_count();
            let (closed, work) =
                crate::instrumentation::measure_deterministic_work(|| proof.apply_normalize());
            assert!(closed.is_ok());
            assert!(!root.has_cached_native_argument());
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
        assert!(
            samples[0] <= 40 * size + 200,
            "size={size}, work={samples:?}"
        );
    }
}
