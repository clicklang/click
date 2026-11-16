use super::*;

#[test]
fn local_observation_rules_ignore_unrelated_facts_and_related_bound_buckets() {
    for related in [false, true] {
        let _session = VerificationSession::enter();
        let (observed, exact) = operation(MachineIntegerType::Int64, Operation::Add).unwrap();
        let goal = equality(observed, exact.clone());
        let mut costs = Vec::new();
        for size in [8, 32, 128] {
            let mut premises = Vec::new();
            for i in 0..size {
                premises.push(if related {
                    le(
                        exact.clone(),
                        IntegerTerm::Constant(BigInt::from(i) + (BigInt::from(1) << 64usize)),
                    )
                } else {
                    equality(
                        IntegerTerm::var(Variable(996000 + i)),
                        IntegerTerm::var(Variable(997000 + i)),
                    )
                });
            }
            let missing = ProofFacts::from_ordered(&premises);
            premises.extend(bounds(&exact, MachineIntegerType::Int64));
            let facts = ProofFacts::from_ordered(&premises);
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|p| facts.pure_known_available(p))
            });
            assert!(accepted);
            let (_, miss) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(!known_bridge_leaf(&goal, &|p| missing.pure_known_available(p)));
            });
            costs.push(work + miss);
        }
        assert!(
            costs.windows(2).all(|p| p[1] <= 2 * p[0]),
            "related={related}: {costs:?}"
        );
    }
}

#[test]
fn observation_leaves_keep_growing_arithmetic_and_comparison_dags_shared() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int64;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(995720));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let operand =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap());
        let exact = IntegerTerm::Add(operand.clone().into(), operand.clone().into());
        let operation = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [root.clone(), root.clone()],
        );
        let observed =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, operation).unwrap());
        let guard = KernelTerm::boolean_comparison_raw(
            ty,
            CompareRelation::LessEqual,
            [
                root.clone(),
                KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(995721)),
            ],
        );
        let condition = written_guard(BooleanOperandView::Shared(&guard)).unwrap();
        let conditional = KernelTerm::machine_if_shared(ty, [guard, root.clone(), root]);
        let conditional =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, conditional).unwrap());
        let mut premises = bounds(&exact, ty).to_vec();
        premises.push(Proposition::ConditionIs(condition, true));
        let facts = ProofFacts::from_ordered(&premises);
        let missing = ProofFacts::from_ordered(&[]);
        let operation_goal = equality(observed, exact);
        let conditional_goal = equality(conditional, operand);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..2 {
                assert!(known_bridge_leaf(&operation_goal, &|p| facts.pure_known_available(p)));
                assert!(!known_bridge_leaf(&operation_goal, &|p| missing.pure_known_available(p)));
                assert!(known_bridge_leaf(&conditional_goal, &|p| facts.pure_known_available(p)));
                assert!(!known_bridge_leaf(&conditional_goal, &|p| missing.pure_known_available(p)));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(samples.windows(2).all(|p| p[1] <= 5 * p[0]), "{samples:?}");
}
