use super::*;

#[test]
fn publishing_one_closed_claim_ignores_other_goals_and_facts() {
    for count in [16_usize, 64, 256, 512] {
        for unrelated in [0_usize, 256] {
            let (_, root) = fixture();
            let branch = root
                .state()
                .open_branches()
                .get(root.focused_branch())
                .unwrap();
            let crate::kernel::proof::ProofObligation::FunctionOutcome(goal) = &branch.obligation
            else {
                unreachable!()
            };
            let mut goal = goal.clone();
            goal.claims = Some(OutcomeClaimGoals::open(
                (0..count).map(|index| {
                    (
                        FunctionContractClaimKey::Ensure(index),
                        Some(FunctionContractClaimTarget::EnsureProposition(index)),
                    )
                }),
                false,
            ));
            let mut facts = branch.state.facts.clone();
            for index in 0..unrelated {
                facts = facts.with_kernel_checked_fact(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let root = root
                .replace_focused_obligation_and_facts(
                    crate::kernel::proof::ProofObligation::FunctionOutcome(goal),
                    facts,
                )
                .unwrap_or_else(|_| panic!("the outcome remains open"));
            let closed = close_claim(&root);
            let (((), work), indexed) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..count {
                        assert!(
                            closed
                                .published_contract_claim(&FunctionContractClaimKey::Ensure(0))
                                .is_some()
                        );
                        assert!(
                            closed
                                .published_contract_claim(&FunctionContractClaimKey::Ensure(
                                    count - 1
                                ))
                                .is_none()
                        );
                    }
                })
            });
            assert!(
                work <= 4 * count,
                "{count} goals, {unrelated} facts: {work} work"
            );
            assert!(
                indexed <= 32 * count * (count.ilog2() as usize + 1),
                "{count} goals, {unrelated} facts: {indexed} index visits"
            );
        }
    }
}

#[test]
fn publication_and_reopening_do_not_walk_shared_result_operands() {
    use crate::kernel::{
        ExecutionValue, KernelTerm, KernelTermExport, KernelType, MachineBinaryOp,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let (execution, _) = fixture();
    let seed = execution.published_outcome(0);
    let mut previous = None;
    for depth in [8, 32, 128] {
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996910));
        let mut root = atom.clone();
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let exports = KernelTermExport::machine_export_count();
        let (opened, work) = crate::instrumentation::measure_deterministic_work(|| {
            publish_result(seed, value.clone(), false)
                .open_core()
                .unwrap()
        });
        assert_eq!(opened.result.shared(), Some(&root));
        assert_eq!(opened.result, value);
        assert!(opened.result.same_native_value(&value));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "publication must not traverse the return expression"
            );
        }
        previous = Some(work);
    }
}
