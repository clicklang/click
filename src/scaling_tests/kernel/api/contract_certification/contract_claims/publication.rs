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
