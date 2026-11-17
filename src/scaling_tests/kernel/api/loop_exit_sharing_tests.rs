// Scaling tests of `src/kernel/api.rs` (module `loop_exit_sharing_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn checked_loop_exit_copies_share_their_fact_storage() {
    for count in [4usize, 64, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = vec![Proposition::ConditionIs(ConditionTerm::Constant(true), true); count];
        let state = ExecutionState::new();
        let (break_exit, break_work) = crate::instrumentation::measure_deterministic_work(|| {
            LoopBreakExit::new(state.clone(), facts.clone())
        });
        let (final_exit, final_work) = crate::instrumentation::measure_deterministic_work(|| {
            LoopFinalExitCandidate::new(state.clone(), facts.clone())
        });
        assert!(break_work >= count && break_work <= count * 4 + 32);
        assert!(final_work >= count && final_work <= count * 4 + 32);
        let jump_exit = final_exit.clone().with_jump_target(ControlTargetId(2));
        for _ in 0..16 {
            let copied_break = break_exit.clone();
            let copied_final = final_exit.clone();
            let (LoopExitFacts::Explicit(original), LoopExitFacts::Explicit(copied)) =
                (break_exit.pure_facts(), copied_break.pure_facts())
            else {
                unreachable!()
            };
            assert!(Arc::ptr_eq(original, copied));
            let (LoopExitFacts::Explicit(original), LoopExitFacts::Explicit(copied)) =
                (final_exit.pure_facts(), copied_final.pure_facts())
            else {
                unreachable!()
            };
            assert!(Arc::ptr_eq(original, copied));
            assert!(copied_break.pure_facts().iter().eq(facts.iter()));
            assert!(copied_final.pure_facts().iter().eq(facts.iter()));
            let copied_jump = jump_exit.clone();
            assert_eq!(copied_jump.jump_target(), Some(ControlTargetId(2)));
            let (LoopExitFacts::Explicit(original), LoopExitFacts::Explicit(copied)) =
                (jump_exit.pure_facts(), copied_jump.pure_facts())
            else {
                unreachable!()
            };
            assert!(Arc::ptr_eq(original, copied));
        }
    }
}

#[test]
fn checked_loop_exit_retains_the_store_and_publishes_shared_propositions() {
    use crate::kernel::proof::{PropositionSource, PureFactStore};
    for size in [32, 128, 512] {
        let source = (0..size)
            .map(|index| Proposition::Predicate {
                name: format!("exit_{index}"),
                arguments: Vec::new(),
            })
            .collect::<Vec<_>>();
        let root = PureFactStore::from_ordered(&source);
        let _ = crate::kernel::proof::take_fact_entry_counts();
        let (exit, work) = crate::instrumentation::measure_deterministic_work(|| {
            LoopBreakExit::from_store(ExecutionState::new(), &root)
        });
        assert!(work <= 32, "size {size}: {work}");
        assert_eq!(crate::kernel::proof::take_fact_entry_counts(), (0, 0));
        assert!(
            exit.pure_facts()
                .fact_store()
                .shares_exact_index_with(&root)
        );
        let published = exit.pure_facts().certified_facts();
        for (stored, fact) in root.shared_presented_propositions().zip(published.iter()) {
            assert!(Arc::ptr_eq(&stored, &fact.shared_proposition()));
            assert!(fact.is_certified());
        }
        assert!(
            exit.pure_facts()
                .context_with(root.assumptions())
                .shares_fact_storage_with(root.assumptions())
        );
    }
}
