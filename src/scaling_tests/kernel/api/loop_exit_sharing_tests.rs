// Scaling tests of `src/kernel/api.rs` (module `loop_exit_sharing_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn checked_loop_exit_copies_share_their_fact_storage() {
    for count in [4usize, 64, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = vec![Proposition::ConditionIs(ConditionTerm::Constant(true), true); count];
        let state = CState::new();
        let (break_exit, break_work) = crate::instrumentation::measure_deterministic_work(|| {
            CLoopBreakExit::new(state.clone(), facts.clone())
        });
        let (final_exit, final_work) = crate::instrumentation::measure_deterministic_work(|| {
            CLoopFinalExitCandidate::new(state.clone(), facts.clone())
        });
        assert!(break_work >= count && break_work <= count * 4 + 32);
        assert!(final_work >= count && final_work <= count * 4 + 32);
        let jump_exit = final_exit.clone().with_jump_target(CControlTargetId(2));
        for _ in 0..16 {
            let copied_break = break_exit.clone();
            let copied_final = final_exit.clone();
            assert!(std::ptr::eq(
                break_exit.pure_facts(),
                copied_break.pure_facts()
            ));
            assert!(std::ptr::eq(
                final_exit.pure_facts(),
                copied_final.pure_facts()
            ));
            assert_eq!(copied_break.pure_facts(), facts);
            assert_eq!(copied_final.pure_facts(), facts);
            let copied_jump = jump_exit.clone();
            assert_eq!(copied_jump.jump_target(), Some(CControlTargetId(2)));
            assert!(std::ptr::eq(
                jump_exit.pure_facts(),
                copied_jump.pure_facts()
            ));
        }
    }
}
