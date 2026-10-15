// Scaling tests of `src/kernel/loops.rs` (module `loop_exit_shared_fact_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn merged_exit_equations_have_output_sized_work() {
    let mut work = Vec::new();
    for count in [4usize, 8, 16, 32] {
        let fresh = CValue::Int32(Bitvector32Term::Variable(Variable(100)));
        let (facts, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let exits = (0..count)
                .map(|value| {
                    let mut restatement = LoopExitRestatement::default();
                    restatement.pin(
                        &fresh,
                        &CValue::Int32(Bitvector32Term::Constant(value as u32)),
                    );
                    restatement.restate(
                        vec![ExecutionPureFact::new(fact(1, value as i64))].into(),
                        Vec::new(),
                        crate::kernel::loans::empty_checked_loan_evidence_sequence(),
                    )
                })
                .collect();
            join_loop_exit_paths(exits).unwrap().0
        });
        assert_eq!(
            facts.len(),
            2,
            "one historical and one successor disjunction"
        );
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[1] > pair[0]), "{work:?}");
    assert!(
        work.windows(2).all(|pair| pair[1] <= 3 * pair[0] + 32),
        "{work:?}"
    );
}
