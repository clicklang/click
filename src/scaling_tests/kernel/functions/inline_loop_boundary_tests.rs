// Scaling tests of `src/kernel/functions.rs` (module `inline_loop_boundary_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn symbolic_inline_loop_refusal_work_is_independent_of_unroll_allowance() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for limit in [4usize, 64, 1024] {
        let mut budget = ExecutionBudget::new();
        budget.loop_unrolls = limit;
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            call(int32(Bitvector32Term::Variable(Variable(7))), &mut budget)
        });
        let paths = result.unwrap();
        assert!(matches!(paths.as_slice(), [CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)), ..
        }] if message.contains("drain_to_zero") && message.contains("loop guard cannot be decided at the call site")));
        assert_eq!(budget.loop_unrolls, limit - 1);
        assert!(budget.inline_call_name.is_none());
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
    eprintln!("symbolic inline-loop work at 4/64/1024 unrolls: {samples:?}");
}
