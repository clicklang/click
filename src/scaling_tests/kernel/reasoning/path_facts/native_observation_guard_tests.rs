// Scaling tests of `src/kernel/reasoning/path_facts.rs` (module
// `native_observation_guard_tests`): exact native observation guard queries.
use super::*;

#[test]
fn native_observation_guard_work_is_flat_beside_unrelated_ambient_conditions() {
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let (native, observed) = equalities(ty);
            let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
            for index in 0..size {
                context = context
                    .assume_condition(ConditionTerm::Variable(Variable(913_000 + index)), true);
            }
            context = context.assume_condition(native, false);
            let no_path_facts = ExecutionFacts::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                decide_with_facts(&context, &no_path_facts, &observed)
            });
            assert_eq!(result, Some(false));
            assert!(work < 512, "{ty:?}, {size}: {work}");
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
            "{ty:?}: {samples:?}"
        );
    }
}
