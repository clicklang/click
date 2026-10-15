// Scaling tests of `src/kernel/tests/wide_comparison_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_comparison_queries_ignore_unrelated_ambient_facts() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for operator in OPERATORS {
            let expression = symbolic(operator, ty);
            // Exercise the second indexed query rather than the direct key.
            let guard = condition(complement(operator), ty);
            let mut samples = Vec::new();
            for size in [16, 64, 256, 1024] {
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context
                        .assume_condition(ConditionTerm::Variable(Variable(167_000 + i)), true);
                }
                context = context.assume_condition(guard.clone(), false);
                let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                    paths(&expression, &context)
                });
                assert_eq!(output.len(), 1);
                assert_eq!(output[0].outcome, CExpressionOutcome::Value(int32(1)));
                assert!(work < 4096, "{size}: {work}");
                samples.push(work);
            }
            assert!(
                samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 128,
                "{samples:?}"
            );
        }
    }
}

#[test]
fn wide_comparison_work_scales_with_explicit_operations() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for operator in OPERATORS {
            let expression = symbolic(operator, ty);
            let context = PureFactContext::new();
            let samples = [2usize, 8, 32, 128].map(|size| {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        assert_eq!(paths(&expression, &context).len(), 2);
                    }
                });
                assert!(work <= 8192 * size, "{size}: {work}");
                work
            });
            for pair in samples.windows(2) {
                assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
            }
        }
    }
}
