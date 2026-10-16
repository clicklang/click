// Scaling tests of `src/kernel/tests/wide_division_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_division_guard_queries_do_not_scan_unrelated_ambient_facts() {
    for remainder in [false, true] {
        for inequalities in [false, true] {
            let mut samples = Vec::new();
            for size in [16, 64, 256, 1024] {
                // Each size measures a cold verification session. Otherwise
                // later samples can inherit the first sample's term caches.
                let _session = crate::kernel::VerificationSession::enter();
                let (zero, _, _, safe) = guards(MachineIntegerType::Int128);
                let (nonzero, inequality_safe) = inequality_guards(MachineIntegerType::Int128);
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context
                        .assume_condition(ConditionTerm::Variable(Variable(156_000 + i)), true);
                }
                context = if inequalities {
                    context
                        .assume_condition(nonzero.clone(), true)
                        .assume_proposition(inequality_safe.clone())
                } else {
                    context
                        .assume_condition(zero.clone(), false)
                        .assume_proposition(safe.clone())
                };
                let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                    paths(MachineIntegerType::Int128, remainder, &context)
                });
                assert_eq!(output.len(), 1);
                assert!(work < 4096, "{size}: {work}");
                samples.push(work);
            }
            assert!(
                samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
                "{samples:?}"
            );
        }
    }
}

#[test]
fn wide_division_work_scales_with_explicit_operations() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            let mut samples = Vec::new();
            for size in [2usize, 8, 32, 128] {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        assert_eq!(
                            paths(ty, remainder, &PureFactContext::new()).len(),
                            if ty == MachineIntegerType::Int128 {
                                3
                            } else {
                                2
                            }
                        );
                    }
                });
                assert!(work <= 8192 * size, "{size}: {work}");
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
            }
        }
    }
}
