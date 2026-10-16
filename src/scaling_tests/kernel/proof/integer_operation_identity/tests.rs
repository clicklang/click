// Scaling tests of `src/kernel/proof/integer_operation_identity.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_operation_identity_checks_only_explicit_premises_and_scales_with_nodes() {
    let (min, max) = Ty::Int64.format().bounds();
    let (mut premises, goal, _) = inputs(Ty::Int64, true, min, max);
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        premises.resize_with(size, || {
            Proposition::ConditionIs(ConditionTerm::Variable(Variable(171_010)), true)
        });
        let cert = certificate(goal.clone(), vec![0, 1]);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
        "{samples:?}"
    );
    let mut previous = None;
    for size in [2usize, 8, 32, 128] {
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerOperationIdentity {
                    bounds: vec![0, 1],
                    result: goal.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        assert!(work <= 4096 * size, "{size}: {work}");
        if let Some(before) = previous {
            assert!(work <= 4 * before + 64);
        }
        previous = Some(work);
    }
}
