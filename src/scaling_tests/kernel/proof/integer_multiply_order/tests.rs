// Scaling tests of `src/kernel/proof/integer_multiply_order.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn selected_premises_and_steps_scale_without_ambient_scans() {
    let a = v(920001);
    let b = v(920002);
    let factor = v(920003);
    let goal = le(p(&a, &factor), p(&b, &factor));
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut premises = vec![le(a.clone(), b.clone()), le(c(0), factor.clone())];
        premises.extend((0..size).map(|i| le(v(930000 + i as u64), c(i as i64))));
        let cert = SpecialArithmeticCertificate {
            nodes: (0..size)
                .map(|_| SpecialArithmeticNode::IntegerMultiplyOrder {
                    bounds: vec![0, 1],
                    result: goal.clone(),
                })
                .collect(),
            conclusion: size - 1,
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
