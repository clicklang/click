// Scaling tests of `src/kernel/proof/integer_quotient_shift.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn quotient_shift_work_is_local_and_linear_in_certificate_nodes() {
    let result = goal(2, k());
    let mut premises = vec![le(c(0), x()), le(c(0), k())];
    let (_, single_work) = crate::instrumentation::measure_deterministic_work(|| {
        check(0, &[0, 1], &premises, &result)
    });
    for size in [4, 16, 64, 256] {
        premises.resize(size, le(c(0), c(1)));
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1], &premises, &result)
        });
        checked.unwrap();
        assert_eq!(work, single_work);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerQuotientShift {
                    bounds: vec![0, 1],
                    result: result.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&result, &premises));
        checked.unwrap();
        assert_eq!(work, single_work * size + 1);
    }
}
