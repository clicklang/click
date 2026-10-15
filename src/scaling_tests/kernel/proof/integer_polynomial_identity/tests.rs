// Scaling tests of `src/kernel/proof/integer_polynomial_identity.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn polynomial_identity_is_bounded_and_independent_of_unused_premises() {
    let goal = successor();
    let (_, single_work) =
        crate::instrumentation::measure_deterministic_work(|| check(0, &[], &[], &goal));
    for size in [1, 4, 16, 64] {
        let premises = vec![goal.clone(); size];
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[], &premises, &goal));
        result.unwrap();
        assert_eq!(work, single_work);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerPolynomialIdentity {
                    bounds: vec![],
                    result: goal.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        assert_eq!(work, single_work * size + 1);
    }
    let mut power = x();
    for _ in 1..17 {
        power = IntegerTerm::multiply(power, x());
    }
    assert_eq!(
        check(0, &[], &[], &eq(power.clone(), power)),
        Err(Error::IntegerPolynomialLimitExceeded)
    );
    let huge = IntegerTerm::constant(BigInt::one() << 4097usize);
    assert_eq!(
        check(0, &[], &[], &eq(huge.clone(), huge)),
        Err(Error::IntegerPolynomialLimitExceeded)
    );
    let mut many = x();
    for index in 0..300 {
        many = IntegerTerm::add(many, IntegerTerm::var(Variable(185_000 + index)));
    }
    assert_eq!(
        check(0, &[], &[], &eq(many.clone(), many)),
        Err(Error::IntegerPolynomialLimitExceeded)
    );
    // Shared squaring cannot expand into an unbounded polynomial.
    let mut exponential = IntegerTerm::add(x(), c(1));
    for _ in 0..10 {
        exponential = IntegerTerm::multiply(exponential.clone(), exponential);
    }
    assert_eq!(
        check(0, &[], &[], &eq(exponential.clone(), exponential)),
        Err(Error::IntegerPolynomialLimitExceeded)
    );
}

#[test]
fn polynomial_identity_work_scales_with_a_fixed_width_ring_dag() {
    let mut costs = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut sum = x();
        for _ in 0..size {
            sum = IntegerTerm::add(sum, c(1));
        }
        let result = eq(sum, IntegerTerm::add(x(), c(size)));
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[], &[], &result));
        checked.unwrap();
        costs.push(work);
        assert_eq!(
            crate::instrumentation::with_run_work_limit(work, || check(0, &[], &[], &result)),
            Ok(())
        );
        assert_eq!(
            crate::instrumentation::with_run_work_limit(work - 1, || check(0, &[], &[], &result)),
            Err(Error::WorkLimitExceeded)
        );
    }
    assert!(
        costs.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
        "{costs:?}"
    );
}
