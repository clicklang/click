// Scaling tests of `src/kernel/proof/integer_product_bounds.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn product_bounds_work_is_linear_in_nodes_and_independent_of_unused_facts_and_operand_depth() {
    let (mut x, y) = variables();
    let mut last = None;
    for size in [4, 16, 64, 256, 1024] {
        for _ in 0..size {
            x = IntegerTerm::multiply(x, y.clone());
        }
        let mut premises = inputs(&x, &y, &[(-2).into(), 3.into(), (-4).into(), 5.into()]);
        premises.extend((0..size).map(|_| le(y.clone(), IntegerTerm::constant_i64(100))));
        let result = goal(&x, &y, 15.into(), false);
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1, 2, 3], &premises, &result)
        });
        assert_eq!(checked, Ok(()));
        if let Some(last) = last {
            assert_eq!(work, last);
        }
        last = Some(work);
        let certificate = SpecialArithmeticCertificate {
            nodes: (0..size)
                .map(|_| SpecialArithmeticNode::IntegerProductBounds {
                    bounds: vec![0, 1, 2, 3],
                    result: result.clone(),
                })
                .collect(),
            conclusion: 0,
        };
        let (checked, total) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&result, &premises)
        });
        assert_eq!(checked, Ok(()));
        assert_eq!(total, size * work + 1);
    }
}

#[test]
fn product_bounds_precharge_big_integer_work_and_stop_before_arithmetic() {
    let (x, y) = variables();
    let mut previous = 0;
    for bits in [64usize, 128, 256, 512, 1024] {
        let limit = BigInt::from(1) << bits;
        let premises = inputs(&x, &y, &[-&limit, limit.clone(), -&limit, limit.clone()]);
        let result = goal(&x, &y, &limit * &limit, false);
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1, 2, 3], &premises, &result)
        });
        assert_eq!(checked, Ok(()));
        assert!(work > previous);
        if previous != 0 {
            assert!(work <= previous * 4);
        }
        previous = work;
        crate::instrumentation::with_run_work_limit(work - 1, || {
            assert_eq!(
                check(0, &[0, 1, 2, 3], &premises, &result),
                Err(Error::WorkLimitExceeded)
            );
        });
        crate::instrumentation::with_run_work_limit(work, || {
            assert_eq!(check(0, &[0, 1, 2, 3], &premises, &result), Ok(()));
        });
    }
}
