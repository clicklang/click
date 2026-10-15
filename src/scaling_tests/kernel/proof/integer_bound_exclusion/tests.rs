// Scaling tests of `src/kernel/proof/integer_bound_exclusion.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_bound_exclusion_work_scales_with_nodes_and_magnitude_not_unused_facts() {
    let x = IntegerTerm::var(Variable(182001));
    let goal = ne(x.clone(), IntegerTerm::constant(0.into()));
    let mut p = vec![le(IntegerTerm::constant(1.into()), x.clone())];
    let mut baseline = None;
    for size in [4usize, 16, 64, 256] {
        while p.len() < size {
            p.push(le(x.clone(), x.clone()));
        }
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0], &p, &goal));
        checked.unwrap();
        assert_eq!(*baseline.get_or_insert(work), work);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerBoundExclusion {
                    bounds: vec![0],
                    result: goal.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &p));
        checked.unwrap();
        assert_eq!(work, size * baseline.unwrap() + 1);
    }
    let mut previous = 0;
    for bits in [64usize, 128, 256, 512, 1024] {
        let endpoint = BigInt::from(1) << bits;
        let p = [le(IntegerTerm::constant(endpoint), x.clone())];
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0], &p, &goal));
        checked.unwrap();
        assert!(work > previous);
        previous = work;
        crate::instrumentation::with_run_work_limit(work - 1, || {
            assert_eq!(check(0, &[0], &p, &goal), Err(Error::WorkLimitExceeded))
        });
        crate::instrumentation::with_run_work_limit(work, || check(0, &[0], &p, &goal).unwrap());
    }
}
