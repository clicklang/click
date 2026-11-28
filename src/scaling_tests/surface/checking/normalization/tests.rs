use super::*;

#[test]
fn normalize_shared_integer_comparisons_without_expanding_operands() {
    use crate::kernel::{IntegerComparisonOperator as Op, KernelIntegerOperator, KernelTerm};
    let mut samples = Vec::new();
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut sum = KernelTerm::integer_literal(0.into());
        for _ in 0..depth {
            sum = KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![sum.clone(), sum])
                .unwrap();
        }
        let mut sample = 0;
        for (operator, expected) in [
            (Op::Equal, Some(true)),
            (Op::NotEqual, Some(false)),
            (Op::LessThan, None),
            (Op::LessEqual, None),
            (Op::GreaterThan, None),
            (Op::GreaterEqual, None),
        ] {
            let root =
                KernelTerm::integer_comparison(operator, [sum.clone(), sum.clone()]).unwrap();
            let condition = StoredConditionTerm::from_root(root.clone()).unwrap();
            let proposition = Proposition::condition_is(condition, true);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_proposition(&proposition)
            });
            sample += work;
            assert_eq!(
                result,
                match expected {
                    Some(true) => NormalizedProposition::True,
                    Some(false) => NormalizedProposition::False,
                    None => NormalizedProposition::Proposition(proposition),
                }
            );
            assert!(!root.has_cached_native_argument());
            assert!(!sum.has_cached_native_argument());
        }
        samples.push(sample);
    }
    assert!(
        samples.windows(2).all(|work| work[0] == work[1]),
        "{samples:?}"
    );
}
