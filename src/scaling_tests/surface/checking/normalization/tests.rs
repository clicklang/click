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

#[test]
fn normalization_preserves_undecided_address_comparisons_without_export() {
    use crate::kernel::{Address, KernelAddressOffset, KernelTerm, SharedAddress};
    let mut samples = Vec::new();
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut offset = KernelAddressOffset::Variable(Variable(982811))
            .into_shared()
            .unwrap();
        for _ in 0..depth {
            offset = KernelAddressOffset::Add([offset.clone(), offset])
                .into_shared()
                .unwrap();
        }
        let base = Address::symbolic(Variable(982812));
        let address = SharedAddress::new(base.shared().block(), offset.clone());
        let mut sample = 0;
        for root in [
            KernelTerm::address_equal_raw([address.clone(), address]),
            KernelTerm::address_offset_equal_raw([offset.clone(), offset]),
        ] {
            let condition = StoredConditionTerm::from_root(root.clone()).unwrap();
            let proposition = Proposition::condition_is(condition, true);
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_proposition(&proposition)
            });
            assert_eq!(normalized, NormalizedProposition::Proposition(proposition));
            assert!(!root.has_cached_native_argument());
            sample += work;
        }
        samples.push(sample);
    }
    assert!(
        samples.windows(2).all(|work| work[0] == work[1]),
        "{samples:?}"
    );
}
