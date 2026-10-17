use super::*;

#[test]
fn object_type_queries_ignore_unrelated_supported_values() {
    let _session = VerificationSession::enter();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(source(&format!("typed{index}"), &pointer(index)));
        }
        let alias = pointer(count + 1);
        context = context.assume_proposition(equal(&pointer(0), &alias));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                assert!(can_type(&context, &alias));
                assert!(!can_type(&context, &pointer(count + 2)));
            }
        });
        assert!(work > 0);
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work <= samples[0] * 2), "{samples:?}");
}

#[test]
fn type_sources_share_the_weighted_pointer_class_merge_bound() {
    let _session = VerificationSession::enter();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let p = pointer(10_000);
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(source(&format!("proof{index}"), &p));
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..count {
                let alias = pointer(20_000 + index);
                context = context.clone().assume_proposition(equal(&p, &alias));
                assert!(can_type(&context, &alias));
            }
        });
        assert!(work > 0);
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) as usize * 2, "{samples:?}");
    }
}
