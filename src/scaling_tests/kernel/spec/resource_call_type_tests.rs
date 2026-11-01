use super::*;

#[test]
fn selected_call_domain_recovery_ignores_unrelated_context() {
    let _session = VerificationSession::enter();
    let source = clause(value(945_004));
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![Term::CValue(value(946_000 + index))],
            });
        }
        let (paths, work) =
            crate::instrumentation::measure_deterministic_work(|| lower(&source, &context, true));
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].facts.len(), 1);
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2),
        "{samples:?}"
    );
}

#[test]
fn selected_constructor_domain_recovery_ignores_growing_context() {
    let _session = VerificationSession::enter();
    let source = constructor_clause(value(945_020));
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![Term::CValue(value(946_000 + index))],
            });
            // Many other nominal classes on the queried pointer must not
            // turn the exact class lookup into an object-bucket scan.
            let other_class = CAccessClass::Struct(CStructClass::opaque(format!("other_{index}")));
            context =
                context.assume_proposition(crate::kernel::object_types::checked_call_type_fact(
                    &value(945_020).with_pointer_object_class(Some(other_class.clone())),
                    &other_class,
                ));
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let recovered = lower(&source, &context, true);
            assert!(lower(&source, &context, false).is_empty());
            recovered
        });
        assert_eq!(paths.len(), 1);
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2),
        "{samples:?}"
    );
}
