#[test]
fn temporary_binding_access_skips_unrelated_locals() {
    let mut samples = Vec::new();
    for size in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = LocalFunctionId::new(Some("unit.cpp".into()), "f".into());
        let temporary: BindingName = LocalBindingId::temporary(owner, 0).into();
        let mut locals = LocalEnvironment::new();
        for index in 0..size {
            locals.set(format!("noise_{index}"), int32(index));
        }
        locals.set("__click_cpp_nested_value_0", int32(3));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                locals.set(&temporary, int32(7));
                assert_eq!(locals.get(&temporary).unwrap().native().as_ref(), &int32(7));
                assert_eq!(locals.resolve_binding(&temporary), temporary);
                assert_eq!(locals.active_source_name(&temporary), None);
                assert_eq!(
                    locals
                        .get("__click_cpp_nested_value_0")
                        .unwrap()
                        .native()
                        .as_ref(),
                    &int32(3)
                );
            }
        });
        samples.push(work);
    }
    assert_eq!(
        samples, [samples[0]; 3],
        "indexed temporary operations: {samples:?}"
    );
}

#[test]
fn reference_carrier_lookups_ignore_unrelated_and_shadowed_bindings() {
    let mut lookup_costs = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let owner = LocalFunctionId::new(Some("references.cpp".into()), "f".into());
        let mut locals = LocalEnvironment::default();
        let mut carriers = Vec::new();
        for ordinal in 0..size {
            let declaration = LocalBindingId::new(owner.clone(), false, ordinal, Some("x".into()));
            let carrier = BindingName::reference_carrier(BindingName::Local(declaration));
            locals.set(carrier.clone(), int32(ordinal));
            carriers.push(carrier);
        }
        let branch = locals.clone();
        let (_, work) =
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    locals.get(&carriers[0]).unwrap().native().as_ref(),
                    &int32(0)
                );
                assert_eq!(
                    locals
                        .get(carriers.last().unwrap())
                        .unwrap()
                        .native()
                        .as_ref(),
                    &int32(size - 1)
                );
                let absent = BindingName::reference_carrier(BindingName::Local(
                    LocalBindingId::new(owner.clone(), false, size, Some("x".into())),
                ));
                assert!(locals.get(&absent).is_none());
            });
        lookup_costs.push(work);
        locals.set(carriers[0].clone(), int32(7));
        assert_eq!(
            branch.get(&carriers[0]).unwrap().native().as_ref(),
            &int32(0)
        );
        assert_eq!(
            locals.get(&carriers[0]).unwrap().native().as_ref(),
            &int32(7)
        );
    }
    assert!(lookup_costs.iter().all(|work| *work > 0));
    assert!(
        lookup_costs.iter().all(|work| *work == lookup_costs[0]),
        "{lookup_costs:?}"
    );
}
