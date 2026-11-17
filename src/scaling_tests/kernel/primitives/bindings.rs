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
