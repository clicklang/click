use super::*;

#[test]
fn let_binding_chains_retain_shared_prefixes_beside_unrelated_locals() {
    for signed in [false, true] {
        let wrap = |value| {
            if signed {
                CValue::Int64(value)
            } else {
                CValue::UInt64(value)
            }
        };
        for nested_values in [false, true] {
            for unrelated in [0, 128, 512] {
                let mut previous = None;
                for size in [16, 64, 256] {
                    let _session = VerificationSession::enter();
                    let mut state = CState::new()
                        .with_local("x", wrap(MachineTerm::Variable(Variable(992410))));
                    for index in 0..unrelated {
                        state.locals.set(format!("other_{index}"), int32(index));
                    }
                    let one = || SpecExpression::Value(wrap(MachineTerm::int64_constant(1)));
                    let expression = if nested_values {
                        let mut value = name("x");
                        for _ in 0..size {
                            value = bind("v", value, add(name("v"), one()));
                        }
                        value
                    } else {
                        let mut body = name(&format!("v{}", size - 1));
                        for index in (0..size).rev() {
                            let source = if index == 0 {
                                name("x")
                            } else {
                                name(&format!("v{}", index - 1))
                            };
                            body = bind(&format!("v{index}"), add(source, one()), body);
                        }
                        body
                    };
                    let exports = KernelTermExport::machine_export_count();
                    let ((path, work), map_work) =
                        crate::persistent::measure_persistent_work(|| {
                            crate::instrumentation::measure_deterministic_work(|| {
                                evaluate(SpecScope::unbound(&state, None), &expression)
                            })
                        });
                    assert!(matches!(path.value, SpecValue::Shared(_)));
                    assert_eq!(path.obligations.len(), if signed { size } else { 0 });
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    eprintln!(
                        "size={size}, signed={signed}, nested={nested_values}, unrelated={unrelated}, work={work}, map={map_work}"
                    );
                    if let Some(previous) = previous {
                        assert!(
                            work + map_work <= previous * 6,
                            "size={size}, signed={signed}, nested={nested_values}, work={work}, map={map_work}, previous={previous}"
                        );
                    }
                    previous = Some(work + map_work);
                }
            }
        }
    }
}

#[test]
fn selected_let_lookup_does_not_scan_other_lexical_values() {
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let state = CState::new();
        let selected = KernelTerm::variable(KernelType::C(CType::UInt64), Variable(992420));
        let mut values = crate::persistent::PersistentMap::default();
        for index in 0..size {
            values.insert(format!("other_{index}"), selected.clone());
        }
        values.insert("selected".into(), selected.clone());
        let scope = SpecScope {
            values: Some(&values),
            ..SpecScope::unbound(&state, None)
        };
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            for _ in 0..8 {
                assert_eq!(
                    evaluate(scope, &name("selected")).value,
                    SpecValue::Shared(selected.clone())
                );
                assert_eq!(
                    evaluate(scope, &bind("selected", word(9), name("selected"))).value,
                    word_value(9)
                );
            }
        });
        assert!(work < 1000, "size={size}, work={work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
