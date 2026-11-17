// Scaling tests for Rust expression lowering: selected work is independent
// of unrelated functions, and total work grows with the selected functions.
use super::*;

#[test]
fn narrow_remainder_lowering_has_bounded_selected_and_linear_total_work() {
    let mut export = super::super::charon::decode(
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/design/charon-trial/narrow-remainder/.click/widths/widths.rs.ullbc"
        )),
        "widths.rs",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/design/charon-trial/narrow-remainder/widths.rs"
        )),
    )
    .unwrap();
    let selected = export
        .functions
        .iter()
        .find(|f| f.name == "parity_u8")
        .unwrap()
        .clone();
    let mut samples = Vec::new();
    for count in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        export.functions = (0..count)
            .map(|index| {
                let mut f = selected.clone();
                f.name = format!("parity_{index}");
                f
            })
            .collect();
        let functions = export
            .functions
            .iter()
            .map(|f| (f.name.as_str(), f))
            .collect();
        let (lowered, selected_work) = crate::instrumentation::measure_deterministic_work(|| {
            lower_function(
                &export,
                None,
                &export.functions[0],
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &functions,
            )
        });
        lowered.unwrap();
        let (all, total_work) =
            crate::instrumentation::measure_deterministic_work(|| lower(&export));
        assert_eq!(all.unwrap().0.len(), count);
        samples.push((count, selected_work, total_work));
    }
    let (base_count, selected, total) = samples[0];
    assert!(selected > 0 && total > 0, "{samples:?}");
    for (count, selected_work, total_work) in &samples {
        assert!(*selected_work <= selected + 64, "{samples:?}");
        assert!(
            *total_work <= total * count / base_count + 128,
            "{samples:?}"
        );
    }
}

#[test]
fn returned_call_lowering_ignores_unrelated_function_declarations() {
    let mut baseline = None;
    for count in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = super::return_call_tests::fixture("__rust_return_value");
        let selected = export.functions[1].clone();
        let identity = export.functions[0].clone();
        export.functions.extend((0..count).map(|index| {
            let mut function = identity.clone();
            function.name = format!("unrelated_{index}");
            function
        }));
        let functions = export
            .functions
            .iter()
            .map(|f| (f.name.as_str(), f))
            .collect();
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            lower_function(
                &export,
                None,
                &selected,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &functions,
            )
        });
        let lowered = lowered.unwrap();
        assert!(
            matches!(lowered.prelowered_kernel_function().unwrap().body(), ProgramStatement::Seq(body)
            if matches!(body.iter().last().map(|statement| statement.as_ref()), Some(ProgramStatement::Return(ProgramExpression::StepResult { step: 0, .. }))))
        );
        assert!(work > 0);
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "{count} unrelated functions"
        );
    }
}

#[test]
fn checked_operand_lowering_is_local_and_scales_with_explicit_expression() {
    fn expression(depth: usize) -> E {
        let mut value = E::Local {
            name: "__rust_checked_0".into(),
        };
        for _ in 0..depth {
            value = E::Binary {
                operator: "add".into(),
                left_type: Type::I32,
                right_type: Type::I32,
                left: Box::new(value),
                right: Box::new(E::Integer { value: 1 }),
            };
        }
        value
    }
    let mut ambient_work = None;
    for count in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = super::return_call_tests::fixture("__rust_checked_0");
        export.functions[1].body = vec![S::Return {
            value: Some(expression(8)),
        }];
        let selected = export.functions[1].clone();
        let identity = export.functions[0].clone();
        export.functions.extend((0..count).map(|index| {
            let mut f = identity.clone();
            f.name = format!("unrelated_{index}");
            f
        }));
        let functions = export
            .functions
            .iter()
            .map(|f| (f.name.as_str(), f))
            .collect();
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            lower_function(
                &export,
                None,
                &selected,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &functions,
            )
        });
        lowered.unwrap();
        assert!(work > 0);
        assert_eq!(
            work,
            *ambient_work.get_or_insert(work),
            "{count} unrelated declarations"
        );
    }
    let mut samples = Vec::new();
    for depth in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut export = super::return_call_tests::fixture("__rust_checked_0");
        export.functions[1].body = vec![S::Return {
            value: Some(expression(depth)),
        }];
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| lower(&export));
        lowered.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|w| w[1] <= w[0] * 5 + 64),
        "{samples:?}"
    );
}
