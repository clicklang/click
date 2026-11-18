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
fn staged_rust_operands_scale_with_captures_and_unrelated_parameters() {
    fn captures(statement: &ProgramStatement) -> usize {
        match statement {
            ProgramStatement::Seq(body) => body.iter().map(|item| captures(item)).sum(),
            ProgramStatement::StepValue { .. } => 1,
            _ => 0,
        }
    }

    let mut samples = Vec::new();
    for count in [8, 32, 128] {
        let mut export = super::return_call_tests::fixture("value");
        let mut value = E::Local {
            name: "value".into(),
        };
        for _ in 0..count {
            value = E::Binary {
                operator: "add".into(),
                left_type: Type::I32,
                right_type: Type::I32,
                left: Box::new(value),
                right: Box::new(E::Integer { value: 1 }),
            };
        }
        export.functions[1].body = vec![S::Return { value: Some(value) }];
        for unrelated in [0, 8, 32, 128] {
            let caller = &mut export.functions[1];
            caller.parameters.truncate(1);
            let template = caller.parameters[0].clone();
            caller.parameters.extend((0..unrelated).map(|index| {
                let mut parameter = template.clone();
                parameter.name = format!("unrelated_{index}");
                parameter
            }));
            let (lowered, work) =
                crate::instrumentation::measure_deterministic_work(|| lower(&export));
            let (functions, _) = lowered.unwrap();
            let body = functions[1].prelowered_kernel_function().unwrap().body();
            assert_eq!(captures(body), count - 1);
            samples.push((count, unrelated, work));
        }
    }
    let (_, _, baseline) = samples[0];
    assert!(baseline > 0);
    for (count, unrelated, work) in &samples {
        assert!(
            *work <= baseline * count / 8 + 64 * unrelated + 64,
            "{samples:?}"
        );
    }
}
