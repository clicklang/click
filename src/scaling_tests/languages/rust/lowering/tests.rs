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
