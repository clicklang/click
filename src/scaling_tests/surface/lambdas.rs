use super::*;

#[test]
fn beta_slots_are_stable_and_linear_through_unused_binders() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let mut body = SurfaceTerm::Binding("x".into());
        for number in (0..size).rev() {
            body = SurfaceTerm::Let {
                name: SurfaceBinder::Generated(crate::kernel::GeneratedBinderId::from_spelling(
                    number,
                )),
                click_type: Some(ClickType::Integer),
                value: Box::new(SurfaceTerm::IntegerLiteral("0".into())),
                body: Box::new(body),
            };
        }
        let application = SurfaceTerm::Apply {
            function: Box::new(SurfaceTerm::Lambda {
                parameters: vec![("x".into(), ClickType::Integer)],
                result: ClickType::Integer,
                body: Box::new(body),
            }),
            arguments: vec![SurfaceTerm::IntegerLiteral("3".into())],
        };
        let (first, work) = crate::instrumentation::measure_deterministic_work(|| {
            reduce_head(&application).unwrap().unwrap()
        });
        assert_eq!(first, reduce_head(&application).unwrap().unwrap());
        assert!(
            work >= size as usize,
            "the walk must count the selected binders: {work}"
        );
        measurements.push(work);
    }
    assert!(
        measurements[2] <= measurements[0] * 20 + 64,
        "selected binder work: {measurements:?}"
    );
}
