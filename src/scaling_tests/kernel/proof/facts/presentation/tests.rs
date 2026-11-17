/// Deep conjunctions intern each node once; unrelated facts and long related
/// syntax must not turn strict membership into a scan or quadratic clone.
#[test]
fn written_syntax_and_ordinal_queries_scale_with_input() {
    let mut samples = Vec::new();
    for size in [32, 128, 512] {
        let mut facts = FactPresentation::default();
        for index in 0..size {
            facts.append(atom(&format!("unrelated_{index}")));
        }
        let chain = (0..size).fold(atom("head").as_ref().clone(), |left, index| {
            Proposition::And(
                Box::new(left),
                Box::new(atom(&format!("related_{index}")).as_ref().clone()),
            )
        });
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            facts.append(Arc::new(chain.clone()));
            assert!(facts.has_conjunct(&chain));
        });
        samples.push(work);
        let (_, selected) = crate::persistent::measure_persistent_work(|| {
            assert!(facts.get(size).is_some());
            assert!(facts.get(size + 1).is_none());
        });
        assert!(
            selected <= 2 * (usize::BITS - size.leading_zeros()) as usize + 4,
            "size {size}: {selected}"
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 6 + 512),
        "{samples:?}"
    );
}
