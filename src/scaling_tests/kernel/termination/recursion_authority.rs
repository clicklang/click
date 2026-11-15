#[test]
fn selecting_recursion_authority_ignores_unrelated_declarations_and_bodies() {
    for size in [1, 16, 64, 256, 1024] {
        let mut functions = vec![expression("f", &[])];
        functions.extend((0..size).map(|index| expression(&format!("unrelated_{index}"), &[])));
        let (authority, work) = crate::instrumentation::measure_deterministic_work(|| {
            RecursionDeclarations::open(
                &functions.iter().collect::<Vec<_>>(),
                &[expression_plan("f")],
            )
            .unwrap()
        });
        assert!(work <= 4 * size + 16, "{size}: {work} opening work");
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            authority
                .select("f", &BTreeSet::from(["f".into()]), false, false)
                .unwrap()
        });
        assert_eq!(
            selected
                .expression
                .as_ref()
                .map(|authority| authority.source.as_str()),
            Some("0")
        );
        assert!(work <= 8, "{size}: {work} selected work");
    }
}

#[test]
fn opening_and_selecting_recursion_authority_scale_with_declared_peers() {
    for size in [1, 8, 64, 256] {
        let peers = (0..size)
            .map(|index| format!("peer_{index}"))
            .collect::<Vec<_>>();
        let mut functions = vec![expression(
            "f",
            &peers.iter().map(String::as_str).collect::<Vec<_>>(),
        )];
        functions.extend(peers.iter().map(|peer| expression(peer, &[])));
        let plans = functions
            .iter()
            .map(|function| expression_plan(function.name()))
            .collect::<Vec<_>>();
        let (authority, work) = crate::instrumentation::measure_deterministic_work(|| {
            RecursionDeclarations::open(&functions.iter().collect::<Vec<_>>(), &plans).unwrap()
        });
        assert!(work <= 8 * size + 16, "{size}: {work} opening work");
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            authority
                .select("f", &peers.into_iter().collect(), false, false)
                .unwrap()
        });
        assert!(selected.expression.is_some());
        assert!(work <= 4 * size + 8, "{size}: {work} selected work");
    }
}
