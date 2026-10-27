#[test]
fn loadability_explanation_ignores_unrelated_objects() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".into());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let missing = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: pointer_base(&values),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let covering = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: pointer_base(&values),
        bytes: Bitvector32Term::Constant(8),
        wide: false,
    };
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: state.memory().clone(),
                base: Pointer {
                    block: PointerBlock::Heap(index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                bytes: Bitvector32Term::Constant(8),
                wide: false,
            });
        }
        let (explanation, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
            loadability_explanation(&missing, &context, &site, &mut site.labels())
        });
        assert!(explanation.is_none());
        assert_eq!(
            miss_work, 0,
            "a missing object must not visit other objects' facts"
        );
        let with_range = context.assume_proposition(covering.clone());
        let (explanation, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
            loadability_explanation(&missing, &with_range, &site, &mut site.labels())
        });
        assert!(explanation.is_some());
        let withdrawn = with_range.without_exact_fact(&covering);
        assert!(loadability_explanation(&missing, &withdrawn, &site, &mut site.labels()).is_none());
        samples.push(hit_work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
