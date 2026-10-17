use super::*;

#[test]
fn integer_known_fact_queries_ignore_unrelated_equalities() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("IntegerScaling", AlgebraicValueType::C(CType::Int32));
    let a = variable(&ty, 920_201);
    let b = variable(&ty, 920_202);
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_proposition(eq(
                I::Variable(Variable(930_000 + 2 * i)),
                I::Variable(Variable(930_001 + 2 * i)),
            ));
        }
        let total = I::Variable(Variable(920_203));
        context = context
            .assume_proposition(eq(total.clone(), count(&a)))
            .assume_proposition(alias(&a, &b));
        let goal = eq(total, count(&b));
        let (known, work) =
            crate::instrumentation::measure_deterministic_work(|| context.contains_known(&goal));
        assert!(known);
        if let Some(prior) = previous {
            assert_eq!(work, prior, "unrelated facts at {size}");
        }
        previous = Some(work);
    }
}

#[test]
fn shared_integer_expression_dags_register_and_merge_in_linear_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: SharedIntegerTerm = I::Variable(Variable(920_211)).into();
    let y: SharedIntegerTerm = I::Variable(Variable(920_212)).into();
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let build = |mut term: SharedIntegerTerm| {
            for _ in 0..size {
                term = I::Add(term.clone(), term).into();
            }
            term
        };
        let a = build(x.clone());
        let b = build(y.clone());
        let ((before, after), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            let before = graph.are_integer_equal(&a, &b);
            graph.add_integer_equality(&x, &y);
            (before, graph.are_integer_equal(&a, &b))
        });
        assert!(!before);
        assert!(after);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= 5 * p[0]),
        "superlinear shared-DAG work: {samples:?}"
    );
}
