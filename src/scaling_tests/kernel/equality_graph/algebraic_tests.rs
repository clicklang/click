// Scaling tests of `src/kernel/equality_graph/algebraic_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn algebraic_closure_nested_constructor_registration_scales_with_selected_model() {
    let nominal = AlgebraicValueType::Algebraic {
        name: "Tree".into(),
        arguments: vec![],
    };
    let ty = model_type("Tree", nominal);
    let costs = [4, 8, 16, 32].map(|depth| {
        let mut a = variable(&ty, 40);
        let mut b = variable(&ty, 41);
        for _ in 0..depth {
            a = constructor(&ty, "Node", vec![AlgebraicValue::Algebraic(a)]);
            b = constructor(&ty, "Node", vec![AlgebraicValue::Algebraic(b)]);
        }
        let mut graph = EqualityGraph::default();
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(!graph.are_algebraic_equal(&a, &b));
                graph.add_algebraic_equality(&variable(&ty, 40), &variable(&ty, 41));
                assert!(graph.are_algebraic_equal(&a, &b));
            })
        });
        (work, maps)
    });
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 3, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 3, "{costs:?}");
    }
}

#[test]
fn algebraic_closure_lookup_does_not_scan_unrelated_models() {
    let ty = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let costs = [8, 32, 128, 512].map(|size| {
        let mut context = PureFactContext::new();
        for id in 0..size {
            context = context.assume_proposition(eq(
                &variable(&ty, 100 + id),
                &constructor(&ty, "Node", vec![scalar(10000 + id)]),
            ));
        }
        context = context.assume_proposition(eq(&variable(&ty, 100), &variable(&ty, 50000)));
        let goal = eq(
            &variable(&ty, 50000),
            &constructor(&ty, "Node", vec![scalar(10000)]),
        );
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(context.contains_known(&goal));
            })
        });
        (work, maps)
    });
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn scalar_conflict_queries_and_selected_merges_skip_ambient_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("ConflictScale", AlgebraicValueType::C(CType::Int32));
    let (a, b) = (variable(&ty, 80), variable(&ty, 81));
    let getter = |model| Bitvector32Term::ClickFunctionApplication {
        name: "pending".into(),
        arguments: vec![PureFunctionArgument::Algebraic(model)],
    };
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut base = PureFactContext::new();
        for index in 0..size {
            base = base.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(1000 + index)),
                    Bitvector32Term::Constant(7),
                ),
                true,
            );
        }
        base = base
            .assume_condition(
                ConditionTerm::equal(getter(a.clone()), Bitvector32Term::Constant(1)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(getter(b.clone()), Bitvector32Term::Constant(0)),
                true,
            );
        let (child, work) = crate::instrumentation::measure_deterministic_work(|| {
            base.assume_proposition(eq(&a, &b))
        });
        assert!(child.equality_graph.has_scalar_constant_conflict());
        let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..64 {
                assert!(child.is_inconsistent());
            }
        });
        assert_eq!(
            query_work, 64,
            "conflict checks read one flag, regardless of ambient state"
        );
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work <= costs[0] * 2),
        "selected-merge work: {costs:?}"
    );
}

#[test]
fn constructor_lookup_skips_unrelated_model_classes() {
    let ty = model_type(
        "ConstructorLookupScale",
        AlgebraicValueType::C(CType::Int32),
    );
    let costs = [16, 64, 256, 1024].map(|size| {
        let mut context = PureFactContext::new();
        for id in 0..size {
            context = context.assume_proposition(eq(
                &variable(&ty, 1000 + id),
                &constructor(&ty, "Node", vec![scalar(id)]),
            ));
        }
        let (a, b, c) = (variable(&ty, 10), variable(&ty, 11), variable(&ty, 12));
        let ctor = constructor(&ty, "Node", vec![scalar(7)]);
        context = context
            .assume_proposition(eq(&a, &b))
            .assume_proposition(eq(&b, &c))
            .assume_proposition(eq(&c, &ctor));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(context.known_algebraic_constructor(&a), Some(ctor));
            })
        });
        (work, maps)
    });
    for pair in costs.windows(2) {
        assert_eq!(pair[1].0, pair[0].0, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}
