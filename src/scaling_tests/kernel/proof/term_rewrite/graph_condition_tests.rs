// Scaling tests of `src/kernel/proof/term_rewrite/graph_condition_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn graph_condition_reduction_scales_with_the_expression_not_ambient_facts() {
    for size in [16usize, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut graph = graph();
        for i in 0..size as u64 {
            graph.add_offset_equality(&offset(1000 + 2 * i), &offset(1001 + 2 * i));
        }
        let empty = HashMap::new();
        let ((output, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                TermRewrite::for_conditions_with_graph(&empty, &graph).bits(&choice())
            })
        });
        assert_eq!(output, Bitvector32Term::Constant(7));
        assert!(work < 100, "size={size}, work={work}");
        assert!(
            map_work < 100 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        let input = Bitvector32Term::ClickFunctionApplication {
            name: "many".into(),
            arguments: vec![PureFunctionArgument::Value(CValue::Int32(choice())); size],
        };
        let expected = Bitvector32Term::ClickFunctionApplication {
            name: "many".into(),
            arguments: vec![
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Constant(7)));
                size
            ],
        };
        let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions_with_graph(&empty, &graph).bits(&input)
        });
        assert_eq!(output, expected);
        assert!(work < 100 * size, "size={size}, expression work={work}");
    }
}

#[test]
fn int32_guard_queries_ignore_unrelated_graph_equalities() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let var = |id| Bitvector32Term::Variable(Variable(id));
        let mut graph = EqualityGraph::default();
        graph.add_int32_equality(&var(1), &var(2));
        for i in 0..size {
            graph.add_int32_equality(&var(100 + 2 * i), &var(101 + 2 * i));
        }
        let choice = Bitvector32Term::If {
            condition: Box::new(ConditionTerm::equal(var(1), var(2))),
            then_term: Box::new(Bitvector32Term::Constant(7)),
            else_term: Box::new(Bitvector32Term::Constant(0)),
        };
        let empty = HashMap::new();
        let ((output, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                TermRewrite::for_conditions_with_graph(&empty, &graph).bits(&choice)
            })
        });
        assert_eq!(output, Bitvector32Term::Constant(7));
        assert!(work < 100, "size={size}, work={work}");
        assert!(
            map_work < 100 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
