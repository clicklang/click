use super::*;

#[test]
fn integer_known_fact_queries_ignore_unrelated_equalities() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("IntegerScaling", AlgebraicValueType::C(ProgramType::Int32));
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

#[test]
fn retained_call_argument_congruence_is_linear_cold_and_constant_warm() {
    use crate::kernel::{KernelTerm, KernelTermExport, SharedMachineIntegerTerm};
    let mut costs = Vec::new();
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf = MachineTerm::ClickFunctionApplication {
            name: "argument_leaf".into(),
            arguments: vec![PureFunctionArgument::Value(ProgramValue::UInt64(
                MachineTerm::Variable(Variable(982821)),
            ))],
        };
        let mut root = KernelTerm::retained_native_machine_operand(M::UInt64, &leaf);
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                M::UInt64,
                crate::kernel::MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let exact = SharedMachineIntegerTerm::from_shared(M::UInt64, root.clone()).unwrap();
        let bound = |argument| {
            ConditionTerm::narrow_compare(
                M::UInt8,
                crate::kernel::CompareRelation::LessEqual,
                MachineTerm::Constant {
                    format: M::UInt8,
                    bits: 48,
                },
                MachineTerm::ClickFunctionApplication {
                    name: "argument_digit".into(),
                    arguments: vec![PureFunctionArgument::SharedMachine(argument)],
                },
            )
        };
        let query =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(&bound(exact.clone()))
                .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (graph, cold) = crate::instrumentation::measure_deterministic_work(|| {
            let observed =
                SharedMachineIntegerTerm::observe_shared(M::UInt64, root.clone()).unwrap();
            let mut graph = EqualityGraph::default();
            graph.add_condition(&bound(observed), true);
            assert!(graph.knows_condition(&query, true));
            graph
        });
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..8 {
                assert!(graph.knows_condition(&query, true));
            }
        });
        assert_eq!(exact.shared_operand(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push((cold, warm));
    }
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= 4 * pair[0].0 + 256, "cold: {costs:?}");
        assert!(pair[1].1 <= pair[0].1 + 64, "warm: {costs:?}");
    }
}
