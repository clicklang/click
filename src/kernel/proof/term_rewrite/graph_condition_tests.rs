use super::*;
use crate::kernel::equality_graph::EqualityGraph;

fn offset(id: u64) -> PointerOffsetTerm {
    PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(id))),
        byte_width: 4,
    }
}

fn guard() -> ConditionTerm {
    ConditionTerm::pointer_offset_equal(offset(51), offset(52))
}

fn choice() -> Bitvector32Term {
    Bitvector32Term::If {
        condition: Box::new(guard()),
        then_term: Box::new(Bitvector32Term::Constant(7)),
        else_term: Box::new(Bitvector32Term::Constant(0)),
    }
}

fn graph() -> EqualityGraph {
    let mut graph = EqualityGraph::default();
    graph.add_offset_equality(&offset(51), &offset(52));
    graph
}

#[test]
fn graph_condition_reduction_keeps_unknown_equalities_and_branches_isolated() {
    let empty = HashMap::new();
    let parent = EqualityGraph::default();
    let mut branch = parent.clone();
    branch.add_offset_equality(&offset(51), &offset(52));
    assert_eq!(
        TermRewrite::for_conditions_with_graph(&empty, &branch).bits(&choice()),
        Bitvector32Term::Constant(7)
    );
    assert_eq!(
        TermRewrite::for_conditions_with_graph(&empty, &parent).bits(&choice()),
        choice()
    );
    // Other rewriting clients do not acquire ambient semantics.
    assert_eq!(
        TermRewrite::for_conditions(&empty).bits(&choice()),
        choice()
    );
}

#[test]
fn graph_condition_reduction_preserves_all_binder_bodies() {
    check_binder_bodies(false);
    check_binder_bodies(true);
}

fn check_binder_bodies(scalar: bool) {
    let guard = || {
        if scalar {
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(51)),
                Bitvector32Term::Variable(Variable(52)),
            )
        } else {
            guard()
        }
    };
    let choice = || Bitvector32Term::If {
        condition: Box::new(guard()),
        then_term: Box::new(Bitvector32Term::Constant(7)),
        else_term: Box::new(Bitvector32Term::Constant(0)),
    };
    let mut graph = graph();
    graph.add_int32_equality(
        &Bitvector32Term::Variable(Variable(51)),
        &Bitvector32Term::Variable(Variable(52)),
    );
    let cited = HashMap::from([(guard(), true)]);
    let empty = HashMap::new();
    let machine_fold = Bitvector32Term::RangeFold {
        start: Box::new(Bitvector32Term::Constant(0)),
        end: Box::new(Bitvector32Term::Constant(2)),
        initial: Box::new(Bitvector32Term::Constant(0)),
        accumulator: Variable(60),
        item: Variable(51),
        body: Box::new(choice()),
    };
    let integer_body = IntegerTerm::from_machine(MachineIntegerType::Int32, choice()).unwrap();
    let integer_fold = IntegerTerm::RangeFold {
        index: IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(2)),
        },
        initial: IntegerTerm::constant_i64(0).into(),
        accumulator: Variable(60),
        item: Variable(51),
        body: integer_body.clone().into(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Case".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32)],
    }]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "GraphScope".into(),
        arguments: vec![],
    };
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "GraphScope".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    };
    let scrutinee = AlgebraicTerm {
        algebraic_type,
        node: AlgebraicTermNode::Variable(Variable(70)),
    };
    let binding = AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(Variable(51))));
    let machine_match = Bitvector32Term::AlgebraicMatch {
        scrutinee: Box::new(scrutinee.clone()),
        arms: vec![AlgebraicBitvectorMatchArm {
            variant: "Case".into(),
            bindings: vec![binding.clone()],
            body: choice(),
        }],
    };
    let integer_match = IntegerTerm::AlgebraicMatch {
        scrutinee: Box::new(scrutinee),
        arms: vec![AlgebraicIntegerMatchArm {
            variant: "Case".into(),
            bindings: vec![binding],
            body: integer_body.into(),
        }],
    };
    let quantified = Proposition::ForAll {
        var: Variable(51),
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(guard(), true)),
    };
    // Both cited facts and graph facts are from the enclosing scope.
    for conditions in [&empty, &cited] {
        for mut rewrite in [
            TermRewrite::for_conditions(conditions),
            TermRewrite::for_conditions_with_graph(conditions, &graph),
        ] {
            assert_eq!(rewrite.bits(&machine_fold), machine_fold);
            assert_eq!(rewrite.integer(&integer_fold), integer_fold);
            assert_eq!(rewrite.bits(&machine_match), machine_match);
            assert_eq!(rewrite.integer(&integer_match), integer_match);
            assert_eq!(rewrite.proposition(&quantified), quantified);
        }
    }
}

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
fn int32_graph_conditions_do_not_cross_sorts_or_admit_disequality() {
    let a = Bitvector32Term::Variable(Variable(81));
    let b = Bitvector32Term::Variable(Variable(82));
    let c = Bitvector32Term::Variable(Variable(83));
    let context = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(a.clone(), b.clone()), true)
        .assume_condition(ConditionTerm::equal(b.clone(), c.clone()), false);
    let empty = HashMap::new();
    let mut rewrite = TermRewrite::for_conditions_with_graph(&empty, &context.equality_graph);
    assert_eq!(
        rewrite.condition(&ConditionTerm::equal(a.clone(), b.clone())),
        ConditionTerm::Constant(true)
    );
    for condition in [
        ConditionTerm::equal(b.clone(), c),
        ConditionTerm::Bitvector64Equal(Box::new(a.clone()), Box::new(b.clone())),
        ConditionTerm::IntegerEqual(
            IntegerTerm::from_machine(MachineIntegerType::Int32, a)
                .unwrap()
                .into(),
            IntegerTerm::from_machine(MachineIntegerType::Int32, b)
                .unwrap()
                .into(),
        ),
    ] {
        assert_eq!(rewrite.condition(&condition), condition);
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
