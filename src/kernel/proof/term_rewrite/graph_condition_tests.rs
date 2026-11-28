use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::equality_graph::EqualityGraph;

fn offset(id: u64) -> AddressOffset {
    AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(id)), 4)
}

fn guard() -> OldConditionTerm {
    OldConditionTerm::address_offset_equal(offset(51), offset(52))
}

fn choice() -> OldMachineTerm {
    OldMachineTerm::If {
        condition: Box::new(guard()),
        then_term: Box::new(OldMachineTerm::constant(7)),
        else_term: Box::new(OldMachineTerm::constant(0)),
    }
}

fn graph() -> EqualityGraph {
    let mut graph = EqualityGraph::default();
    graph.add_offset_equality(&offset(51).clone(), &offset(52).clone());
    graph
}

#[test]
fn cited_graph_decides_stored_pointer_equations_at_either_polarity() {
    let _session = VerificationSession::enter();
    let addresses = [99849, 99850].map(|v| Address::symbolic(Variable(v)));
    let offsets = [99851, 99852].map(offset);
    let pointers = addresses.each_ref().map(|a| {
        Pointer::new(a.clone(), ProgramType::Int32Pointer)
            .with_element_count(OldMachineTerm::uint64_constant(5))
    });
    for root in [
        KernelTerm::address_equal_raw(addresses.each_ref().map(|a| a.shared().clone())),
        KernelTerm::address_offset_equal_raw(offsets.each_ref().map(|o| o.shared().clone())),
        KernelTerm::pointer_equal_raw(pointers.each_ref().map(|p| p.shared().clone())),
    ] {
        let written = KernelTermExport::condition(&root).unwrap();
        let mut positive = EqualityGraph::default();
        match &written {
            OldConditionTerm::AddressEqual(a, b) => {
                positive.add_equality(a, b);
            }
            OldConditionTerm::AddressOffsetEqual(a, b) => {
                positive.add_offset_equality(a, b);
            }
            OldConditionTerm::PointerEqual(a, b) => positive.add_pointer_equality(a, b),
            _ => unreachable!(),
        }
        let empty = EqualityGraph::default();
        let mut negative = EqualityGraph::default();
        assert!(negative.add_condition(&written, false));
        let facts = HashMap::new();
        let direct = HashMap::from([(written.flipped(), false)]);
        for truth in [true, false] {
            let goal = Proposition::condition_is(
                StoredConditionTerm::from_root(root.clone()).unwrap(),
                truth,
            );
            for (map, selected, ambient, decision) in [
                (&facts, &positive, &empty, Some(true)),
                (&facts, &negative, &empty, Some(false)),
                (&facts, &empty, &negative, None),
                (&direct, &positive, &empty, Some(false)),
            ] {
                let result = TermRewrite::for_cited_conditions_with_graph(map, selected, ambient)
                    .proposition(&goal);
                assert_eq!(
                    result.literal_condition(),
                    decision.map(|value| (value, truth))
                );
                assert!(!root.has_cached_native_argument());
            }
        }
    }
}

#[test]
fn stored_offset_equality_keeps_written_sums_and_uses_graph_evidence() {
    let _session = VerificationSession::enter();
    let [a, b] = [99839, 99840].map(offset);
    let sum = |a: &AddressOffset| AddressOffset::raw_add(a.clone(), AddressOffset::constant(0));
    let [left, right] = [sum(&a), sum(&b)];
    let root =
        KernelTerm::address_offset_equal_raw([left.shared().clone(), right.shared().clone()]);
    let source = StoredConditionTerm::from_root(root.clone()).unwrap();
    let mut graph = EqualityGraph::default();
    graph.add_offset_equality(&left, &right);
    let conditions = HashMap::new();

    for truth in [false, true] {
        let goal = Proposition::condition_is(source.clone(), truth);
        let mut rewrite = TermRewrite::for_pointer_offset_exact(&a, &b);
        let Proposition::ConditionIs(result, polarity) = rewrite.proposition(&goal) else {
            panic!("expected an offset equality");
        };
        assert!(rewrite.changed);
        assert_eq!(polarity, truth);
        assert_eq!(
            result.operand_view().pointer_offsets().unwrap(),
            [right.shared().clone(), right.shared().clone()]
        );
        assert!(!result.root().unwrap().has_cached_native_argument());
        assert_eq!(
            TermRewrite::for_conditions_with_graph(&conditions, &graph)
                .proposition(&goal)
                .literal_condition(),
            Some((true, truth))
        );
        assert!(!root.has_cached_native_argument());
    }
}

#[test]
fn stored_pointer_words_supply_order_guards_and_graph_operands() {
    let _session = VerificationSession::enter();
    let pointer = Pointer::new(
        Address::symbolic(Variable(99834)),
        ProgramType::Int32Pointer,
    );
    let [a, b] = [99835, 99836].map(|id| OldMachineTerm::Variable(Variable(id)));
    let source = KernelTerm::pointer_equal_raw([&a, &b].map(|word| {
        pointer
            .clone()
            .with_address(Address::from_integer_address(word.clone()))
            .into_shared()
    }));
    let goal = Proposition::condition_is(
        StoredConditionTerm::from_root(source.clone()).unwrap(),
        false,
    );
    assert_eq!(
        TermRewrite::conditional_guards(&goal),
        [
            OldConditionTerm::uint64_less_equal(a.clone(), b.clone()),
            OldConditionTerm::uint64_less_than(a.clone(), b.clone()),
        ]
    );
    let conditions = HashMap::new();
    let mut graph = EqualityGraph::default();
    let Proposition::ConditionIs(symbolic, false) =
        TermRewrite::for_conditions_with_graph(&conditions, &graph).proposition(&goal)
    else {
        panic!("expected the original truth polarity");
    };
    let root = symbolic.root().expect("stored word equality");
    assert!(matches!(
        root.node(),
        KernelTermNode::BoolCompare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            ..
        }
    ));
    assert!(!root.has_cached_native_argument());
    graph.add_uint64_equality(&a, &b);
    assert_eq!(
        TermRewrite::for_conditions_with_graph(&conditions, &graph)
            .proposition(&goal)
            .literal_condition(),
        Some((true, false))
    );
    assert!(!source.has_cached_native_argument());
}

#[test]
fn graph_condition_reduction_keeps_unknown_equalities_and_branches_isolated() {
    let empty = HashMap::new();
    let parent = EqualityGraph::default();
    let mut branch = parent.clone();
    branch.add_offset_equality(&offset(51).clone(), &offset(52).clone());
    assert_eq!(
        TermRewrite::for_conditions_with_graph(&empty, &branch).bits(&choice()),
        OldMachineTerm::constant(7)
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
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(51)),
                OldMachineTerm::Variable(Variable(52)),
            )
        } else {
            guard()
        }
    };
    let choice = || OldMachineTerm::If {
        condition: Box::new(guard()),
        then_term: Box::new(OldMachineTerm::constant(7)),
        else_term: Box::new(OldMachineTerm::constant(0)),
    };
    let mut graph = graph();
    graph.add_int32_equality(
        &OldMachineTerm::Variable(Variable(51)),
        &OldMachineTerm::Variable(Variable(52)),
    );
    let cited = HashMap::from([(guard(), true)]);
    let empty = HashMap::new();
    let machine_fold = OldMachineTerm::RangeFold {
        start: Box::new(OldMachineTerm::constant(0)),
        end: Box::new(OldMachineTerm::constant(2)),
        initial: Box::new(OldMachineTerm::constant(0)),
        accumulator: Variable(60),
        item: Variable(51),
        body: Box::new(choice()),
    };
    let integer_body = IntegerTerm::from_machine(MachineIntegerType::Int32, choice()).unwrap();
    let integer_fold = IntegerTerm::RangeFold {
        index: IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
        },
        initial: IntegerTerm::constant_i64(0).into(),
        accumulator: Variable(60),
        item: Variable(51),
        body: integer_body.clone().into(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Case".into(),
        fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
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
    let binding =
        AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(Variable(51))));
    let machine_match = OldMachineTerm::AlgebraicMatch {
        scrutinee: Box::new(scrutinee.clone()),
        arms: vec![AlgebraicBitvectorMatchArm {
            binding_names: Default::default(),
            variant: "Case".into(),
            bindings: vec![binding.clone()],
            body: choice(),
        }],
    };
    let integer_match = IntegerTerm::AlgebraicMatch {
        scrutinee: Box::new(scrutinee),
        arms: vec![AlgebraicIntegerMatchArm {
            binding_names: Default::default(),
            variant: "Case".into(),
            bindings: vec![binding],
            body: integer_body.into(),
        }],
    };
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        Variable(51),
        Sort::ProgramInt32,
        Proposition::condition_is(guard(), true),
    );
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
fn int32_graph_conditions_do_not_cross_sorts_or_admit_disequality() {
    let a = OldMachineTerm::Variable(Variable(81));
    let b = OldMachineTerm::Variable(Variable(82));
    let c = OldMachineTerm::Variable(Variable(83));
    let context = PureFactContext::new()
        .assume_condition(OldConditionTerm::equal(a.clone(), b.clone()), true)
        .assume_condition(OldConditionTerm::equal(b.clone(), c.clone()), false);
    let empty = HashMap::new();
    let mut rewrite = TermRewrite::for_conditions_with_graph(&empty, &context.equality_graph);
    assert_eq!(
        rewrite.condition(&OldConditionTerm::equal(a.clone(), b.clone())),
        OldConditionTerm::Constant(true)
    );
    for condition in [
        OldConditionTerm::equal(b.clone(), c),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(a.clone()),
            right: Box::new(b.clone()),
        },
        OldConditionTerm::IntegerEqual(
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

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/graph_condition_tests.rs");
}

#[test]
fn rewriting_a_bool_claim_keeps_the_lowerings_truth_polarity() {
    let from = OldConditionTerm::bool_application("before", vec![]);
    let after = OldConditionTerm::bool_application("after", vec![]);
    let replacement = OldConditionTerm::bool_not(after.clone());
    for truth in [false, true] {
        let claim = Proposition::condition_is(from.clone(), truth);
        let rewritten = TermRewrite::for_condition_exact(&from, &replacement).proposition(&claim);
        assert_eq!(rewritten, Proposition::condition_is(after.clone(), !truth));
    }
}
