use super::*;
use crate::kernel::VerificationSession;

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}
fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Bitvector32Term {
    Bitvector32Term::ClickFunctionApplication {
        name: name.into(),
        arguments,
    }
}
fn scalar(term: Bitvector32Term) -> PureFunctionArgument {
    PureFunctionArgument::Value(CValue::Int32(term))
}
fn eq(a: Bitvector32Term, b: Bitvector32Term) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::equal(a, b), true)
}
fn pointer(name: &str) -> Pointer {
    Pointer {
        block: name.into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn array(memory: &CMemory, p: Pointer, element_type: CType) -> PureFunctionArgument {
    PureFunctionArgument::ArrayRef {
        memory: memory.clone(),
        pointer: CValue::Pointer(CPointerValue::new(p, CType::Int32Pointer)),
        element_type,
    }
}

#[test]
fn fact_lookup_uses_late_equalities_through_nested_applications() {
    let f = |x| call("f", vec![scalar(x)]);
    let g = |x| call("g", vec![scalar(f(x))]);
    let held = eq(g(var(1)), var(3));
    let required = eq(g(var(2)), var(4));
    let context = PureFactContext::new().assume_proposition(held);
    assert!(!context.contains_known(&required));
    let context = context
        .assume_proposition(eq(var(1), var(2)))
        .assume_proposition(eq(var(3), var(4)));
    assert!(context.contains_known(&required));
    assert!(!context.contains_assumed_exact(&required));
    assert!(!context.contains_known(&eq(call("other", vec![scalar(f(var(2)))]), var(4))));
    assert!(!context.contains_known(&eq(var(1), var(3)))); // no injectivity
}

#[test]
fn fact_lookup_transports_comparisons_and_negative_facts_without_arithmetic_search() {
    let held = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(10), var(11)), false);
    let required =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(var(12), var(13)), false);
    let context = PureFactContext::new()
        .assume_proposition(held)
        .assume_proposition(eq(var(10), var(12)))
        .assume_proposition(eq(var(11), var(13)));
    assert!(context.contains_known(&required));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(var(12), var(13)),
        true
    )));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(var(12), var(13)),
        false
    )));
}

#[test]
fn fact_lookup_preserves_branch_withdrawal_restriction_and_replacement() {
    let source = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(20), var(21)), true);
    let target = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(22), var(21)), true);
    let alias = eq(var(20), var(22));
    let parent = PureFactContext::new().assume_proposition(source.clone());
    let child = parent.clone().assume_proposition(alias.clone());
    assert!(child.contains_known(&target));
    assert!(!parent.contains_known(&target));
    assert!(!child.without_exact_fact(&alias).contains_known(&target));
    assert!(!child.without_exact_fact(&source).contains_known(&target));
    assert!(
        !child
            .restricted_to_facts(
                &[(ConditionTerm::signed_less_than(var(20), var(21)), true)],
                &[]
            )
            .contains_known(&target)
    );
    let replaced = child.assume_condition(ConditionTerm::signed_less_than(var(20), var(21)), false);
    assert!(!replaced.contains_known(&source));
    assert!(!replaced.contains_known(&target));
}

#[test]
fn pure_application_arguments_keep_snapshots_types_and_argument_order() {
    let _session = VerificationSession::enter();
    let memory = CMemory::new().with_block("p", 4).with_block("q", 4);
    let changed = memory.clone().store(pointer("p"), CValue::Int32(var(34)));
    let f = |memory: &CMemory, p, ty| call("f", vec![array(memory, p, ty)]);
    let held = eq(f(&memory, pointer("p"), CType::Int32), var(30));
    let context = PureFactContext::new()
        .assume_proposition(held)
        .assume_condition(
            ConditionTerm::PointerEqual(Box::new(pointer("p")), Box::new(pointer("q"))),
            true,
        );
    assert!(context.contains_known(&eq(f(&memory, pointer("q"), CType::Int32), var(30))));
    assert!(!context.contains_known(&eq(f(&changed, pointer("q"), CType::Int32), var(30))));
    assert!(!context.contains_known(&eq(f(&memory, pointer("q"), CType::UInt32), var(30))));
    let lhs = call("pair", vec![scalar(var(31)), scalar(var(32))]);
    let rhs = call("pair", vec![scalar(var(32)), scalar(var(31))]);
    assert!(!context.contains_known(&eq(lhs, rhs)));
}

#[test]
fn fact_congruence_keeps_predicate_truth_out_of_resource_equality_history() {
    let mut base = EqualityGraph::default();
    let condition = ConditionTerm::signed_less_than(var(40), var(41));
    base.add_condition(&condition, true);
    let mut derived = base.clone();
    let mut child = base.clone();
    child.add_int32_equality(&var(40), &var(42));
    let value_checkpoint = child.input_key();
    child.add_condition(&ConditionTerm::signed_less_than(var(42), var(43)), false);
    assert!(value_checkpoint == child.input_key());
    assert!(child.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(derived.append_inputs_from(&child));
    assert!(!derived.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(!base.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(derived.knows_condition(&ConditionTerm::signed_less_than(var(42), var(41)), true));
    assert!(!base.knows_condition(&ConditionTerm::signed_less_than(var(42), var(41)), true));
}

#[test]
fn fact_lookup_does_not_scan_unrelated_facts() {
    let mut costs = Vec::new();
    for size in [32, 128, 512, 2048] {
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context
                .assume_proposition(eq(call("f", vec![scalar(var(100 + i))]), var(10000 + i)));
        }
        context = context.assume_proposition(eq(var(100), var(50000)));
        let required = eq(call("f", vec![scalar(var(50000))]), var(10000));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(context.contains_known(&required));
            })
        });
        costs.push((work, map_work));
    }
    eprintln!("fact lookup costs: {costs:?}");
    // Fourfold ambient growth adds only index height, not a fact scan.
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn fact_lookup_uses_pointer_read_congruence_after_a_late_address_alias() {
    let _session = VerificationSession::enter();
    let memory = intern_c_memory(CMemory::new());
    let a = Pointer::symbolic(Variable(72));
    let b = Pointer::symbolic(Variable(73));
    let f = |address: &Pointer| {
        call(
            "tag",
            vec![PureFunctionArgument::Value(CValue::Pointer(
                CPointerValue::new(Pointer::loaded_value(&memory, address), CType::Int32Pointer),
            ))],
        )
    };
    let source = eq(f(&a), var(71));
    let target = eq(f(&b), var(71));
    let context = PureFactContext::new().assume_proposition(source.clone());
    assert!(!context.contains_known(&target));
    let alias = Proposition::ConditionIs(ConditionTerm::pointer_equal(a, b), true);
    let context = context.assume_proposition(alias.clone());
    assert!(context.contains_known(&target));
    assert!(!context.without_exact_fact(&alias).contains_known(&target));
    assert!(!context.without_exact_fact(&source).contains_known(&target));
}

#[test]
fn nested_application_registration_and_late_merge_scale_with_expression_size() {
    let mut costs = Vec::new();
    for size in [8usize, 32, 128, 512] {
        let nested = |mut value| {
            for _ in 0..size {
                value = call("nested", vec![scalar(value)]);
            }
            value
        };
        let a = nested(var(81));
        let b = nested(var(82));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_int32_equal(&a, &b));
                graph.add_int32_equality(&var(81), &var(82));
                assert!(graph.are_int32_equal(&a, &b));
            })
        });
        costs.push((size, work, map_work));
    }
    for sample in &costs[1..] {
        let base = costs[0];
        assert!(sample.1 <= base.1 * (sample.0 / base.0) * 2, "{costs:?}");
        assert!(
            sample.2
                <= base.2 * (sample.0 / base.0) * (sample.0.ilog2() as usize + 1)
                    / (base.0.ilog2() as usize + 1)
                    * 2,
            "{costs:?}"
        );
    }
}
