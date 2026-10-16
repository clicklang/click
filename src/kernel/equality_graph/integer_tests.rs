use super::algebraic_tests::{model_type, variable};
use super::*;
use crate::kernel::{IntegerTerm as I, MachineIntegerType as M, SharedIntegerTerm};

fn cached(model: &AlgebraicTerm) -> I {
    I::from_machine(
        M::Int32,
        Bitvector32Term::ClickFunctionApplication {
            name: "cached".into(),
            arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
        },
    )
    .unwrap()
}
fn count(model: &AlgebraicTerm) -> I {
    I::add(I::constant_i64(1), cached(model))
}
fn eq(a: I, b: I) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::integer_equal(a, b), true)
}
fn alias(a: &AlgebraicTerm, b: &AlgebraicTerm) -> Proposition {
    Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
}

#[test]
fn integer_count_facts_follow_early_and_late_model_aliases_and_withdrawal() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("IntegerModel", AlgebraicValueType::C(CType::Int32));
    let a = variable(&ty, 920_101);
    let b = variable(&ty, 920_102);
    let same = alias(&a, &b);
    let total = I::Variable(Variable(920_103));
    let premise = eq(total.clone(), count(&a));
    let goal = eq(total, count(&b));
    for early in [false, true] {
        let mut context = PureFactContext::new();
        if early {
            context = context.assume_proposition(same.clone());
        }
        context = context.assume_proposition(premise.clone());
        if !early {
            assert!(!context.contains_known(&goal));
            context = context.assume_proposition(same.clone());
        }
        assert!(context.contains_known(&goal));
        assert!(!context.without_exact_fact(&same).contains_known(&goal));
        assert!(!context.without_exact_fact(&premise).contains_known(&goal));
        assert!(
            !context
                .with_only_proposition_facts(&[])
                .contains_known(&goal)
        );
    }
}

fn operations(x: &SharedIntegerTerm) -> Vec<I> {
    let two: SharedIntegerTerm = I::constant_i64(2).into();
    vec![
        I::Negate(x.clone()),
        I::Add(x.clone(), two.clone()),
        I::Subtract(x.clone(), two.clone()),
        I::Multiply(x.clone(), two.clone()),
        I::TruncatingQuotient(x.clone(), two.clone()),
        I::TruncatingRemainder(x.clone(), two),
    ]
}

#[test]
fn integer_value_aliases_reach_operations_calls_and_input_checkpoints() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: SharedIntegerTerm = I::Variable(Variable(920_111)).into();
    let y: SharedIntegerTerm = I::Variable(Variable(920_112)).into();
    let mut graph = EqualityGraph::default();
    for (a, b) in operations(&x).iter().zip(operations(&y).iter()) {
        assert!(!graph.are_integer_equal(a, b));
    }
    let sibling = graph.clone();
    let mut checkpoint = graph.input_root();
    graph.add_condition(&ConditionTerm::IntegerEqual(x.clone(), y.clone()), true);
    assert!(checkpoint.append_inputs_from(&graph));
    let call = |value: I| {
        I::PureFunctionApplication(SharedPureApplication::intern(
            "integer_call".into(),
            vec![PureFunctionArgument::Integer(value.into())],
        ))
    };
    for (a, b) in operations(&x).into_iter().zip(operations(&y)) {
        assert!(graph.are_integer_equal(&a, &b));
        assert!(graph.are_integer_equal(&call(a.clone()), &call(b.clone())));
        assert!(checkpoint.are_integer_equal(&a, &b));
        assert!(!sibling.are_integer_equal(&a, &b));
    }
    assert!(!graph.are_integer_equal(&operations(&x)[0], &operations(&x)[1]));
}

#[test]
fn integer_order_truth_follows_aliases_without_merging_unrelated_true_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: SharedIntegerTerm = I::Variable(Variable(920_121)).into();
    let y: SharedIntegerTerm = I::Variable(Variable(920_122)).into();
    for make in [
        ConditionTerm::IntegerLessThan,
        ConditionTerm::IntegerLessEqual,
        ConditionTerm::IntegerGreaterThan,
        ConditionTerm::IntegerGreaterEqual,
        ConditionTerm::IntegerNotEqual,
    ] {
        for value in [true, false] {
            let mut graph = EqualityGraph::default();
            let goal = make(y.clone(), I::constant_i64(5).into());
            graph.add_condition(&make(x.clone(), I::constant_i64(5).into()), value);
            assert!(!graph.knows_condition(&goal, value));
            graph.add_integer_equality(&x, &y);
            assert!(graph.knows_condition(&goal, value));
            assert!(!graph.are_integer_equal(&I::constant_i64(5), &I::constant_i64(6)));
        }
    }
}

#[test]
fn integer_observations_keep_machine_types_and_read_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let bits = Bitvector32Term::Variable(Variable(920_131));
    let signed = I::from_machine(M::Int32, bits.clone()).unwrap();
    let unsigned = I::from_machine(M::UInt32, bits).unwrap();
    let graph = EqualityGraph::default();
    assert!(!graph.are_integer_equal(&signed, &unsigned));
    let p = Pointer::symbolic(Variable(920_132));
    let before = intern_c_memory(
        CMemory::new().store(p.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
    );
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(p.clone(), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let read = |memory| {
        I::from_machine(
            M::Int32,
            Bitvector32Term::MemoryLoad(memory, Box::new(p.clone()), LoadKind::Bits32),
        )
        .unwrap()
    };
    assert!(!graph.are_integer_equal(&read(before), &read(after)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/integer_tests.rs");
}
