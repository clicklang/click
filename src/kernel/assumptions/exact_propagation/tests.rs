use super::*;

fn atom(name: &str) -> Proposition {
    Proposition::Predicate {
        name: name.into(),
        arguments: vec![],
    }
}
fn not(p: Proposition) -> Proposition {
    Proposition::Not(Box::new(p))
}
fn or(a: Proposition, b: Proposition) -> Proposition {
    Proposition::Or(Box::new(a), Box::new(b))
}
fn and(a: Proposition, b: Proposition) -> Proposition {
    Proposition::And(Box::new(a), Box::new(b))
}
fn implies(a: Proposition, b: Proposition) -> Proposition {
    Proposition::Implies(Box::new(a), Box::new(b))
}
fn context(facts: Vec<Proposition>) -> PureFactContext {
    facts
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
}

#[test]
fn exact_propagation_handles_both_admission_orders_and_polarities() {
    let (a, b, c) = (atom("a"), atom("b"), atom("c"));
    for (rule, trigger, result) in [
        (or(a.clone(), b.clone()), not(a.clone()), b.clone()),
        (or(a.clone(), b.clone()), not(b.clone()), a.clone()),
        (implies(a.clone(), b.clone()), a.clone(), b.clone()),
        (
            implies(a.clone(), b.clone()),
            not(b.clone()),
            not(a.clone()),
        ),
        (
            or(not(a.clone()), not(b.clone())),
            a.clone(),
            not(b.clone()),
        ),
    ] {
        for facts in [
            vec![rule.clone(), trigger.clone()],
            vec![trigger.clone(), rule.clone()],
        ] {
            let ctx = context(facts);
            assert!(ctx.contains_known(&result), "{rule:?}, {trigger:?}");
            assert!(!ctx.contains_known(&c));
        }
        assert!(!context(vec![rule]).contains_known(&result));
    }
}

#[test]
fn exact_propagation_chains_conjunctive_guards_and_multiple_disjuncts() {
    let (a, b, c, d) = (atom("a"), atom("b"), atom("c"), atom("d"));
    let parent = context(vec![
        implies(and(a.clone(), b.clone()), c.clone()),
        or(not(c.clone()), d.clone()),
        a.clone(),
    ]);
    assert!(!parent.contains_known(&c));
    assert!(!parent.contains_known(&d));
    let child = parent.clone().assume_proposition(b.clone());
    assert!(child.contains_known(&c));
    assert!(child.contains_known(&d));
    assert!(!parent.contains_known(&c));
    assert!(!parent.contains_known(&d));
    for facts in [
        vec![
            or(or(a.clone(), b.clone()), c.clone()),
            not(a.clone()),
            not(b.clone()),
        ],
        vec![
            not(b.clone()),
            not(a.clone()),
            or(a.clone(), or(b.clone(), c.clone())),
        ],
    ] {
        assert!(context(facts).contains_known(&c));
    }
    let restored = child
        .pure_facts()
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    assert!(restored.contains_known(&d));
    assert!(
        !child
            .restricted_to_facts(&[], &[implies(a.clone(), b.clone())])
            .contains_known(&b)
    );
    assert!(
        child
            .restricted_to_facts(&[], &[implies(a.clone(), b.clone()), a])
            .contains_known(&b)
    );
}

#[test]
fn exact_propagation_is_idempotent_and_does_not_fire_cycles_without_a_seed() {
    let (a, b) = (atom("a"), atom("b"));
    let parent = context(vec![
        implies(a.clone(), b.clone()),
        implies(b.clone(), a.clone()),
    ]);
    assert!(!parent.contains_known(&a));
    assert!(!parent.contains_known(&b));
    let child = parent.clone().assume_proposition(a.clone());
    assert!(child.contains_known(&b));
    let repeated = child.clone().assume_proposition(a);
    assert_eq!(
        child.exact_propagation.next_clause,
        repeated.exact_propagation.next_clause
    );
    assert!(!parent.contains_known(&b));
    assert!(context(vec![or(b.clone(), b.clone())]).contains_known(&b));
}

#[test]
fn exact_propagation_keeps_condition_polarity_and_restriction_support() {
    let a = ConditionTerm::Variable(crate::kernel::Variable(780_000));
    let b = atom("result");
    let rule = or(Proposition::condition_is(a.clone(), true), b.clone());
    let parent = context(vec![rule.clone()]);
    let child = parent.clone().assume_condition(a.clone(), false);
    assert!(child.contains_known(&b));
    assert!(!parent.contains_known(&b));
    assert!(
        !child
            .restricted_to_facts(&[(a.clone(), true)], std::slice::from_ref(&rule))
            .contains_known(&b)
    );
    assert!(
        child
            .restricted_to_facts(&[(a, false)], &[rule])
            .contains_known(&b)
    );
}

#[test]
fn exact_propagation_does_not_match_different_memory_states_or_types() {
    use crate::kernel::*;
    let pointer = Address {
        base: "propagation-cell".into(),
        offset: AddressOffset::Constant(0),
    };
    let before = SymbolicMemory::new()
        .with_block("propagation-cell", 4)
        .store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(781_000))),
        );
    let after = before.clone().store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(781_001))),
    );
    let read = |memory| {
        Proposition::condition_is(
            ConditionTerm::equal(
                OldMachineTerm::read_named(
                    ProgramPoint::at(&intern_memory(memory)),
                    Box::new(pointer.clone()),
                    LoadKind::Int32,
                ),
                OldMachineTerm::constant(0),
            ),
            true,
        )
    };
    let goal = atom("goal");
    let rule = implies(read(before.clone()), goal.clone());
    assert!(!context(vec![rule.clone(), read(after)]).contains_known(&goal));
    assert!(context(vec![rule, read(before)]).contains_known(&goal));
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/assumptions/exact_propagation.rs");
}

#[test]
fn exact_propagation_preserves_models_of_nested_boolean_formulas() {
    fn eval(p: &Proposition, assignment: usize) -> bool {
        match p {
            Proposition::Predicate { name, .. } => {
                assignment & (1 << name.parse::<usize>().unwrap()) != 0
            }
            condition_source_0 @ Proposition::ConditionIs(_, b)
                if let Some((ConditionTerm::Constant(a), _)) =
                    condition_source_0.condition_native() =>
            {
                a == b
            }
            Proposition::Not(p) => !eval(p, assignment),
            Proposition::And(a, b) => eval(a, assignment) && eval(b, assignment),
            Proposition::Or(a, b) => eval(a, assignment) || eval(b, assignment),
            Proposition::Implies(a, b) => !eval(a, assignment) || eval(b, assignment),
            _ => panic!("unexpected proposition"),
        }
    }
    let (a, b, c) = (atom("0"), atom("1"), atom("2"));
    let pieces = [
        a.clone(),
        not(a.clone()),
        and(a.clone(), b.clone()),
        or(a.clone(), b.clone()),
        implies(a.clone(), b.clone()),
    ];
    for left in &pieces {
        for right in &pieces {
            for source in [
                and(left.clone(), right.clone()),
                or(left.clone(), right.clone()),
                implies(left.clone(), right.clone()),
                not(implies(left.clone(), right.clone())),
                implies(and(left.clone(), b.clone()), c.clone()),
            ] {
                for mask in 0..27 {
                    let mut encoded = mask;
                    let mut premises = vec![source.clone()];
                    for name in ["0", "1", "2"] {
                        match encoded % 3 {
                            1 => premises.push(atom(name)),
                            2 => premises.push(not(atom(name))),
                            _ => {}
                        }
                        encoded /= 3;
                    }
                    let mut index = Index::default();
                    let mut pending = premises.clone();
                    while let Some(fact) = pending.pop() {
                        pending.extend(index.admit(&fact));
                    }
                    for model in 0..8 {
                        if premises.iter().all(|p| eval(p, model)) {
                            assert!(
                                index.known.iter().all(|p| eval(&p.proposition, model)),
                                "unsound consequence for {premises:?}, model {model}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn exact_propagation_publishes_whole_composite_conclusions() {
    let (a, b, c) = (atom("a"), atom("b"), atom("c"));
    for result in [or(b.clone(), c.clone()), implies(b.clone(), c.clone())] {
        for source in [
            implies(a.clone(), result.clone()),
            or(not(a.clone()), result.clone()),
        ] {
            let ctx = context(vec![source, a.clone()]);
            assert!(
                ctx.contains_known(&result),
                "lost whole conclusion: {result:?}"
            );
            assert!(!ctx.contains_known(&b));
            assert!(!ctx.contains_known(&c));
        }
    }
}

#[test]
fn exact_propagation_does_not_match_distinct_numeric_carriers() {
    use crate::kernel::*;
    let narrow = Proposition::Predicate {
        name: "typed".into(),
        arguments: vec![Term::ProgramValue(
            (ProgramValue::Int32(OldMachineTerm::constant(0))).into(),
        )],
    };
    let wide = Proposition::Predicate {
        name: "typed".into(),
        arguments: vec![Term::ProgramValue(
            (ProgramValue::UInt64(OldMachineTerm::uint64_constant(0))).into(),
        )],
    };
    let result = atom("result");
    let rule = implies(narrow.clone(), result.clone());
    assert!(!context(vec![rule.clone(), wide]).contains_known(&result));
    assert!(context(vec![rule, narrow]).contains_known(&result));
}

#[test]
fn exact_propagation_forks_with_pending_work_do_not_inherit_the_drain_guard() {
    let (a, b, c) = (atom("a"), atom("b"), atom("c"));
    let mut parent = context(vec![implies(a.clone(), b.clone())]);
    // Model a context fork inside an admission helper while the outer queue
    // is still being drained. The admitted fact is already in the fact store.
    parent.exact_propagation.draining = true;
    parent = parent.assume_proposition(a);
    let child = parent.clone().assume_proposition(c);
    assert!(child.contains_known(&b));
    assert!(!parent.contains_known(&b));
}

#[test]
fn exact_propagation_records_conflicts_without_contaminating_siblings() {
    let a = atom("a");
    let root = context(vec![a.clone()]);
    let child = root.clone().assume_proposition(not(a));
    assert!(child.is_inconsistent());
    assert!(!root.is_inconsistent());
    assert!(!root.restricted_to_facts(&[], &[]).is_inconsistent());
}

#[test]
fn exact_propagation_does_not_use_equality_derived_guards() {
    use crate::kernel::*;
    let a = OldMachineTerm::Variable(Variable(782_000));
    let b = OldMachineTerm::Variable(Variable(782_001));
    let guard = ConditionTerm::equal(b.clone(), OldMachineTerm::constant(0));
    let result = atom("result");
    let ctx = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(a.clone(), b), true)
        .assume_condition(ConditionTerm::equal(a, OldMachineTerm::constant(0)), true)
        .assume_proposition(implies(
            Proposition::condition_is(guard.clone(), true),
            result.clone(),
        ));
    assert_eq!(ctx.decide(&guard), Some(true));
    assert!(!ctx.contains_known(&result));
    assert!(ctx.assume_condition(guard, true).contains_known(&result));
}

#[test]
fn exact_propagation_uses_only_intrinsic_literal_and_reflexive_truths() {
    use crate::kernel::*;
    let x = OldMachineTerm::Variable(Variable(782_010));
    let result = atom("result");
    for guard in [
        ConditionTerm::equal(x.clone(), x.clone()),
        ConditionTerm::signed_less_equal(OldMachineTerm::constant(0), OldMachineTerm::constant(7)),
        ConditionTerm::integer_less_equal(
            IntegerTerm::constant_i64(0),
            IntegerTerm::constant_i64(7),
        ),
    ] {
        assert!(
            context(vec![implies(
                Proposition::condition_is(guard.clone(), true),
                result.clone()
            )])
            .contains_known(&result)
        );
        assert!(
            !context(vec![implies(
                Proposition::condition_is(guard, false),
                result.clone()
            )])
            .contains_known(&result)
        );
    }
}

#[test]
fn exact_propagation_matches_native_observation_guards_at_both_polarities() {
    use crate::kernel::*;
    let x = OldMachineTerm::Variable(Variable(782_020));
    let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, x.clone()).unwrap();
    let integer = ConditionTerm::integer_less_equal(IntegerTerm::constant_i64(0), observed.clone());
    let native = ConditionTerm::signed_less_equal(OldMachineTerm::constant(0), x.clone());
    let result = atom("result");
    for (integer, native) in [
        (integer, native),
        (
            ConditionTerm::integer_greater_equal(observed, IntegerTerm::constant_i64(0)),
            ConditionTerm::signed_greater_equal(x, OldMachineTerm::constant(0)),
        ),
    ] {
        for truth in [true, false] {
            let original = Proposition::condition_is(integer.clone(), truth);
            let propagated = context(vec![implies(atom("seed"), original.clone()), atom("seed")]);
            assert!(
                propagated.contains_assumed_exact(&original),
                "propagation must retain the clause's source spelling"
            );
            let guard = Proposition::condition_is(integer.clone(), truth);
            let fact = Proposition::condition_is(native.clone(), truth);
            let rule = implies(guard, result.clone());
            for facts in [vec![rule.clone(), fact.clone()], vec![fact, rule.clone()]] {
                assert!(context(facts).contains_known(&result));
            }
            assert!(
                !context(vec![
                    rule,
                    Proposition::condition_is(native.clone(), !truth)
                ])
                .contains_known(&result)
            );
        }
    }
}

#[test]
fn exact_propagation_matches_value_preserving_observation_conversions() {
    use crate::kernel::*;
    use MachineIntegerType as M;
    let x = OldMachineTerm::Variable(Variable(782_030));
    let y = OldMachineTerm::Variable(Variable(782_031));
    let widened = OldMachineTerm::machine_integer_cast(M::Int32, M::Int64, x.clone());
    let guard = Proposition::condition_is(
        ConditionTerm::integer_less_than(
            IntegerTerm::from_machine(M::Int64, widened).unwrap(),
            IntegerTerm::from_machine(M::Int32, y.clone()).unwrap(),
        ),
        true,
    );
    let fact =
        Proposition::condition_is(ConditionTerm::signed_less_than(x.clone(), y.clone()), true);
    let result = atom("converted_result");
    assert!(context(vec![implies(guard, result.clone()), fact.clone()]).contains_known(&result));
    let wrapping = OldMachineTerm::machine_integer_cast(M::Int32, M::UInt64, x);
    let different = Proposition::condition_is(
        ConditionTerm::integer_less_than(
            IntegerTerm::from_machine(M::UInt64, wrapping).unwrap(),
            IntegerTerm::from_machine(M::Int32, y).unwrap(),
        ),
        true,
    );
    assert!(!context(vec![implies(different, result.clone()), fact]).contains_known(&result));
}

#[test]
fn exact_propagation_matches_retained_and_native_arithmetic_operands() {
    use crate::kernel::*;
    use MachineIntegerType as M;
    let _session = VerificationSession::enter();
    let variable = |id| OldMachineTerm::Variable(Variable(id));
    let root = |id| KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(id));
    let subtract = KernelTerm::machine_binary_shared(
        M::Int32,
        MachineBinaryOp::Subtract,
        [root(782041), root(782042)],
    );
    let retained =
        IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(M::Int32, subtract).unwrap());
    let guard = Proposition::condition_is(
        ConditionTerm::integer_less_than(
            IntegerTerm::from_machine(M::Int32, variable(782040)).unwrap(),
            retained,
        ),
        true,
    );
    let native = Proposition::condition_is(
        ConditionTerm::signed_less_than(
            variable(782040),
            OldMachineTerm::machine_binary(
                M::Int32,
                MachineBinaryOp::Subtract,
                variable(782041),
                variable(782042),
            ),
        ),
        true,
    );
    let result = atom("retained_result");
    let rule = implies(guard, result.clone());
    for facts in [
        vec![rule.clone(), native.clone()],
        vec![native.clone(), rule.clone()],
    ] {
        let ctx = context(facts);
        assert!(ctx.contains_known(&result));
        assert!(ctx.contains_assumed_exact(&native));
    }
    let different = Proposition::condition_is(
        ConditionTerm::signed_less_than(
            variable(782040),
            OldMachineTerm::machine_binary(
                M::Int32,
                MachineBinaryOp::Add,
                variable(782041),
                variable(782042),
            ),
        ),
        true,
    );
    assert!(!context(vec![rule, different]).contains_known(&result));
}

#[test]
fn exact_propagation_computes_substituted_word_equality_guards() {
    use crate::kernel::*;
    let result = atom("result");
    for (right, equal) in [(0, false), (1, true), (2, false)] {
        let comparison = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::uint64_constant(1)),
            right: Box::new(OldMachineTerm::int64_constant(right)),
        };
        for truth in [true, false] {
            let guard = Proposition::condition_is(comparison.clone(), truth);
            let facts = context(vec![implies(guard, result.clone())]);
            assert_eq!(facts.contains_known(&result), equal == truth);
        }
    }
    // A width mismatch is not an intrinsic equality, even for equal bits.
    let mismatched = ConditionTerm::Compare {
        format: MachineIntegerType::Int64,
        relation: CompareRelation::Equal,
        left: Box::new(OldMachineTerm::constant(1)),
        right: Box::new(OldMachineTerm::int64_constant(1)),
    };
    assert_eq!(
        crate::kernel::proof::fact_reasoning::trivial_condition_value(&mismatched),
        None
    );
}
