// Scaling tests of `src/surface/planning/proposition_search.rs` (module
// `atomic_reduction_tests`): repeated selected-premise reduction work.
use super::*;

#[test]
fn repeated_atomic_reduction_does_not_rebuild_its_selected_facts() {
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let (context, goal, id) = selection(size, Variable(785_003));
        with_simp_atomic_reduction_cache(|| {
            let (first, first_work) =
                crate::instrumentation::measure_deterministic_work(|| reduce(&context, &goal, id));
            let (again, repeated_work) =
                crate::instrumentation::measure_deterministic_work(|| reduce(&context, &goal, id));
            assert_eq!(first.0.pure_facts(), again.0.pure_facts());
            assert!(
                first
                    .0
                    .proves_atomic_for_derivation_with_id(&goal, true)
                    .0
                    .is_some()
            );
            assert!(first_work > repeated_work);
            assert!(repeated_work <= 4, "{size}: {repeated_work}");
            samples.push((size, first_work, repeated_work));
        });
    }
    eprintln!("(facts, initial reduction, repeated reduction): {samples:?}");
}

#[test]
fn repeated_unsigned_and_integer_reductions_reuse_selected_evidence() {
    let value = Bitvector32Term::Variable(Variable(786_001));
    let wide_guard = Proposition::ConditionIs(
        ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), value.clone()),
        true,
    );
    let wide_goal = Proposition::ConditionIs(
        ConditionTerm::uint64_less_than(
            Bitvector32Term::uint64_subtract(value.clone(), Bitvector32Term::UInt64Constant(1)),
            value.clone(),
        ),
        true,
    );
    let integer = |index: u64| IntegerTerm::var(Variable(786_100 + index));
    let le = |left: IntegerTerm, right: IntegerTerm| {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(left, right), true)
    };
    let eq = |left: IntegerTerm, right: IntegerTerm| {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left.into(), right.into()), true)
    };
    let cases = [
        (
            vec![
                wide_guard,
                Proposition::ConditionIs(
                    ConditionTerm::uint64_less_equal(
                        value.clone(),
                        Bitvector32Term::UInt64Constant(1000),
                    ),
                    true,
                ),
            ],
            wide_goal,
            Term::Bitvector32(value),
        ),
        (
            vec![le(integer(0), integer(1))],
            le(integer(0), integer(1)),
            Term::Integer(integer(0)),
        ),
        (
            vec![eq(integer(0), integer(1))],
            eq(integer(0), integer(1)),
            Term::Integer(integer(0)),
        ),
    ];
    for (case, (required, goal, argument)) in cases.into_iter().enumerate() {
        for size in [8, 16, 32, 64] {
            let mut context = required
                .iter()
                .cloned()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise)
                });
            for index in 0..size {
                context = context.assume_proposition(Proposition::Predicate {
                    name: format!("connected_scalar_{index}"),
                    arguments: vec![argument.clone()],
                });
            }
            let (evidence, id) = context.proves_atomic_for_derivation_with_id(&goal, true);
            let evidence = evidence
                .unwrap_or_else(|| panic!("scalar case {case} must have a valid selected proof"));
            with_simp_atomic_reduction_cache(|| {
                let first = reduce_simp_atomic_premises(
                    &goal,
                    true,
                    (context.clone(), id, evidence.clone()),
                )
                .unwrap();
                let (again, work) = crate::instrumentation::measure_deterministic_work(|| {
                    reduce_simp_atomic_premises(
                        &goal,
                        true,
                        (context.clone(), id, evidence.clone()),
                    )
                    .unwrap()
                });
                assert_eq!(first.0.pure_facts(), again.0.pure_facts());
                assert!(
                    work <= 4,
                    "{size} selected scalar facts: {work} repeated work"
                );
                let premises = RetainedPremises::from_context(&again.0);
                let retained = premises.named().to_vec();
                assert!(!retained.is_empty());
                assert!(retained.iter().all(|premise| required.contains(premise)));
                let derivation = proposition_derivation(
                    &goal,
                    PropositionDerivationRule::ContextualAtomic {
                        premises,
                        premises_id: again.1,
                        for_simp: true,
                        evidence: again.2,
                    },
                );
                assert!(derivation.check(&context));
                for missing in &retained {
                    assert!(!derivation.check(&context.without_exact_fact(missing)));
                }
            });
        }
    }
}
