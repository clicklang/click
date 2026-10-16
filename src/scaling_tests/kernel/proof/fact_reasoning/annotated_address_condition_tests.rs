// Scaling regressions for annotated address condition checking.
use super::*;

#[test]
fn annotated_condition_lookup_and_selected_normalization_skip_unrelated_facts() {
    let _session = VerificationSession::enter();
    let source = Proposition::ConditionIs(comparison(false), false);
    let cited = Proposition::ConditionIs(comparison(true), false);
    let goal = choice(comparison(false), false);
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut premises = vec![source.clone()];
        premises.extend((0..size).map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(982_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            )
        }));
        let wrapped = |body| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Constant(true),
                    true,
                )),
                Box::new(body),
            )
        };
        for index in 0..size {
            let address = |id| Bitvector32Term::pointer_address(Pointer::symbolic(Variable(id)));
            premises.push(wrapped(Proposition::ConditionIs(
                ConditionTerm::uint64_equal(address(984_000 + index), address(985_000 + index)),
                true,
            )));
        }
        premises.push(wrapped(source.clone()));
        let target = wrapped(cited.clone());
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(facts.assumptions().decide(&comparison(true)), Some(false));
            assert!(facts.available_across_effects(&target, &ExecutionFacts::new()));
            normalize_using_conditions(&goal, std::slice::from_ref(&cited), &facts)
        });
        result.unwrap();
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] * 2),
        "{costs:?}"
    );
}
