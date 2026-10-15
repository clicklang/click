// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn quantified_single_match_does_not_check_the_whole_alpha_bucket() {
    let quantified = |name: String| Proposition::ForAll {
        var: Variable(1),
        sort: Sort::CInt32,
        body: Box::new(Proposition::Exists {
            name,
            var: Variable(2),
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(1)),
                    Bitvector32Term::Variable(Variable(2)),
                ),
                true,
            )),
        }),
    };
    let goal = quantified("goal".into());
    let mut curve = Vec::new();
    for size in [8, 16, 32, 64] {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| quantified(format!("witness{i}")))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            facts.quantified_bucket_len(&quantified_equivalence_index_key(&goal).unwrap()),
            Some(size)
        );
        let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.matching_quantified_fact(&goal)
        });
        assert!(matched.is_some());
        curve.push(work);
    }
    assert!(curve[0] > 0);
    assert!(
        curve.iter().all(|work| *work == curve[0]),
        "single-match bucket work: {curve:?}"
    );
}

#[test]
fn quantified_nested_matching_work_is_linear_and_context_indexed() {
    let nested = |depth: usize, base: u64| {
        let mut p = Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(base)),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        for index in (0..depth).rev() {
            p = Proposition::ForAll {
                var: Variable(base + index as u64),
                sort: Sort::CInt32,
                body: Box::new(p),
            };
        }
        p
    };
    let mut depths = Vec::new();
    let mut contexts = Vec::new();
    for size in [8, 16, 32, 64] {
        let left = nested(size, 100);
        let right = nested(size, 1000);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            quantified_binder_equivalent(&left, &right)
        });
        assert!(matches);
        depths.push(work);
        let mut facts = ProofFacts::from_ordered(&[nested(2, 100)]);
        for index in 0..size {
            facts = facts.with_fact(Proposition::ForAll {
                var: Variable(9000),
                sort: Sort::CInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(9000)),
                        Bitvector32Term::Constant(index as u32 + 1),
                    ),
                    true,
                )),
            });
        }
        let goal = nested(2, 1000);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.matching_quantified_fact(&goal).is_some()
        });
        assert!(matches);
        contexts.push(work);
    }
    assert!(depths[0] > 0);
    for pair in depths.windows(2) {
        assert!(pair[1] <= pair[0] * 2, "binder work: {depths:?}");
    }
    assert!(
        contexts.iter().all(|work| *work == contexts[0]),
        "unrelated context work: {contexts:?}"
    );
}
