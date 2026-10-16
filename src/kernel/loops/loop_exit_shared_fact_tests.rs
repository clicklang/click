use super::*;
use std::cell::Cell;

fn fact(variable: u64, value: i64) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(variable))),
            Box::new(Bitvector32Term::Constant(value as _)),
        ),
        true,
    )
}

fn exit(restated: Vec<Proposition>) -> LoopExitFacts {
    LoopExitFacts {
        stated: Vec::new().into(),
        disjunct: Vec::new(),
        restated,
        successor_equations: Vec::new(),
        obligations: Vec::new(),
        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    }
}

fn kept(exits: &[LoopExitFacts]) -> Vec<Proposition> {
    facts_every_exit_restates(exits, &[])
        .into_iter()
        .map(|fact| fact.proposition().clone())
        .collect()
}

#[test]
fn merged_exit_equations_are_available_without_historical_guards() {
    let fresh = CValue::Int32(Bitvector32Term::Variable(Variable(100)));
    let make = |value: u32, guard: i64| {
        let mut restatement = LoopExitRestatement::default();
        restatement.pin(&fresh, &CValue::Int32(Bitvector32Term::Constant(value)));
        restatement.restate(
            vec![ExecutionPureFact::new(fact(1, guard))].into(),
            Vec::new(),
            crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )
    };
    let expected = Proposition::Or(Box::new(fact(100, 7)), Box::new(fact(100, 9)));
    let (facts, _, _) = join_loop_exit_paths(vec![make(7, 0), make(9, 1)]).unwrap();
    assert!(facts.iter().any(|fact| fact.proposition() == &expected));
    assert!(
        !facts
            .iter()
            .any(|entry| entry.proposition() == &fact(100, 7))
    );
    assert!(
        !facts
            .iter()
            .any(|entry| entry.proposition() == &fact(100, 9))
    );
    // An exit with no equation cannot be silently omitted from the join.
    let unknown = LoopExitFacts::unabstracted(
        vec![ExecutionPureFact::new(fact(1, 2))].into(),
        Vec::new(),
        crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    );
    let (facts, _, _) = join_loop_exit_paths(vec![make(7, 0), unknown]).unwrap();
    assert!(!facts.iter().any(|entry| entry.proposition() == &expected));
    assert!(
        !facts
            .iter()
            .any(|entry| entry.proposition() == &fact(100, 7))
    );
}

/// A fact is kept only when every exit restates that very proposition.
#[test]
fn only_a_fact_every_exit_restates_is_kept() {
    let merged = 7_000_001;
    // Every exit restates it: kept once, in the first exit's order.
    assert_eq!(
        kept(&[
            exit(vec![fact(merged, 1), fact(merged, 2), fact(merged, 1)]),
            exit(vec![fact(merged, 2), fact(merged, 1)]),
            exit(vec![fact(merged, 1), fact(merged, 2), fact(merged, 3)]),
        ]),
        vec![fact(merged, 1), fact(merged, 2)],
    );
    // All but one exit restate it.
    assert!(
        kept(&[
            exit(vec![fact(merged, 1)]),
            exit(vec![fact(merged, 1)]),
            exit(vec![fact(merged, 2)]),
        ])
        .is_empty()
    );
    // An exit that restates nothing keeps nothing, whichever it is.
    assert!(kept(&[exit(vec![fact(merged, 1)]), exit(Vec::new())]).is_empty());
    assert!(kept(&[exit(Vec::new()), exit(vec![fact(merged, 1)])]).is_empty());
    // The same words about different symbols are different facts: each
    // exit's own name for something (an arm binding, say) is not shared.
    assert!(
        kept(&[
            exit(vec![fact(7_000_010, 1)]),
            exit(vec![fact(7_000_011, 1)]),
        ])
        .is_empty()
    );
    // A fact the exits already share as stated is not added again.
    let shared = [ExecutionPureFact::new(fact(merged, 1))];
    assert!(
        facts_every_exit_restates(
            &[exit(vec![fact(merged, 1)]), exit(vec![fact(merged, 1)])],
            &shared,
        )
        .is_empty()
    );
}

/// The intersection is one indexing pass per exit and one lookup pass
/// over the first exit's facts: its comparisons grow with the exits
/// times the facts times a logarithm, along either axis, and never with
/// the square of either.
#[test]
fn facts_in_every_exit_cost_exits_times_facts() {
    #[derive(Eq)]
    struct Counted<'a>(usize, &'a Cell<usize>);
    impl PartialEq for Counted<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.cmp(other).is_eq()
        }
    }
    impl PartialOrd for Counted<'_> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Counted<'_> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.1.set(self.1.get() + 1);
            self.0.cmp(&other.0)
        }
    }
    for (exits, facts) in [
        (4usize, 64usize),
        (16, 64),
        (64, 64),
        (256, 64),
        (8, 16),
        (8, 64),
        (8, 256),
        (8, 1024),
    ] {
        let comparisons = Cell::new(0);
        let sets = (0..exits)
            .map(|_| {
                (0..facts)
                    .rev()
                    .map(|fact| Counted(fact, &comparisons))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let positions =
            positions_in_every_set(sets[0].iter(), sets[1..].iter().map(|set| set.iter()));
        assert_eq!(positions.len(), facts);
        assert!(
            comparisons.get() <= 4 * exits * facts * (facts.ilog2() as usize + 1),
            "{exits} exits of {facts} facts: {} comparisons",
            comparisons.get()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/loop_exit_shared_fact_tests.rs");
}
