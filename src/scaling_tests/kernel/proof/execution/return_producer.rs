use super::super::tests::bound_return_producer;
use super::*;
use crate::kernel::{OldConditionTerm, OldMachineTerm, Variable};

#[test]
fn return_producer_ignores_unrelated_history_and_facts() {
    for size in [16, 64, 256, 512] {
        let (mut core, _, mut facts) = bound_return_producer();
        for index in 0..size {
            facts = facts.with_fact(Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(1000 + index)),
                    OldMachineTerm::constant(0),
                ),
                false,
            ));
        }
        // Open the ordinary goal under its already checked root; later operations
        // must examine only their own delta, independent of root size.
        let producer = core.return_producers.get(&0).unwrap().clone();
        let mut grown = producer;
        grown.context = facts.assumptions().clone();
        grown.base = facts.clone();
        core.return_producers.insert(0, grown);
        let event = CheckedExecutionEvent::Context(Box::new(facts.assumptions().clone()));
        for _ in 0..size {
            core.execution_evidence[0].push(event.clone());
        }
        let ancestor = core.clone();
        let delta = facts.with_fact(Proposition::condition_is(
            OldConditionTerm::Constant(false),
            false,
        ));
        let (((), work), indexed) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                core.retain_return_facts(0, &delta).unwrap();
            })
        });
        assert!(work <= 64, "{size}: {work} work");
        assert!(indexed <= 128, "{size}: {indexed} index work");
        assert!(ancestor.return_producers.get(&0).is_some());
    }
}
