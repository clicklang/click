// Scaling tests for compound scalar guards in src/kernel/spec.rs.
use super::*;

#[test]
fn compound_guard_construction_visits_each_logical_node_once() {
    for size in [16, 64, 256, 1024] {
        let mut guard = Proposition::ConditionIs(ConditionTerm::Variable(Variable(1)), true);
        for index in 1..size {
            guard = Proposition::Or(
                Box::new(guard),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Variable(Variable(index + 1)),
                    true,
                )),
            );
        }
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            conditional_spec_value(&guard, int32(7), int32(9))
        });
        assert!(value.is_some());
        assert_eq!(work, size as usize * 2 - 1, "one visit per guard node");
    }
}
