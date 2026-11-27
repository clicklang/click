// Scaling tests for compound scalar guards in src/kernel/spec.rs.
use super::*;

#[test]
fn compound_guard_construction_and_native_output_scale_linearly() {
    let mut previous = None;
    let mut unit_cost = None;
    for size in [16, 64, 256, 1024] {
        let mut guard = Proposition::condition_is(OldConditionTerm::Variable(Variable(1)), true);
        for index in 1..size {
            guard = Proposition::Or(
                Box::new(guard),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Variable(Variable(index + 1)),
                    true,
                )),
            );
        }
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            conditional_spec_value(&guard, int32(7), int32(9))
        });
        assert!(value.is_some());
        assert_eq!(
            work,
            size as usize * 2 - 1,
            "one native visit per guard node"
        );
        let exports = KernelTermExport::machine_export_count();
        let (value, work) =
            crate::instrumentation::measure_deterministic_work(|| conditional_guard(&guard));
        assert!(value.unwrap().0.root().is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 32 * size as usize, "size={size} work={work}");
        if let Some((last_size, last_work)) = previous {
            let added = (size - last_size) as usize;
            let cost = *unit_cost.get_or_insert((work - last_work) / added);
            assert_eq!(work - last_work, added * cost, "size={size}");
        }
        previous = Some((size, work));
    }
}

#[test]
fn recognizing_a_single_condition_does_not_visit_the_operand_tree() {
    let _session = crate::kernel::VerificationSession::enter();
    let yes = KernelTerm::boolean_literal(true);
    let no = KernelTerm::boolean_literal(false);
    let mut previous_work = None;
    for size in [8, 32, 128, 512] {
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(10997351));
        for _ in 0..size {
            root = KernelTerm::boolean_if_raw([root, yes.clone(), no.clone()]);
        }
        let claim = Proposition::Not(Box::new(Proposition::condition_is(
            StoredConditionTerm::from_root(root.clone()).unwrap(),
            true,
        )));
        let (recognized, work) = crate::instrumentation::measure_deterministic_work(|| {
            is_single_normalization_condition(&claim)
        });
        assert!(recognized);
        assert!(!root.has_cached_native_argument());
        if let Some(previous) = previous_work {
            assert_eq!(work, previous);
        }
        previous_work = Some(work);
    }
}
