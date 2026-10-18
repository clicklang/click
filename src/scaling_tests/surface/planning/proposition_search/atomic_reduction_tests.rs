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
