// Scaling tests of `src/surface/checking/integer_refutation_planner.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn work_grows_linearly_with_independent_unused_premises() {
    let mut samples = Vec::new();
    for size in [8u64, 16, 32, 64] {
        let mut premises = vec![le(x(50), x(51)), le(x(51), c(3))];
        for extra in 0..size {
            premises.push(le(x(1000 + extra), c(extra as i64)));
        }
        let goal = le(x(50), c(3));
        let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_integer_refutation(&goal, &premises)
        });
        assert!(matches!(outcome, IntegerRefutation::Proved { .. }));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{samples:?}");
    }
}

#[test]
fn type_range_rows_grow_linearly_with_machine_observations() {
    use crate::kernel::{Bitvector32Term, MachineIntegerType};
    let observe = |id: u64| {
        IntegerTerm::from_machine(
            MachineIntegerType::UInt32,
            Bitvector32Term::Variable(Variable(id)),
        )
        .unwrap()
    };
    let mut samples = Vec::new();
    for size in [8u64, 16, 32, 64] {
        // `0 <= y - 1` needs `1 <= y`; every other observation brings two
        // unused type-range rows.
        let premises = vec![le(c(1), observe(60))];
        let ranges: Vec<IntegerTerm> = std::iter::once(observe(60))
            .chain((0..size).map(|extra| observe(2000 + extra)))
            .collect();
        let goal = le(c(0), IntegerTerm::subtract(observe(60), c(1)));
        let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_integer_refutation_with_ranges(&goal, &premises, &ranges)
        });
        assert!(matches!(outcome, IntegerRefutation::Proved { .. }));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{samples:?}");
    }
}
