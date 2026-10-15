// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `machine_integer_substitution_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn machine_backed_integer_substitution_scales_with_shared_dag() {
    for depth in [8, 16, 32, 64] {
        let source = SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(7)),
        );
        let mut term = IntegerTerm::Machine(source);
        for _ in 0..depth {
            term = IntegerTerm::add(term.clone(), term.clone());
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_integer(
                &term,
                Variable(7),
                &Bitvector32Term::Constant(7),
            )
        });
        assert!(
            work <= (depth + 1) * 32,
            "unexpected shared DAG work at depth {depth}: {work}"
        );
    }
}
