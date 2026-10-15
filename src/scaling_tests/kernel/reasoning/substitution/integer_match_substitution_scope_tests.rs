// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `integer_match_substitution_scope_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn match_substitution_shared_function_dag_scales_linearly() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let mut body = IntegerTerm::from_machine(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(9050)),
        )
        .unwrap();
        for _ in 0..depth {
            body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "pair".into(),
                vec![
                    PureFunctionArgument::Integer(body.clone().into()),
                    PureFunctionArgument::Integer(body.into()),
                ],
            ));
        }
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_integer(
                &symbolic_match(body, Variable(9051)),
                Variable(9050),
                &Bitvector32Term::Variable(Variable(9052)),
            )
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "function DAG expanded: {work:?}");
    }
}

#[test]
fn match_substitution_shared_bodies_scale_linearly() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let mut body = IntegerTerm::from_machine(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(9020)),
        )
        .unwrap();
        for _ in 0..depth {
            body = shared_symbolic_match(body, Variable(9021));
        }
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_integer(
                &symbolic_match(body, Variable(9021)),
                Variable(9020),
                &Bitvector32Term::Variable(Variable(9022)),
            )
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "match substitution expanded: {work:?}"
        );
    }
}
