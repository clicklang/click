// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `checked_singleton_substitution_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn checked_singleton_substitution_scales_with_shared_integer_dags() {
    let variable = Variable(70_102);
    let samples = [8, 16, 32, 64].map(|depth| {
        let mut value = observed(variable);
        for _ in 0..depth {
            value = IntegerTerm::add(value.clone(), value.clone());
        }
        let source = Proposition::Equal(
            Term::Integer(value.into()),
            Term::Integer(observed(variable).into()),
        );
        let (result, work) = instrumentation::measure_deterministic_work(|| {
            substitute_machine_constant_in_pure_proposition(&source, variable, 7)
        });
        assert!(result.is_ok());
        assert!(
            work <= 128 * (depth + 1),
            "depth {depth}: {work} work units"
        );
        work
    });
    assert!(samples[3] <= samples[0] * 10, "{samples:?}");
}

#[test]
fn pointer_witness_substitution_scales_with_the_explicit_proposition() {
    let from = Variable(70_112);
    let target = Variable(70_113);
    let leaf = Proposition::Equal(pointer_term(from), pointer_term(target));
    let samples = [8, 16, 32, 64].map(|size| {
        let mut source = leaf.clone();
        for _ in 1..size {
            source = Proposition::And(Box::new(leaf.clone()), Box::new(source));
        }
        let (result, work) = instrumentation::measure_deterministic_work(|| {
            substitute_pointer_value_in_proposition(&source, from, &pointer_value(target))
        });
        assert!(result.is_ok(), "size {size}: {result:?}");
        assert!(work <= 200 * size, "size {size}: {work}");
        work
    });
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}
