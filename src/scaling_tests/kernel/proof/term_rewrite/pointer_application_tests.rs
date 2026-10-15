// Scaling tests of `src/kernel/proof/term_rewrite/pointer_application_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pure_pointer_dag_substitution_and_capture_collection_scale_linearly() {
    let source = Variable(410);
    let replacement = Pointer::symbolic(Variable(411));
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut input = Pointer::symbolic(source);
        let mut expected = replacement.clone();
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_pointer_variable(source, &replacement);
            let result = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            result
        });
        assert!(result == expected);
        let (_, capture_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = CarrierVariables::for_rewrite(false);
            collect_pointer_carriers(&input, &mut variables);
            assert_eq!(variables.c, BTreeSet::from([source]));
            let mut captured = BTreeSet::new();
            crate::kernel::prelude::collect_proposition_capture_variables(
                &Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(Box::new(input.clone()), Box::new(input.clone())),
                    true,
                ),
                &mut captured,
            );
            assert!(captured.contains(&source));
        });
        measurements.push(work + capture_work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}

#[test]
fn pure_pointer_legacy_scalar_substitution_visits_the_shared_dag_once() {
    let variable = Variable(710);
    let replacement = Bitvector32Term::Constant(9);
    let mut measurements = Vec::new();
    for depth in [8, 16, 32] {
        let mut input = call(
            "scalar",
            vec![PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(variable),
            ))],
        );
        let mut expected = call(
            "scalar",
            vec![PureFunctionArgument::Value(CValue::Int32(
                replacement.clone(),
            ))],
        );
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::prelude::substitute_bitvector_variable_in_pointer(
                &input,
                variable,
                &replacement,
            )
        });
        assert!(result == expected);
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}
