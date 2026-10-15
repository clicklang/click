// Scaling tests of `src/surface/proof/surface_synthesis/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn boolean_local_synthesis_round_trips_and_scales_with_local_population() {
    for size in [16usize, 64, 256, 1024] {
        let mut state = CState::new();
        for index in 0..size {
            state = state.with_local(
                format!("a_{index:04}"),
                crate::kernel::bool_value(Bitvector32Term::Variable(Variable(2000 + index as u64))),
            );
        }
        let value = crate::kernel::bool_value(Bitvector32Term::Variable(Variable(9000)));
        let CValue::Bool(term) = &value else {
            unreachable!()
        };
        state = state.with_local("z_bool", value.clone());
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_bitvector(
                term,
                ParameterBinding::default(),
                &state,
                &BTreeMap::new(),
            )
        });
        let surface = surface.expect("a normalized Boolean local has its source spelling");
        assert_eq!(
            surface,
            ContractExpression::CFragment(CExpression::Variable("z_bool".into()))
        );
        assert!(
            work >= size && work <= size + 64,
            "{size} locals: {work} work"
        );
        let equality = ClickProposition::Comparison {
            left: surface.clone(),
            operator: ComparisonOperator::Equal,
            right: surface,
        };
        let lowered = relower_written_proposition(&equality, &state).unwrap();
        assert_eq!(
            lowered,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(term.clone()), Box::new(term.clone()),),
                true
            )
        );
    }
}
