// Scaling tests of `src/surface/proof/smart_closures.rs` (module `synthesized_literal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn speculative_simp_premise_spelling_declines_large_components_without_rendering() {
    let function = syntax::parse_function("int32 noop() { return 0; }").unwrap();
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let proof = Proof::for_fixed_state_goal(
        "speculative premise rendering",
        0,
        &[],
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ),
        ParameterBinding::new(function.parameters(), &[]),
        &state,
        &state,
        &snapshots,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
        &[],
    );
    for size in [128, 512, 2048, 8192] {
        let premises = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(8_179_000 + index))),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.resolve_simp_premises(&premises, &[])
        });
        assert!(
            result.is_none(),
            "an oversized speculative component must be declined"
        );
        assert_eq!(work, 0, "size {size}: no candidate should be rendered");
    }
}
