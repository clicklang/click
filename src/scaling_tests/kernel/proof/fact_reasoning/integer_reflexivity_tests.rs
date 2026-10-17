// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `integer_reflexivity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn normalize_using_graph_work_ignores_unrelated_ambient_equalities() {
    let a = Pointer::symbolic(Variable(96_120));
    let b = Pointer::symbolic(Variable(96_121));
    let c = Pointer::symbolic(Variable(96_122));
    let goal = normalization_pointer_equality(&a, &c);
    let mut curve = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = ProofFacts::from_ordered(&[
            normalization_pointer_equality(&a, &b),
            normalization_pointer_equality(&b, &c),
        ]);
        for i in 0..size {
            facts = facts.with_fact(normalization_pointer_equality(
                &Pointer::symbolic(Variable(100_000 + i * 2)),
                &Pointer::symbolic(Variable(100_001 + i * 2)),
            ));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, &[], &facts)
        });
        assert!(result.is_ok());
        curve.push(work);
    }
    assert!(curve[0] > 0);
    assert!(
        curve.iter().all(|work| *work == curve[0]),
        "ambient equality work: {curve:?}"
    );
}
