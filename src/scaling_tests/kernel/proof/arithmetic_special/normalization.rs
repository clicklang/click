use super::*;
use crate::kernel::proof::ProofFacts;
use crate::kernel::proof::fact_reasoning::normalize_using_conditions;

#[test]
fn specialized_normalization_uses_only_selected_inputs_as_related_and_unrelated_facts_grow() {
    let v = |n| IntegerTerm::var(crate::kernel::Variable(n));
    let le = |a: IntegerTerm, b: IntegerTerm| {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    };
    let (a, b, f) = (v(877001), v(877002), v(877003));
    let selected = vec![
        le(a.clone(), b.clone()),
        le(f.clone(), IntegerTerm::constant_i64(0)),
    ];
    let goal = le(
        IntegerTerm::multiply(b.clone(), f.clone()),
        IntegerTerm::multiply(a.clone(), f),
    );
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = selected.clone();
            for index in 0..size {
                ambient.push(le(
                    v(if related { 877001 } else { 878000 + index }),
                    IntegerTerm::constant_i64(1000 + index as i64),
                ));
            }
            let facts = ProofFacts::from_ordered(&ambient);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            result.unwrap();
            assert!(normalize_using_conditions(&goal, &selected[..1], &facts).is_err());
            work
        });
        assert!(
            samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] + 8),
            "{related}: {samples:?}"
        );
    }
}
