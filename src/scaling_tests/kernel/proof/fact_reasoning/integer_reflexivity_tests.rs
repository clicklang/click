// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `integer_reflexivity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn normalize_using_graph_work_ignores_unrelated_ambient_equalities() {
    let a = OldAddress::symbolic(Variable(96_120));
    let b = OldAddress::symbolic(Variable(96_121));
    let c = OldAddress::symbolic(Variable(96_122));
    let goal = normalization_pointer_equality(&a, &c);
    let mut curve = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactStore::from_ordered(&[
            normalization_pointer_equality(&a, &b),
            normalization_pointer_equality(&b, &c),
        ]);
        for i in 0..size {
            facts = facts.with_fact(normalization_pointer_equality(
                &OldAddress::symbolic(Variable(100_000 + i * 2)),
                &OldAddress::symbolic(Variable(100_001 + i * 2)),
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

#[test]
fn listed_loaded_fold_matching_tracks_explicit_premises_not_memory_history() {
    let mut fixed = Vec::new();
    let mut selected = Vec::new();
    for size in [16u32, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = OldAddress {
            base: "listed-fold".into(),
            offset: OldAddressOffset::Constant(0),
        };
        let mut memory = SymbolicMemory::new().with_block("listed-fold", size * 4);
        for index in 0..size {
            memory = memory.store(
                pointer.offset_by_bytes(index * 4),
                ProgramValue::Int32(OldMachineTerm::constant(index)),
            );
        }
        let memory = crate::kernel::intern_memory(memory);
        let required = listed_loaded_fold(&memory, 981_000, 989_000);
        let matching = listed_loaded_fold(&memory, 982_000, 989_000);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            listed_comparison_fact_is_available(&required, std::slice::from_ref(&matching))
        });
        assert!(result);
        fixed.push(work);
        let mut premises = (0..size)
            .map(|index| {
                listed_loaded_fold(
                    &memory,
                    983_000 + u64::from(index) * 4,
                    990_000 + u64::from(index),
                )
            })
            .collect::<Vec<_>>();
        premises.insert(0, matching);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            listed_comparison_fact_is_available(&required, &premises)
        });
        assert!(result);
        selected.push(work);
    }
    assert!(
        fixed[0] > 0 && fixed.iter().all(|work| *work == fixed[0]),
        "{fixed:?}"
    );
    assert!(
        selected
            .windows(2)
            .all(|pair| pair[1] <= pair[0] * 5 + 1024),
        "{selected:?}"
    );
}
