use super::*;

#[test]
fn symbolic_byte_initialization_publication_ignores_unrelated_locals() {
    let (mut state, _, _, original) = fixture();
    let range = MemoryRange::new_wide(
        original.base().clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::Variable(Variable(918_001)),
        1,
    );
    let mut expected_work = None;
    for size in [0, 64, 256] {
        for index in 0..size {
            state = state.with_local(format!("output_neighbor_{index}"), int32(index));
        }
        let (fact, work) = crate::instrumentation::measure_deterministic_work(|| {
            initialized_scalar_range_fact(&state, &range, ProgramType::UInt8)
        });
        assert!(matches!(fact, Proposition::ForAll { .. }));
        assert_eq!(work, *expected_work.get_or_insert(work));
    }
}

#[test]
fn input_initialization_publication_ignores_range_length_and_unrelated_locals() {
    let mut expected = None;
    for unrelated in [0, 64, 256] {
        let (mut state, function, segment, original) = fixture();
        for i in 0..unrelated {
            state = state.with_local(format!("unrelated_{i}"), int32(i));
        }
        for length in [1u32, 1024, 1_000_000_000] {
            let range = MemoryRange::new(original.base().clone(), 0u32.into(), length.into());
            let (fact, work) = crate::instrumentation::measure_deterministic_work(|| {
                initialized_input_range_fact(
                    &state,
                    function.contract_interface(),
                    &segment,
                    &range,
                )
                .unwrap()
                .unwrap()
            });
            assert!(matches!(fact, Proposition::ForAll { .. }));
            if let Some(expected) = expected {
                assert_eq!(work, expected);
            } else {
                expected = Some(work);
            }
        }
    }
}

#[test]
fn publishing_many_initialized_input_facts_scales_with_the_fact_count() {
    let (state, function, segment, range) = fixture();
    let mut costs = Vec::new();
    for count in [16, 64, 256] {
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut facts = PureFactContext::new();
            for _ in 0..count {
                let fact = initialized_input_range_fact(
                    &state,
                    function.contract_interface(),
                    &segment,
                    &range,
                )
                .unwrap()
                .unwrap();
                facts = facts.assume_proposition(fact);
            }
            facts
        });
        costs.push(work);
    }
    for pair in costs.windows(2) {
        assert!(pair[1] <= 5 * pair[0] + 32, "{costs:?}");
    }
}
