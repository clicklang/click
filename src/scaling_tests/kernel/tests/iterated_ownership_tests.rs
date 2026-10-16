// Scaling tests of `src/kernel/tests/iterated_ownership_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn taking_one_element_is_constant_in_the_range_size() {
    let mut samples = Vec::new();
    for size in SIZES {
        let state = cells_state(size, size);
        let (taken, work) =
            crate::instrumentation::measure_deterministic_work(|| take(&state, size / 2));
        taken.expect("the middle cell is free");
        samples.push((size, work));
    }
    assert_constant_plus_log("taking one element", &samples, 4.0);
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn a_loop_taking_m_elements_is_linear_in_m() {
    let capacity = 8192;
    let mut samples = Vec::new();
    for claimed in LOOP_SIZES {
        let state = cells_state(capacity, claimed);
        let (claimed_state, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..claimed).try_fold(state.clone(), |state, index| {
                store_guard(&take(&state, index)?, index, 1)
            })
        });
        let claimed_state = claimed_state.expect("every free cell can be claimed");
        assert!(held_fact(&claimed_state).holes().is_empty());
        samples.push((claimed, work));
    }
    eprintln!("claiming M elements (M, units): {samples:?}");
    for window in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = window else {
            unreachable!()
        };
        // Twice the elements may cost at most two and a half times the
        // work: a quadratic loop would cost four.
        let ratio = *large_work as f64 / *small_work as f64;
        let elements = f64::from(*large) / f64::from(*small);
        assert!(
            ratio <= elements * 1.25,
            "claiming {large} elements charged {large_work} units against {small_work} for \
             {small}: growth {ratio:.2} for {elements}x the elements ({samples:?})"
        );
    }
}

#[test]
fn separation_from_an_unrelated_range_is_constant_in_the_range_size() {
    let mut samples = Vec::new();
    for size in SIZES {
        let fact = CResource::iterated(cells_fact(size));
        let unrelated = CResource::Memory(range(UNRELATED, 0, 4));
        let assumptions = PureFactContext::new();
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.proves_resource_separate(&fact, &unrelated)
        });
        assert!(separate, "a range in another block is separate");
        samples.push((size, work));
    }
    assert_constant_plus_log("separation from an unrelated range", &samples, 2.0);
    // A range that may hold an element is never proved separate.
    let fact = CResource::iterated(cells_fact(16));
    assert!(
        !PureFactContext::new()
            .proves_resource_separate(&fact, &CResource::Memory(range(DATA, 3, 4)))
    );
}

#[test]
fn unfolding_the_declaring_resource_is_constant_in_the_range_size() {
    let definitions = cells_definition();
    let mut samples = Vec::new();
    for size in SIZES {
        let folded = CResourceFact::own(CResource::Composite {
            name: "cells".into(),
            arguments: vec![
                CValue::pointer(heap_base(DATA)).into(),
                CValue::pointer(heap_base(OCCUPIED)).into(),
                int32(size).into(),
            ]
            .into(),
        });
        let context = ResourceContext::new().unchecked_with_fact(folded.clone());
        let memory = CMemory::new();
        let assumptions = PureFactContext::new();
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::expand_composite_resource_fact(
                &context,
                &folded,
                &definitions,
                &memory,
                &assumptions,
            )
        });
        let expanded = expanded.expect("the body expands");
        assert!(
            expanded.contains_exact_representation(&CResourceFact::own(CResource::iterated(
                cells_fact(size)
            )))
        );
        // Folding is the same exchange read backwards: the folded head is
        // what remains once the exposed body is consumed.
        let folded_again = expanded
            .clone()
            .without_fact(
                &CResourceFact::own(CResource::iterated(cells_fact(size))),
                &assumptions,
            )
            .and_then(|context| {
                context.without_fact(
                    &CResourceFact::own_memory(range(OCCUPIED, 0, size)),
                    &assumptions,
                )
            })
            .expect("the exposed body can be consumed");
        assert!(folded_again.is_empty());
        samples.push((size, work));
    }
    assert_constant_plus_log("unfolding the declaring resource", &samples, 4.0);
}

#[test]
fn giving_one_element_is_constant_in_the_range_size() {
    let mut samples = Vec::new();
    for size in SIZES {
        let state = cells_state(size, size);
        let taken = take(&state, size / 2).expect("the middle cell is free");
        let (returned, work) =
            crate::instrumentation::measure_deterministic_work(|| give(&taken, size / 2));
        let returned = returned.expect("the taken cell can be returned");
        assert!(held_fact(&returned).holes().is_empty());
        samples.push((size, work));
    }
    assert_constant_plus_log("giving one element", &samples, 4.0);
}
