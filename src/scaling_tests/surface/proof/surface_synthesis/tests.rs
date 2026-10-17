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

#[test]
fn pointer_spelling_skips_cyclic_offsets_and_tries_the_next_local() {
    std::thread::Builder::new()
        .stack_size(1792 * 1024)
        .spawn(|| {
            for size in [1usize, 8, 32, 128] {
                let pointer = Pointer {
                    block: crate::kernel::PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(0),
                };
                let cyclic = Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(Bitvector32Term::PointerAddress(Box::new(pointer.clone()))),
                        byte_width: 4,
                    },
                };
                let mut state = CState::new();
                for index in 0..size {
                    state = state.with_local(
                        format!("a_{index:04}"),
                        CValue::typed_pointer(cyclic.clone(), CType::Int32Pointer),
                    );
                }
                let synthesize = |state: &CState| {
                    synthesize_surface_pointer(
                        &pointer,
                        ParameterBinding::default(),
                        state,
                        &BTreeMap::new(),
                    )
                };
                let (missing, work) =
                    crate::instrumentation::measure_deterministic_work(|| synthesize(&state));
                assert!(missing.is_none());
                assert!(work >= size && work <= 4 * size + 64, "{size}: {work}");
                state = state.with_local(
                    "z_pointer",
                    CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
                );
                for _ in 0..2 {
                    let (found, work) =
                        crate::instrumentation::measure_deterministic_work(|| synthesize(&state));
                    assert_eq!(found, Some(CExpression::Variable("z_pointer".into())));
                    assert!(work >= size && work <= 4 * size + 64, "{size}: {work}");
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
