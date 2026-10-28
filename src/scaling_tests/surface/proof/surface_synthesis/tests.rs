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
        // A `Bool` equals itself (rule L-Eq), so the equality folds.
        let lowered = relower_written_proposition(&equality, &state).unwrap();
        assert_eq!(
            lowered,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
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
                        value: Box::new(Bitvector32Term::pointer_address(pointer.clone())),
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

#[test]
fn pointer_local_synthesis_skips_unrelated_pointer_blocks() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256, 1024] {
        let mut state = CState::new();
        for i in 0..size {
            state = state.with_local(
                format!("a_{i:04}"),
                CValue::pointer(Pointer::symbolic(Variable(982_000 + i as u64))),
            );
        }
        let base = Pointer::symbolic(Variable(984_000));
        state = state.with_local("z_base", CValue::pointer(base.clone()));
        let selected = base.offset_by_bytes(8);
        let (expression, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_pointer(
                &selected,
                ParameterBinding::default(),
                &state,
                &BTreeMap::new(),
            )
        });
        assert_eq!(
            expression,
            Some(CExpression::Add(
                Box::new(CExpression::Variable("z_base".into())),
                Box::new(CExpression::Value(int32(2))),
            ))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn integer_division_synthesis_work_tracks_the_selected_expression() {
    use crate::kernel::{IntegerTerm, SharedIntegerTerm};
    let variable = Variable(8_410_000);
    let names = BTreeMap::from([(variable, "n".to_string())]);
    let state = CState::new();
    let samples = [4usize, 8, 16, 32].map(|size| {
        let mut term: SharedIntegerTerm = IntegerTerm::Variable(variable).into();
        for level in 0..size {
            let divisor = IntegerTerm::Constant(4.into()).into();
            term = if level % 2 == 0 {
                IntegerTerm::TruncatingQuotient(term, divisor)
            } else {
                IntegerTerm::TruncatingRemainder(term, divisor)
            }
            .into();
        }
        let _scope = SurfaceSynthesisScope::enter();
        let surface =
            synthesize_surface_integer(&term, ParameterBinding::default(), &state, &names)
                .expect("the selected quotient/remainder chain is spellable");
        let mut cursor = &surface;
        for level in (0..size).rev() {
            let ContractExpression::Call { name, arguments } = cursor else {
                panic!("the selected division node lost its spelling");
            };
            assert_eq!(
                name,
                if level % 2 == 0 {
                    "truncating_quotient"
                } else {
                    "truncating_remainder"
                }
            );
            assert_eq!(arguments.len(), 2);
            assert_eq!(arguments[1], ContractExpression::IntegerLiteral("4".into()));
            cursor = &arguments[0];
        }
        assert_eq!(*cursor, ContractExpression::Binding("n".into()));
        let work = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let slot = slot.borrow();
            let budget = slot.as_ref().unwrap();
            assert_eq!(budget.depth, 0);
            assert_eq!(budget.exhausted_category, None);
            SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work
        });
        assert!(work >= size && work <= 3 * size + 8, "{size}: {work}");
        work
    });
    for pair in samples.windows(2) {
        assert!(pair[1] > pair[0] && pair[1] <= 2 * pair[0], "{samples:?}");
    }
}

#[test]
fn integer_division_synthesis_refuses_shared_dag_expansion_within_its_budget() {
    use crate::kernel::{IntegerTerm, SharedIntegerTerm};
    let variable = Variable(8_420_000);
    let names = BTreeMap::from([(variable, "n".to_string())]);
    let state = CState::new();
    for size in [16usize, 32, 64, 128] {
        let mut term: SharedIntegerTerm = IntegerTerm::Variable(variable).into();
        for _ in 0..size {
            term = IntegerTerm::TruncatingRemainder(term.clone(), term).into();
        }
        let _scope = SurfaceSynthesisScope::enter();
        assert!(
            synthesize_surface_integer(&term, ParameterBinding::default(), &state, &names)
                .is_none()
        );
        SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let slot = slot.borrow();
            let budget = slot.as_ref().unwrap();
            assert_eq!(budget.depth, 0);
            assert_eq!(budget.exhausted_category, Some("integer"));
            let work = SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work;
            assert!(
                work > 0 && work <= SURFACE_SYNTHESIS_WORK_LIMIT,
                "{size}: {work}"
            );
        });
    }
}

#[test]
fn allocation_result_names_use_one_index_as_recorded_history_grows() {
    let mut samples = Vec::new();
    let mut insertion_samples = Vec::new();
    for count in [4usize, 16, 64, 128] {
        let source = format!(
            "void f() {{ int32* p; {} }}",
            "p = malloc(4);".repeat(count)
        );
        let function = crate::languages::c::syntax::parse_function(&source).unwrap();
        let layout =
            crate::surface::lowering::SourceExecutionLayout::for_function(&function).unwrap();
        let mut snapshots = RecordedSnapshots::new().with_source_layout(layout.clone());
        let mut last = Pointer::null();
        let mut last_region = 0;
        let mut insertion_work = 0;
        for n in 0..count {
            last = Pointer {
                block: PointerBlock::Heap(990_000 + n as u64),
                offset: PointerOffsetTerm::Constant(0),
            };
            last_region = layout
                .source_path_region(&[SourcePathStep::Statement(n + 1)], ProgramPointKind::Exit)
                .unwrap();
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                snapshots.insert(
                    ProgramPointRef {
                        region: CodeRegionRef::Region(last_region),
                        kind: ProgramPointKind::Exit,
                    },
                    CState::new().with_local(
                        "p",
                        CValue::typed_pointer(last.clone(), CType::Int32Pointer),
                    ),
                )
            });
            insertion_work += work;
        }
        insertion_samples.push((count, insertion_work));
        let ((answer, work), indexed) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                snapshots.allocation_result(&last)
            })
        });
        assert_eq!(answer, Some(CodeRegionRef::Region(last_region)));
        assert_eq!(work, 1);
        samples.push(indexed);
    }
    let (base_count, base_work) = insertion_samples[0];
    assert!(base_work > 0);
    assert!(
        insertion_samples
            .iter()
            .all(|(count, work)| { *work <= base_work * count / base_count * 4 }),
        "{insertion_samples:?}"
    );
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4 + 8),
        "{samples:?}"
    );
}
