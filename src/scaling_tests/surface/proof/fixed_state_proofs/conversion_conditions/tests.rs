#[test]
fn loadability_explanation_ignores_unrelated_objects() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".into());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let missing = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: pointer_base(&values),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let covering = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: pointer_base(&values),
        bytes: Bitvector32Term::Constant(8),
        wide: false,
    };
    let mut samples = Vec::new();
    let mut misses = Vec::new();
    for size in [8u64, 32, 128] {
        // Keep term-bridge imports cold at every sample size.
        crate::kernel::clear_integer_bridge_memo();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: state.memory().clone(),
                base: Pointer {
                    block: PointerBlock::Heap(index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                bytes: Bitvector32Term::Constant(8),
                wide: false,
            });
        }
        let (explanation, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
            loadability_explanation(&missing, &context, &site, &mut site.labels())
        });
        assert!(explanation.is_none());
        misses.push(miss_work);
        let with_range = context.assume_proposition(covering.clone());
        let (explanation, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
            loadability_explanation(&missing, &with_range, &site, &mut site.labels())
        });
        assert!(explanation.is_some());
        let withdrawn = with_range.without_exact_fact(&covering);
        assert!(loadability_explanation(&missing, &withdrawn, &site, &mut site.labels()).is_none());
        samples.push(hit_work);
    }
    assert!(
        misses.iter().all(|work| *work == misses[0]),
        "miss work: {misses:?}"
    );
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn scoped_obligation_probing_scales_with_requirements_not_ambient_facts() {
    fn work(requirements: u64, ambient: u64, related: bool) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let (values, state) = indexed_pointer_site();
        let expression = CExpression::Variable("index".into());
        let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
        let mut context = PureFactContext::new();
        for i in 0..ambient {
            context = context.assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(Bitvector32Term::Variable(Variable(780_000 + i))),
                    right: Box::new(1000u32.into()),
                },
                true,
            );
        }
        if related {
            for i in 0..ambient {
                let condition = Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(Bitvector32Term::Variable(Variable(785_000 + i))),
                        right: Box::new(Bitvector32Term::Constant(i as u32)),
                    },
                    true,
                );
                context = context.assume_proposition(Proposition::ForAll {
                    var: Variable(785_000 + i),
                    sort: crate::kernel::Sort::CInt32,
                    name: crate::kernel::BinderName::written("other"),
                    body: Box::new(Proposition::Implies(
                        Box::new(condition.clone()),
                        Box::new(condition),
                    )),
                });
            }
        }
        // The context lazily keys facts admitted since its last query. Charge
        // that one-time construction separately from the obligation checks.
        let (_, startup) = crate::instrumentation::measure_deterministic_work(|| {
            context.build_stated_proposition_index();
        });
        assert!(
            startup <= ambient as usize * 32 + 64,
            "index startup: {startup}"
        );
        let obligations = (0..requirements)
            .map(|i| {
                crate::kernel::ProofObligation::verification_condition(Proposition::ForAll {
                    var: Variable(790_000 + i),
                    sort: crate::kernel::Sort::CInt32,
                    name: crate::kernel::BinderName::written("k"),
                    body: Box::new(Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessThan,
                            left: Box::new(Bitvector32Term::Variable(Variable(790_000 + i))),
                            right: Box::new(255u32.into()),
                        },
                        true,
                    )),
                })
            })
            .collect::<Vec<_>>();
        let ((result, probe), work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::execution_planning::probe_open_obligations(|| {
                refuse_unproved_conversion_bounds(&obligations, &context, &site)
            })
        });
        result.unwrap();
        assert_eq!(probe.recorded.len(), requirements as usize);
        for (requirement, obligation) in probe.recorded.iter().zip(&obligations) {
            assert_eq!(&requirement.proposition, obligation.proposition());
        }
        work
    }
    let selected = [4, 16, 64, 256].map(|n| work(n, 0, false));
    for pair in selected.windows(2) {
        assert!(pair[1] <= pair[0] * 5 + 64, "requirements: {selected:?}");
    }
    let ambient = [4, 16, 64, 256].map(|n| work(4, n, false));
    assert!(
        ambient.iter().all(|n| *n <= ambient[0] + 64),
        "ambient: {ambient:?}"
    );
    let related = [4, 16, 64, 256].map(|n| work(4, n, true));
    assert!(
        related.iter().all(|n| *n <= related[0] + 64),
        "same-shape universal facts: {related:?}"
    );
}
