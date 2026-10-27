// Deterministic scaling tests for condition matching in memory resolution.

#[test]
fn exact_memory_condition_matches_ignore_other_facts() {
    let var = |id| Bitvector32Term::Variable(Variable(id));
    let condition = |kind, left, right| match kind {
        0 => ConditionTerm::IntegerEqual(
            crate::kernel::IntegerTerm::var(Variable(left)).into(),
            crate::kernel::IntegerTerm::var(Variable(right)).into(),
        ),
        1 => ConditionTerm::pointer_equal(
            Pointer::symbolic(Variable(left)),
            Pointer::symbolic(Variable(right)),
        ),
        2 => ConditionTerm::uint64_less_than(var(left), var(right)),
        3 => ConditionTerm::signed_less_than(
            Bitvector32Term::add(var(left), 1u32.into()),
            var(right),
        ),
        _ => unreachable!(),
    };
    for kind in 0..4 {
        for related in [false, true] {
            let mut samples = Vec::new();
            for size in [8u64, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let mut context = PureFactContext::new();
                for index in 0..size {
                    let left = if related { 950_000 } else { index };
                    context = context.assume_condition(condition(kind, left, index + 10_000), true);
                }
                let goal = condition(kind, 950_000, 950_001);
                // Compound misses still use the general fallback; only
                // their exact hits are claimed to have constant work here.
                let missing_work = if kind != 3 {
                    let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                        context.has_matching_condition_fact_for_memory_resolution(&goal, true)
                    });
                    assert!(!found, "exact-only conditions need the stated fact");
                    work
                } else {
                    0
                };
                context = context.assume_condition(goal.clone(), true);
                let (found, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.has_matching_condition_fact_for_memory_resolution(&goal, true)
                });
                assert!(found);
                samples.push((missing_work, hit_work));
            }
            eprintln!("exact condition kind={kind}, related={related}: {samples:?}");
            assert!(
                samples.iter().all(|sample| *sample == samples[0]),
                "condition matching scans facts: kind={kind}, related={related}, {samples:?}"
            );
        }
    }
}

#[test]
fn symmetric_memory_condition_matches_ignore_other_facts() {
    use CompareRelation::*;
    use MachineIntegerType::*;
    for format in [Int32, UInt32] {
        for relation in [Equal, LessThan] {
            for related in [false, true] {
                let mut samples = Vec::new();
                for size in [8u64, 16, 32] {
                    let _session = crate::kernel::VerificationSession::enter();
                    let term = |id| {
                        Bitvector32Term::add(Bitvector32Term::Variable(Variable(id)), 1u32.into())
                    };
                    let condition = |left, right, relation| ConditionTerm::Compare {
                        format,
                        relation,
                        left: Box::new(term(left)),
                        right: Box::new(term(right)),
                    };
                    let mut context = PureFactContext::new();
                    for index in 0..size {
                        context = context.assume_condition(
                            condition(
                                if related { 970_000 } else { index },
                                index + 10_000,
                                relation,
                            ),
                            true,
                        );
                    }
                    let fact = condition(970_000, 970_001, relation);
                    let reverse = match relation {
                        Equal => Equal,
                        LessThan => GreaterThan,
                        LessEqual => GreaterEqual,
                        GreaterThan => LessThan,
                        GreaterEqual => LessEqual,
                    };
                    let goal = condition(970_001, 970_000, reverse);
                    for value in [false, true] {
                        let context = context.clone().assume_condition(fact.clone(), value);
                        let (found, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                context
                                    .has_matching_condition_fact_for_memory_resolution(&goal, value)
                            });
                        assert!(found);
                        samples.push(work);
                    }
                }
                eprintln!("symmetric {format:?} {relation:?} related={related}: {samples:?}");
                assert!(
                    samples.iter().all(|work| *work == samples[0]),
                    "{samples:?}"
                );
            }
        }
    }
}

#[test]
fn equivalent_equality_spellings_use_bounded_lookups() {
    use CompareRelation::Equal;
    use MachineIntegerType::{Int32, UInt32};
    for kind in 0..3 {
        let mut samples = Vec::new();
        for size in [8u64, 16, 32] {
            let _session = crate::kernel::VerificationSession::enter();
            let word =
                |id| Bitvector32Term::add(Bitvector32Term::Variable(Variable(id)), 1u32.into());
            let comparison = |format, left, right| ConditionTerm::Compare {
                format,
                relation: Equal,
                left: Box::new(word(left)),
                right: Box::new(word(right)),
            };
            let offset = |left, right| {
                ConditionTerm::PointerOffsetEqual(
                    Box::new(PointerOffsetTerm::Variable(Variable(left))),
                    Box::new(PointerOffsetTerm::Variable(Variable(right))),
                )
            };
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    if kind == 2 {
                        offset(index, index + 10_000)
                    } else {
                        comparison(Int32, index, index + 10_000)
                    },
                    true,
                );
            }
            let (fact, goal) = match kind {
                0 => (
                    comparison(Int32, 980_000, 980_001),
                    comparison(UInt32, 980_000, 980_001),
                ),
                1 => (
                    comparison(Int32, 980_000, 980_001),
                    comparison(UInt32, 980_001, 980_000),
                ),
                _ => (offset(980_000, 980_001), offset(980_001, 980_000)),
            };
            for value in [false, true] {
                let context = context.clone().assume_condition(fact.clone(), value);
                let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.has_matching_condition_fact_for_memory_resolution(&goal, value)
                });
                assert!(found);
                samples.push(work);
                let withdrawn =
                    context.without_exact_fact(&Proposition::ConditionIs(fact.clone(), value));
                assert!(!withdrawn.has_matching_condition_fact_for_memory_resolution(&goal, value));
                assert!(!context.has_matching_condition_fact_for_memory_resolution(&goal, !value));
            }
        }
        eprintln!("equivalent equality kind={kind}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}
