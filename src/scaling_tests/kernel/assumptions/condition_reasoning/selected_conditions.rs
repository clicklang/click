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
                let (found, missing_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        context.has_matching_condition_fact_for_memory_resolution(&goal, true)
                    });
                assert!(!found, "unmatched conditions need an explicit fact");
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

#[test]
fn memory_condition_matching_does_not_walk_alias_classes() {
    for unsigned in [false, true] {
        let compare = |left, right| {
            if unsigned {
                ConditionTerm::unsigned_less_than(left, right)
            } else {
                ConditionTerm::signed_less_than(left, right)
            }
        };
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let left = |id| Bitvector32Term::Variable(Variable(990_000 + id));
            let right = |id| Bitvector32Term::Variable(Variable(991_000 + id));
            let mut facts = PureFactContext::new();
            for id in 1..size {
                facts = facts
                    .assume_condition(ConditionTerm::equal(left(0), left(id)), true)
                    .assume_condition(ConditionTerm::equal(right(0), right(id)), true);
            }
            let goal = compare(left(0), right(0));
            let (found, missing) = crate::instrumentation::measure_deterministic_work(|| {
                facts.has_matching_condition_fact_for_memory_resolution(&goal, true)
            });
            assert!(!found);
            let fact = compare(left(size - 1), right(size - 1));
            facts = facts.assume_condition(fact, true);
            let (found, hit) = crate::instrumentation::measure_deterministic_work(|| {
                facts.has_matching_condition_fact_for_memory_resolution(&goal, true)
            });
            assert!(found);
            samples.push((missing, hit));
        }
        eprintln!("two memory alias classes unsigned={unsigned} at 8/32/128: {samples:?}");
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 + 32,
                "miss multiplies alias classes: {samples:?}"
            );
            assert!(
                pair[1].1 <= pair[0].1 + 32,
                "hit multiplies alias classes: {samples:?}"
            );
        }
    }
}

#[test]
fn aliased_memory_condition_matches_ignore_unrelated_facts() {
    let var = |id| Bitvector32Term::Variable(Variable(id));
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(var(992_000), var(992_001)), true)
            .assume_condition(ConditionTerm::equal(var(993_000), var(993_001)), true);
        for id in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_than(var(id), var(id + 10_000)),
                true,
            );
        }
        let goal = ConditionTerm::signed_greater_than(var(993_000), var(992_000));
        let source = ConditionTerm::signed_less_than(var(992_001), var(993_001));
        let (found, missing) = crate::instrumentation::measure_deterministic_work(|| {
            facts.has_matching_condition_fact_for_memory_resolution(&goal, true)
        });
        assert!(!found);
        for value in [true, false] {
            let held = facts.clone().assume_condition(source.clone(), value);
            let (found, hit) = crate::instrumentation::measure_deterministic_work(|| {
                held.has_matching_condition_fact_for_memory_resolution(&goal, value)
            });
            assert!(found);
            assert!(!held.has_matching_condition_fact_for_memory_resolution(&goal, !value));
            let withdrawn =
                held.without_exact_fact(&Proposition::ConditionIs(source.clone(), value));
            assert!(!withdrawn.has_matching_condition_fact_for_memory_resolution(&goal, value));
            samples.push((missing, hit));
        }
    }
    eprintln!("aliased memory condition beside 8/32/128 unrelated facts: {samples:?}");
    assert!(
        samples.iter().all(|sample| *sample == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn unsigned_memory_condition_matches_ignore_unrelated_facts() {
    let var = |id| Bitvector32Term::Variable(Variable(id));
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(var(994_000), var(994_001)), true)
            .assume_condition(ConditionTerm::equal(var(995_000), var(995_001)), true);
        for id in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::unsigned_less_than(var(id), var(id + 10_000)),
                true,
            );
        }
        let goal = ConditionTerm::unsigned_greater_than(var(995_000), var(994_000));
        let source = ConditionTerm::unsigned_less_than(var(994_001), var(995_001));
        let (found, missing) = crate::instrumentation::measure_deterministic_work(|| {
            facts.has_matching_condition_fact_for_memory_resolution(&goal, true)
        });
        assert!(!found);
        for value in [true, false] {
            let held = facts.clone().assume_condition(source.clone(), value);
            let (found, hit) = crate::instrumentation::measure_deterministic_work(|| {
                held.has_matching_condition_fact_for_memory_resolution(&goal, value)
            });
            assert!(found);
            assert!(!held.has_matching_condition_fact_for_memory_resolution(&goal, !value));
            let withdrawn =
                held.without_exact_fact(&Proposition::ConditionIs(source.clone(), value));
            assert!(!withdrawn.has_matching_condition_fact_for_memory_resolution(&goal, value));
            samples.push((missing, hit));
        }
    }
    eprintln!("unsigned memory conditions beside 8/32/128 facts: {samples:?}");
    assert!(
        samples.iter().all(|sample| *sample == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn compound_load_condition_hits_and_misses_ignore_other_facts() {
    for unsigned in [false, true] {
        for related in [false, true] {
            let mut samples = Vec::new();
            for size in [8u64, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let var = |id| Bitvector32Term::Variable(Variable(id));
                let raw = Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(Pointer::symbolic(Variable(997_000))),
                    crate::kernel::LoadKind::Int32,
                );
                let named = Bitvector32Term::Variable(
                    crate::kernel::eval::load_variable_for_term(&raw).unwrap().0,
                );
                let compound = |term| Bitvector32Term::add(term, 1u32.into());
                let condition = |left, right| {
                    if unsigned {
                        ConditionTerm::unsigned_less_than(left, right)
                    } else {
                        ConditionTerm::signed_less_than(left, right)
                    }
                };
                let mut facts = PureFactContext::new();
                for id in 0..size {
                    let left = if related {
                        compound(named.clone())
                    } else {
                        var(id)
                    };
                    facts = facts.assume_condition(condition(left, var(id + 10_000)), true);
                }
                let source = condition(compound(named), var(998_000));
                let goal = condition(compound(raw), var(998_000));
                assert_ne!(source, goal);
                let (found, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.has_matching_condition_fact_for_memory_resolution(&goal, true)
                });
                assert!(!found);
                for value in [false, true] {
                    let held = facts.clone().assume_condition(source.clone(), value);
                    let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                        held.has_matching_condition_fact_for_memory_resolution(&goal, value)
                    });
                    assert!(found);
                    samples.push((miss_work, work));
                }
            }
            eprintln!("compound load unsigned={unsigned}, related={related}: {samples:?}");
            assert!(
                samples.iter().all(|work| *work == samples[0]),
                "{samples:?}"
            );
        }
    }
}

#[test]
fn ordinary_condition_misses_do_not_walk_aliases_or_variable_buckets() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let var = |id| Bitvector32Term::Variable(Variable(930_000 + id));
            let mut context = PureFactContext::new();
            for id in 1..=size {
                let condition = if aliases {
                    ConditionTerm::equal(var(0), var(id))
                } else {
                    ConditionTerm::signed_less_than(var(0), var(id))
                };
                context = context.assume_condition(condition, true);
            }
            let goal = ConditionTerm::signed_less_than(var(0), var(1000));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(!context.has_condition_fact(goal.clone(), true));
                }
            });
            samples.push(work);
        }
        eprintln!("ordinary condition aliases={aliases}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "{samples:?}"
        );
    }
}
