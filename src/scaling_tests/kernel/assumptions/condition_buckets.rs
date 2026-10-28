#[test]
fn strict_upper_bound_queries_do_not_scan_condition_side_buckets() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| Bitvector32Term::Variable(Variable(940_000 + id));
        let mut facts = PureFactContext::new();
        for index in 1..=size {
            facts =
                facts.assume_condition(ConditionTerm::signed_less_than(var(index), var(0)), true);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!facts.has_exact_strict_upper_bound(&var(0)));
            }
        });
        samples.push(work);
    }
    eprintln!("strict upper side-bucket misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn constant_interval_queries_do_not_scan_symbolic_side_bounds() {
    for unsigned in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let var = |id| Bitvector32Term::Variable(Variable(950_000 + id));
            let order = |a, b| {
                if unsigned {
                    ConditionTerm::unsigned_less_equal(a, b)
                } else {
                    ConditionTerm::signed_less_equal(a, b)
                }
            };
            let mut facts = PureFactContext::new();
            for index in 1..=size {
                facts = facts.assume_condition(order(var(0), var(index)), true);
            }
            facts = facts
                .assume_condition(order(0u32.into(), var(0)), true)
                .assume_condition(order(var(0), 100u32.into()), true);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    let interval = if unsigned {
                        facts.indexed_unsigned32_constant_interval(&var(0))
                    } else {
                        facts.indexed_constant_interval(&var(0))
                    };
                    assert_eq!(interval, Some((0, 100)));
                }
            });
            samples.push(work);
        }
        eprintln!("constant interval unsigned={unsigned}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 16),
            "{samples:?}"
        );
    }
}

#[test]
fn direct_order_extrema_preserve_truth_formats_and_branch_isolation() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(951_000));
    let upper = ConditionTerm::signed_greater_equal(x.clone(), 100u32.into());
    let lower = ConditionTerm::signed_less_than(x.clone(), 10u32.into());
    let parent = PureFactContext::new()
        .assume_condition(upper.clone(), false)
        .assume_condition(lower, false);
    assert_eq!(parent.indexed_constant_interval(&x), Some((10, 99)));
    assert!(parent.has_exact_strict_upper_bound(&x));
    assert_eq!(parent.indexed_unsigned32_constant_interval(&x), None);
    let tighter = ConditionTerm::signed_less_equal(x.clone(), 80u32.into());
    let child = parent.clone().assume_condition(tighter.clone(), true);
    assert_eq!(child.indexed_constant_interval(&x), Some((10, 80)));
    assert_eq!(parent.indexed_constant_interval(&x), Some((10, 99)));
    let weakened = child.without_exact_fact(&Proposition::ConditionIs(tighter, true));
    assert_eq!(weakened.indexed_constant_interval(&x), Some((10, 99)));
    let weakened = weakened.without_exact_fact(&Proposition::ConditionIs(upper, false));
    assert!(!weakened.has_exact_strict_upper_bound(&x));
    assert_eq!(
        weakened.indexed_constant_interval(&x),
        Some((10, i64::from(i32::MAX)))
    );
}

#[test]
fn growing_constant_bound_buckets_keep_extrema_and_update_cost_indexed() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(952_000));
        let mut facts = PureFactContext::new();
        for bound in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_than(x.clone(), (bound + 100).into()),
                true,
            );
        }
        let ((_, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert_eq!(
                        facts.indexed_constant_interval(&x),
                        Some((i64::from(i32::MIN), 100))
                    );
                    assert!(facts.has_exact_strict_upper_bound(&x));
                }
                let mut index = facts.checked_order_bounds.clone();
                index.adjust(
                    &ConditionTerm::signed_less_than(x.clone(), 50u32.into()),
                    true,
                    true,
                );
                assert_eq!(index.interval(&x, false), Some((i64::from(i32::MIN), 49)));
            })
        });
        samples.push((work, persistent));
    }
    assert!(
        samples.iter().all(|s| s.0 <= samples[0].0 + 16),
        "{samples:?}"
    );
    assert!(samples[2].1 <= samples[0].1 * 3 + 32, "{samples:?}");
}

#[test]
fn equality_queries_do_not_scan_shared_endpoint_buckets() {
    for query in 0..3 {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let var = |id| Bitvector32Term::Variable(Variable(970_000 + id));
            let mut facts = PureFactContext::new();
            for index in 1..=size {
                facts = facts
                    .assume_condition(ConditionTerm::signed_less_equal(var(0), var(index)), true);
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    match query {
                        0 => assert!(!facts.range_facts_force_equal(&var(0), &0u32.into())),
                        1 => assert_eq!(facts.signed_constant_known_equal(&var(0)), None),
                        _ => assert!(
                            !facts.has_anchored_bitvector_equality_fact_for_memory_resolution(
                                &var(0),
                                &var(size + 1)
                            )
                        ),
                    }
                }
            });
            samples.push(work);
        }
        eprintln!("equality bucket query={query}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "query={query}: {samples:?}"
        );
    }
}

#[test]
fn interval_queries_do_not_walk_symbolic_order_components() {
    for branching in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let var = |id| Bitvector32Term::Variable(Variable(971_000 + id));
            let mut facts = PureFactContext::new()
                .assume_condition(ConditionTerm::signed_less_equal(0u32.into(), var(0)), true);
            for index in 1..=size {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(
                        var(if branching { 0 } else { index - 1 }),
                        var(index),
                    ),
                    true,
                );
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert_eq!(
                        facts.signed_interval(&var(0)),
                        Some((0, i64::from(i32::MAX)))
                    );
                }
            });
            samples.push(work);
        }
        eprintln!("symbolic interval branching={branching}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "branching={branching}: {samples:?}"
        );
    }
}

#[test]
fn equality_class_hits_and_anchored_misses_stay_indexed() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| Bitvector32Term::Variable(Variable(972_000 + id));
        let mut facts = PureFactContext::new();
        for index in 1..=size {
            facts = facts.assume_condition(ConditionTerm::equal(var(0), var(index)), true);
        }
        facts = facts.assume_condition(ConditionTerm::equal(var(size), 7u32.into()), true);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert_eq!(facts.signed_constant_known_equal(&var(0)), Some(7));
                assert_eq!(facts.signed_interval(&var(0)), Some((7, 7)));
                assert!(
                    facts.has_anchored_bitvector_equality_fact_for_memory_resolution(
                        &var(0),
                        &var(1)
                    )
                );
                assert!(
                    !facts.has_anchored_bitvector_equality_fact_for_memory_resolution(
                        &var(0),
                        &var(size + 1)
                    )
                );
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn contiguous_exclusion_queries_skip_runs_and_preserve_branches() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(973_000));
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), x.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x.clone(), size.into()),
                true,
            );
        // Insert the two halves in opposite orders, joining the runs at the end.
        for value in (0..size / 2)
            .chain((size / 2 + 1..size).rev())
            .chain([size / 2])
        {
            facts = facts.assume_condition(ConditionTerm::equal(x.clone(), value.into()), false);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(facts.range_facts_force_equal(&x, &size.into()));
                assert_eq!(
                    facts.signed_interval_past_exclusions(&x),
                    Some((i64::from(size), i64::from(size)))
                );
            }
        });
        samples.push(work);
        let removed = ConditionTerm::equal(x.clone(), (size / 2).into());
        let child = facts
            .clone()
            .without_exact_fact(&Proposition::ConditionIs(removed.clone(), false));
        assert_eq!(
            child.signed_interval_past_exclusions(&x),
            Some((i64::from(size / 2), i64::from(size)))
        );
        assert!(facts.range_facts_force_equal(&x, &size.into()));
        assert!(
            child
                .assume_condition(removed, false)
                .range_facts_force_equal(&x, &size.into())
        );
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn excluded_runs_keep_duplicate_sources_and_widths_separate() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(974_000));
    let forward = ConditionTerm::equal(x.clone(), 0u32.into());
    let reverse = ConditionTerm::equal(0u32.into(), x.clone());
    let mut index = checked_scalar_facts::CheckedScalarFacts::default();
    index.adjust(&forward, false, true);
    index.adjust(&reverse, false, true);
    index.adjust(&forward, false, false);
    assert_eq!(index.past_exclusions(&x, 0, 3), (1, 3));
    index.adjust(&reverse, false, false);
    assert_eq!(index.past_exclusions(&x, 0, 3), (0, 3));
    let wide = ConditionTerm::Compare {
        format: MachineIntegerType::Int64,
        relation: CompareRelation::Equal,
        left: x.clone().into(),
        right: Bitvector32Term::Int64Constant(0).into(),
    };
    index.adjust(&wide, false, true);
    assert_eq!(index.past_exclusions(&x, 0, 3), (0, 3));
}

#[test]
fn constant_equality_evidence_does_not_enumerate_symbolic_bounds() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| Bitvector32Term::Variable(Variable(975_000 + id));
        let mut facts = PureFactContext::new();
        for index in 1..=size {
            facts =
                facts.assume_condition(ConditionTerm::signed_less_equal(var(0), var(index)), true);
        }
        let (_, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                facts
                    .singleton_constant_equality_evidence(Variable(975_000))
                    .is_none()
            );
        });
        let facts = facts
            .assume_condition(ConditionTerm::signed_less_equal(7u32.into(), var(0)), true)
            .assume_condition(ConditionTerm::signed_less_equal(var(0), 7u32.into()), true);
        let (_, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts
                    .singleton_constant_equality_evidence(Variable(975_000))
                    .map(|v| v.0),
                Some(7)
            );
        });
        samples.push((miss_work, hit_work));
    }
    assert!(
        samples
            .iter()
            .all(|work| work.0 <= samples[0].0 + 32 && work.1 <= samples[0].1 + 32),
        "{samples:?}"
    );
}
