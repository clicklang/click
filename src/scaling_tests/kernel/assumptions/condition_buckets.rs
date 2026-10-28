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
