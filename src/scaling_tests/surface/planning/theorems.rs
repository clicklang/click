#[test]
fn conclusion_index_ignores_unrelated_theorems_on_hits_and_misses() {
    let file = parser::parse("function selected(x: Integer) -> Integer { x } theorem law(x: Integer) { ensures selected(x) == x; } theorem probe(value: Integer) { ensures selected(value) == value; }").unwrap();
    let template = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = file.theorem_definitions()[1].ensures()[0].ensure() else {
        panic!()
    };
    for size in [0, 64, 256, 1024] {
        let mut index = TheoremConclusionIndex::default();
        for ordinal in 0..size {
            let mut theorem = template.clone();
            theorem.name = format!("unused{ordinal}");
            let Ensure::Proposition(SurfaceProposition::Comparison {
                left: SurfaceTerm::Call { name, .. },
                ..
            }) = &mut theorem.ensures[0].ensure
            else {
                panic!()
            };
            *name = format!("unused_function{ordinal}");
            index.insert(&theorem, ordinal);
        }
        index.insert(template, size);
        for reversed in [false, true] {
            let mut goal = goal.clone();
            if reversed {
                let SurfaceProposition::Comparison { left, right, .. } = &mut goal else {
                    panic!()
                };
                std::mem::swap(left, right);
            }
            let ((count, work), lookup_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    index.candidates(&goal, usize::MAX).count()
                })
            });
            assert_eq!(count, 1);
            assert_eq!(work, 8);
            assert!(
                lookup_work <= 12 * (size + 2).ilog2() as usize + 16,
                "index scanned {size} unrelated theorems: {lookup_work}"
            );
            let mut missing = goal.clone();
            let SurfaceProposition::Comparison { left, right, .. } = &mut missing else {
                panic!()
            };
            match (left, right) {
                (SurfaceTerm::Call { name, .. }, _) | (_, SurfaceTerm::Call { name, .. }) => {
                    *name = "absent".into()
                }
                _ => panic!(),
            }
            let (count, work) = crate::persistent::measure_persistent_work(|| {
                index.candidates(&missing, usize::MAX).count()
            });
            assert_eq!(count, 0);
            assert!(
                work <= 12 * (size + 2).ilog2() as usize + 16,
                "miss scanned {size} unrelated theorems: {work}"
            );
        }
    }
}

#[test]
fn conclusion_index_prefix_and_related_candidate_work_are_bounded() {
    let file = parser::parse("function selected(x: Integer) -> Integer { x } theorem law(x: Integer) { ensures selected(x) == x; }").unwrap();
    let template = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = template.ensures()[0].ensure() else {
        panic!()
    };
    for size in [8, 32, 128, 512] {
        let mut index = TheoremConclusionIndex::default();
        for ordinal in 0..size {
            index.insert(template, ordinal);
        }
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            index
                .candidates(goal, usize::MAX)
                .map(|candidate| {
                    assert!(
                        match_theorem_conclusion(template, candidate.ensure, goal)
                            .next()
                            .is_some()
                    );
                })
                .count()
        });
        assert_eq!(count, size);
        assert!(
            work <= 8 * size + 7,
            "candidate matching was superlinear: {size}: {work}"
        );
        assert_eq!(index.candidates(goal, size / 2).count(), size / 2);
        assert_eq!(index.candidates(goal, 0).count(), 0);
    }
}

#[test]
fn symmetric_match_alternatives_stop_at_the_existing_work_budget() {
    for size in [8usize, 16, 32] {
        let parameters = (0..size)
            .map(|i| format!("x{i}: Integer, y{i}: Integer"))
            .collect::<Vec<_>>()
            .join(", ");
        let comparisons = (0..size)
            .map(|i| format!("x{i} == y{i}"))
            .collect::<Vec<_>>()
            .join(" and ");
        let source = format!("theorem law({parameters}) {{ ensures {comparisons}; }}");
        let file = parser::parse(&source).unwrap();
        let theorem = &file.theorem_definitions()[0];
        let Ensure::Proposition(goal) = theorem.ensures()[0].ensure() else {
            panic!()
        };
        crate::instrumentation::with_run_work_limit(256, || {
            let mut applications = match_theorem_conclusion(theorem, 0, goal);
            assert!(applications.by_ref().count() < 256);
            assert!(crate::instrumentation::deadline_exceeded());
            assert!(applications.next().is_none());
        });
    }
}
