#[test]
fn conclusion_index_ignores_unrelated_theorems_on_hits_and_misses() {
    let file = parser::parse("function selected(x: Integer) -> Integer { x } theorem law(x: Integer) { ensures selected(x) == x; } theorem probe(value: Integer) { ensures selected(value) == value; }").unwrap();
    let template = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = file.theorem_definitions()[1].ensures()[0].ensure() else { panic!() };
    for size in [0, 64, 256, 1024] {
        let mut index = TheoremConclusionIndex::default();
        for ordinal in 0..size {
            let mut theorem = template.clone();
            theorem.name = format!("unused{ordinal}");
            let Ensure::Proposition(ClickProposition::Comparison { left: ContractExpression::Call { name, .. }, .. }) = &mut theorem.ensures[0].ensure else { panic!() };
            *name = format!("unused_function{ordinal}");
            index.insert(&theorem, ordinal);
        }
        index.insert(template, size);
        let ((count, work), lookup_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| index.candidates(goal, usize::MAX).count())
        });
        assert_eq!(count, 1);
        assert_eq!(work, 5);
        assert!(lookup_work <= 64, "index scanned {size} unrelated theorems: {lookup_work}");
        let mut missing = goal.clone();
        let ClickProposition::Comparison { left: ContractExpression::Call { name, .. }, .. } = &mut missing else { panic!() };
        *name = "absent".into();
        let (count, work) = crate::persistent::measure_persistent_work(|| index.candidates(&missing, usize::MAX).count());
        assert_eq!(count, 0);
        assert!(work <= 64, "miss scanned {size} unrelated theorems: {work}");
    }
}

#[test]
fn conclusion_index_prefix_and_related_candidate_work_are_bounded() {
    let file = parser::parse("function selected(x: Integer) -> Integer { x } theorem law(x: Integer) { ensures selected(x) == x; }").unwrap();
    let template = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = template.ensures()[0].ensure() else { panic!() };
    for size in [8, 32, 128, 512] {
        let mut index = TheoremConclusionIndex::default();
        for ordinal in 0..size { index.insert(template, ordinal); }
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            index.candidates(goal, usize::MAX).map(|candidate| {
                assert!(match_theorem_conclusion(template, candidate.ensure, goal).is_some());
            }).count()
        });
        assert_eq!(count, size);
        assert!(work <= 8 * size + 4, "candidate matching was superlinear: {size}: {work}");
        assert_eq!(index.candidates(goal, size / 2).count(), size / 2);
        assert_eq!(index.candidates(goal, 0).count(), 0);
    }
}
