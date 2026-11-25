#[test]
fn retained_pure_citations_use_singletons_without_scanning_related_or_unrelated_sources() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let point = crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new());
    let value = MachineTerm::Variable(Variable(987_123));
    let values = ProgramValueBindings::from([("n".into(), ProgramValue::Int32(value))]);
    let source = SyntaxProposition::Comparison {
        left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("n".into())),
        operator: ComparisonOperator::GreaterEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let expected = super::super::pure_theorems::lower_pure_theorem_proposition(
        "retained citation",
        &source,
        ContractEnvironment::new(&values, &BTreeMap::new()),
        &point,
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    let context = super::super::pure_theorems::PureTheoremContext {
        diagnostic_names: Default::default(),
        declaration_bindings: BTreeMap::new(),
        point: point.clone(),
        values,
        integer_values: Default::default(),
        array_refs: BTreeMap::new(),
        requires: vec![expected.clone()],
        surface_requirements: Default::default(),
    };
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let root = Proof::for_pure_goal(
                "retained citation",
                &context.requires,
                Proposition::condition_is(ConditionTerm::Constant(true), true),
                &context,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
            );
            let mut proof = root.with_local_surface_fact(&source, &expected).unwrap();
            for index in 0..size {
                let different = SyntaxProposition::Comparison {
                    left: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("n".into())),
                    operator: ComparisonOperator::GreaterEqual,
                    right: SyntaxTerm::IntegerLiteral((index + 1).to_string()),
                };
                let fact = Proposition::condition_is(
                    ConditionTerm::IntegerLessEqual(
                        crate::kernel::IntegerTerm::constant_i64(index + 1).into(),
                        crate::kernel::IntegerTerm::var(Variable(988_000 + index as u64)).into(),
                    ),
                    true,
                );
                proof = proof
                    .with_local_surface_fact(if related { &source } else { &different }, &fact)
                    .unwrap();
            }
            let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.lower_cited_surface_proposition(&source, "retained citation")
            });
            assert_eq!(lowered.unwrap(), expected);
            // The index never gives authority to a missing premise.
            let missing = Proof::for_pure_goal(
                "missing citation",
                &[],
                Proposition::condition_is(ConditionTerm::Constant(true), true),
                &context,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
            )
            .with_local_surface_fact(&source, &expected)
            .unwrap();
            let lowered = missing
                .lower_cited_surface_proposition(&source, "missing citation")
                .unwrap();
            assert!(
                !missing
                    .facts()
                    .listed_premise_available(&lowered, &[], false)
            );
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 8),
            "source bucket scan (related={related}): {samples:?}"
        );
    }
}
