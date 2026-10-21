// Scaling tests of `src/surface/proof/smart_execution.rs`: argument guard
// selection must visit the selected argument and indexed evidence, not ambient
// facts, source forms, or values.
use super::*;
use crate::surface::proof::pure_theorems::PureTheoremContext;

#[test]
fn model_argument_guard_selection_is_independent_of_unrelated_facts() {
    let parsed = crate::surface::parse(
        "spec enum Count { At(int32) } theorem accept(model: Count) { ensures model == model by simp(); }",
    ).unwrap();
    let theorem = &parsed.theorem_definitions()[0];
    let application = TheoremApplication {
        name: "accept".into(),
        arguments: vec![ContractExpression::AlgebraicConstructor {
            algebraic_type: AlgebraicTypeApplication {
                rigid: false,
                name: "Count".into(),
                arguments: vec![],
            },
            variant: "At".into(),
            arguments: vec![ContractExpression::Subtract(
                Box::new(ContractExpression::Binding("x".into())),
                Box::new(ContractExpression::IntegerLiteral("1".into())),
            )],
        }],
    };
    let guard = ClickProposition::Defined {
        expression: match &application.arguments[0] {
            ContractExpression::AlgebraicConstructor { arguments, .. } => arguments[0].clone(),
            _ => unreachable!(),
        },
    };
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::with_algebraic_types(
        parsed.click_function_definitions(),
        parsed.algebraic_type_definitions(),
    );
    let definitions = SpecDefinitions::new(&predicates, &functions);
    let theorems = TheoremEnvironment::new(parsed.theorem_definitions());
    let mut baseline = None;
    for size in [4usize, 16, 64, 256] {
        let mut values = BTreeMap::from([(
            "x".into(),
            CValue::Int32(crate::kernel::Bitvector32Term::Variable(
                crate::kernel::Variable(90_000),
            )),
        )]);
        let memory = crate::kernel::CMemory::new();
        let arrays = ClickArrayRefs::new();
        let lowered = lower_pure_theorem_proposition(
            "argument guard scaling",
            &guard,
            ContractEnvironment::new(&values, &arrays),
            &memory,
            definitions,
        )
        .unwrap();
        let mut requires = vec![lowered.clone()];
        let mut forms = SurfacePropositionMap::default();
        forms.record_lowering(&guard, &lowered).unwrap();
        for index in 0..size {
            let name = format!("unused_{index}");
            let value = CValue::Int32(crate::kernel::Bitvector32Term::Variable(
                crate::kernel::Variable(100_000 + index as u64),
            ));
            values.insert(name.clone(), value);
            let surface = ClickProposition::Comparison {
                left: ContractExpression::Binding(name),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::IntegerLiteral(index.to_string()),
            };
            let fact = lower_pure_theorem_proposition(
                "unrelated guard fact",
                &surface,
                ContractEnvironment::new(&values, &arrays),
                &memory,
                definitions,
            )
            .unwrap();
            forms.record_lowering(&surface, &fact).unwrap();
            requires.push(fact);
        }
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            memory: memory.clone(),
            values,
            integer_values: Default::default(),
            array_refs: arrays,
            requires: requires.clone(),
            surface_requirements: forms,
        };
        let root = Proof::for_pure_goal(
            "argument guard scaling",
            &requires,
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
            &context,
            definitions,
            &theorems,
        );
        let state = CState::new().with_memory(memory);
        let algebraic = BTreeMap::new();
        let snapshots = RecordedSnapshots::new();
        let application_context = TheoremApplicationContext {
            values: &context.values,
            array_refs: &context.array_refs,
            algebraic_values: &algebraic,
            pre_state: &state,
            post_state: &state,
            result: None,
            recorded_snapshots: &snapshots,
            integer_values: &context.integer_values,
            pointer_element_widths: BTreeMap::new(),
        };
        let ((result, persistent), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::persistent::measure_persistent_work(|| {
                    root.argument_guard_premises(theorem, &application, &application_context, &[])
                })
            });
        assert_eq!(result.unwrap(), vec![guard.clone()]);
        let (base_work, base_persistent) = *baseline.get_or_insert((work, persistent));
        // The cold smallest fixture may initialize selected-term caches;
        // growing unrelated context must never cost more than that fixture.
        assert!(
            work <= base_work,
            "{size} unrelated facts grew argument work from {base_work} to {work}"
        );
        let index_levels = (size + 1).ilog2() as usize + 1;
        let base_levels = (4usize + 1).ilog2() as usize + 1;
        assert!(
            persistent * base_levels <= base_persistent * index_levels,
            "{size} unrelated facts exceeded logarithmic index work: {base_persistent} -> {persistent}"
        );
        assert!(root.certificate().steps().is_empty());
    }
}
