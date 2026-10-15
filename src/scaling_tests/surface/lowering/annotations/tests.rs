// Scaling tests of `src/surface/lowering/annotations/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_certificate_lowering_scales_with_nodes_not_unrelated_bindings() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let surface = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(ContractExpression::Binding("x".into())),
            Box::new(ContractExpression::IntegerLiteral("1".into())),
        ),
        operator: ComparisonOperator::GreaterThan,
        right: ContractExpression::Binding("x".into()),
    };
    let mut costs = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut bindings = crate::persistent::PersistentMap::default();
        bindings = bindings.with_inserted(
            "x".into(),
            SpecIntegerExpression::Term(IntegerTerm::var(Variable(7))),
        );
        for index in 0..unrelated {
            bindings = bindings.with_inserted(
                format!("unused{index}"),
                SpecIntegerExpression::Term(IntegerTerm::var(Variable(index + 100))),
            );
        }
        let mut node_costs = Vec::new();
        for nodes in [8, 16, 32, 64] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..nodes {
                    lower_integer_certificate_proposition(&surface, &bindings).unwrap();
                }
            });
            node_costs.push(work);
        }
        for pair in node_costs.windows(2) {
            assert_eq!(pair[1], 2 * pair[0]);
        }
        costs.push(node_costs[0]);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn proposition_snapshot_selection_matches_full_context_without_unrelated_bindings() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let entry = CState::new().with_local("used", int32(1));
    let atom = |expression| ClickProposition::Comparison {
        left: expression,
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Binding("late".into()),
    };
    let proposition = ClickProposition::And(
        Box::new(atom(ContractExpression::At {
            selector: SnapshotSelector::Mark("before".into()),
            expression: Box::new(ContractExpression::Binding("used".into())),
        })),
        Box::new(atom(ContractExpression::Old(Box::new(
            ContractExpression::Binding("used".into()),
        )))),
    );
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = CState::new().with_local("used", int32(2));
        for index in 0..size {
            state = state.with_local(format!("unused{index}"), int32(index));
        }
        let mut snapshots = RecordedSnapshots::new();
        snapshots.insert(SnapshotSelector::Mark("before".into()), state);
        let (mut lowerer, context) = fixed_state_elaboration(
            BTreeMap::new(),
            BTreeMap::new(),
            &entry,
            BTreeMap::from([("used".into(), int32(1))]),
            BTreeMap::from([("used".into(), int32(9)), ("late".into(), int32(3))]),
            None,
            &snapshots,
            SpecDefinitions::new(&predicates, &functions),
            BTreeSet::new(),
            BTreeMap::new(),
        );
        let reference = lowerer
            .click_proposition_to_spec_proposition(&proposition, &context)
            .unwrap();
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(&proposition, &mut names);
        lowerer.capture_referenced_names = Some(names);
        let ((selected, projected), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let selected = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                let projected = lowerer
                    .snapshot_environment(&SnapshotSelector::Mark("before".into()), &context)
                    .unwrap()
                    .unwrap();
                (selected, projected)
            });
        assert_eq!(selected, reference);
        assert_eq!(projected.values.len(), 2);
        assert!(
            matches!(projected.values.get(&"used".to_string()), Some(SpecExpression::Value(value)) if value == &int32(2))
        );
        assert!(
            matches!(projected.values.get(&"late".to_string()), Some(SpecExpression::Value(value)) if value == &int32(3))
        );
        costs.push(work);
    }
    assert!(
        costs.iter().all(|cost| *cost == costs[0]),
        "snapshot selection costs: {costs:?}"
    );
}
