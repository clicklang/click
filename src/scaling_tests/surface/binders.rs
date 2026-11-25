use super::*;
use crate::surface::lowering::{ContractSubstitutions, SubstitutionSourceMap};
#[derive(Debug)]
struct Source {
    values: BTreeMap<String, SurfaceTerm>,
    queries: std::cell::Cell<usize>,
}
impl SubstitutionSourceMap for Source {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&SurfaceTerm> {
        self.queries.set(self.queries.get() + 1);
        name.named().and_then(|name| self.values.get(name))
    }
}
#[test]
fn typed_binder_freshening_scales_with_selected_replacements_and_ignores_ambient_names() {
    let mut baseline = Vec::new();
    for unrelated in [0, 128, 512] {
        let mut costs = Vec::new();
        for size in [4, 16, 64] {
            let mut source = Source {
                values: (0..unrelated)
                    .map(|i| {
                        (
                            format!("unrelated_{i}"),
                            SurfaceTerm::IntegerLiteral("0".into()),
                        )
                    })
                    .collect(),
                queries: Default::default(),
            };
            let mut parameters = Vec::new();
            let mut leaves = Vec::new();
            for i in 0..size {
                let name = format!("y{i}");
                source
                    .values
                    .insert(format!("x{i}"), SurfaceTerm::Binding(name.clone()));
                parameters.push((SurfaceBinder::from(name.clone()), ClickType::Integer));
                leaves.push(SurfaceTerm::Add(
                    Box::new(SurfaceTerm::Binding(format!("x{i}"))),
                    Box::new(SurfaceTerm::Binding(name)),
                ));
            }
            while leaves.len() > 1 {
                leaves = leaves
                    .chunks(2)
                    .map(|pair| {
                        SurfaceTerm::Add(Box::new(pair[0].clone()), Box::new(pair[1].clone()))
                    })
                    .collect();
            }
            let expression = SurfaceTerm::Lambda {
                parameters,
                result: ClickType::Integer,
                body: Box::new(leaves.pop().unwrap()),
            };
            let ((answer, allocations), work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    lowering::substitute_contract_expression(
                        &expression,
                        ContractSubstitutions::new(&source),
                    )
                    .unwrap()
                })
            });
            assert_eq!(source.queries.get(), size);
            assert_eq!(allocations, size);
            assert_eq!(
                lowering::contract_expression_referenced_bindings(&answer).len(),
                size
            );
            assert!(work > 0);
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(pair[1] <= 7 * pair[0], "{costs:?}");
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(costs, baseline);
        }
    }
}

#[derive(Debug)]
struct ReferenceSource {
    values: BTreeMap<crate::kernel::BindingName, SurfaceTerm>,
    queries: std::cell::Cell<usize>,
}
impl SubstitutionSourceMap for ReferenceSource {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&SurfaceTerm> {
        self.queries.set(self.queries.get() + 1);
        self.values.get(name)
    }
}
#[test]
fn reference_substitution_selects_only_its_carrier_and_keeps_lexical_captures_free() {
    use crate::kernel::BindingName;
    let carrier = BindingName::reference_carrier("x");
    let expression = SurfaceTerm::Lambda {
        parameters: vec![("y".into(), ClickType::Integer)],
        result: ClickType::Integer,
        body: Box::new(SurfaceTerm::ProgramExpression(ProgramExpression::Variable(
            carrier.clone(),
        ))),
    };
    let mut baseline = None;
    for size in [16, 64, 256, 1024] {
        let mut source = ReferenceSource {
            values: (0..size)
                .map(|i| {
                    (
                        BindingName::reference_carrier(format!("unused_{i}")),
                        SurfaceTerm::IntegerLiteral("0".into()),
                    )
                })
                .collect(),
            queries: Default::default(),
        };
        source
            .values
            .insert(carrier.clone(), SurfaceTerm::Binding("y".into()));
        let ((actual, work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                lowering::substitute_contract_expression(
                    &expression,
                    ContractSubstitutions::new(&source),
                )
                .unwrap()
            })
        });
        assert_eq!(source.queries.get(), 1);
        assert_eq!(
            lowering::contract_expression_referenced_bindings(&actual),
            BTreeSet::from([BindingName::from("y")])
        );
        assert!(work > 0 && persistent_work > 0);
        let cost = (work, persistent_work);
        assert_eq!(*baseline.get_or_insert(cost), cost);
    }
}

#[test]
fn interface_substitution_reads_only_referenced_proof_bindings() {
    use crate::kernel::BindingName;

    let generated = SurfaceBinder::fresh();
    let selected = SurfaceTerm::ProgramExpression(ProgramExpression::Value(int32(42)));
    let fact = SurfaceProposition::ForAll {
        name: "x".into(),
        written_name: None,
        click_type: ClickType::Integer,
        body: Box::new(SurfaceProposition::Comparison {
            left: SurfaceTerm::Binding("n".into()),
            operator: ComparisonOperator::Equal,
            right: SurfaceTerm::Binding("x".into()),
        }),
    };
    let resource = ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::View,
        kind: ResourceKind::Token,
        name: "observed".into(),
        arguments: vec![generated.reference()],
        parameter_types: vec![InterfaceType::Int32],
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut bindings: PersistentBinderMap<_> = (0..size)
            .map(|index| (format!("unused_{index}"), selected.clone()))
            .collect();
        bindings.insert("x", selected.clone());
        bindings.insert("n", SurfaceTerm::Binding("x".into()));
        bindings.insert(generated.clone(), selected.clone());
        let ((rewritten_fact, rewritten_resource), work) =
            crate::persistent::measure_persistent_work(|| {
                let substitutions = ContractSubstitutions::new(&bindings);
                (
                    lowering::substitute_click_proposition_in(&fact, &substitutions).unwrap(),
                    verification::substitute_resource_clause_for_summary_in(
                        &resource,
                        &substitutions,
                    )
                    .unwrap(),
                )
            });

        let mut free = BTreeSet::new();
        lowering::collect_click_proposition_referenced_bindings(&rewritten_fact, &mut free);
        assert_eq!(free, BTreeSet::from([BindingName::from("x")]));
        assert!(matches!(
            rewritten_resource,
            ResourceClause::Declared { arguments, .. } if arguments == [selected.clone()]
        ));
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "a fixed interface should read only its named bindings: {samples:?}"
    );
}
