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
