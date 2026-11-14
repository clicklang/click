//! Match spelling uses the same scoped names as nested folds. Only arm bodies
//! see their declarations; scrutinees are raised in the enclosing scope.
use super::*;
use crate::kernel::proof::term_rewrite::{BindingCarrier, typed_declaration_variable};
use crate::kernel::{KernelMatch, KernelTermExport, KernelType};

pub(super) fn raise_match(
    matched: &KernelMatch,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    folds::scope(|| {
        let KernelType::Algebraic(ty) = matched.arguments[0].ty() else {
            return None;
        };
        let scrutinee = raise_kernel_term(
            &matched.arguments[0],
            parameter_binding,
            state,
            bound_variables,
        )?;
        let mut export = KernelTermExport::default();
        let declarations = matched
            .arms
            .iter()
            .map(|arm| arm.export_bindings(&mut export))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let arms = raise_arms(
            &ty.name,
            matched
                .arms
                .iter()
                .zip(&declarations)
                .zip(&matched.arguments[1..])
                .map(|((arm, declarations), body)| {
                    (
                        arm.variant.as_str(),
                        &arm.binding_names,
                        declarations.as_slice(),
                        body,
                    )
                }),
            |body| raise_kernel_term(body, parameter_binding, state, bound_variables),
        )?;
        Some(SurfaceTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    })
}

struct ArmScope(Vec<folds::Binding>);
impl Drop for ArmScope {
    fn drop(&mut self) {
        while self.0.pop().is_some() {}
    }
}

fn raise_arms<'a, T: 'a>(
    type_name: &str,
    inputs: impl ExactSizeIterator<
        Item = (
            &'a str,
            &'a crate::kernel::BindingNames,
            &'a [crate::kernel::AlgebraicValue],
            &'a T,
        ),
    >,
    raise_body: impl Fn(&T) -> Option<SurfaceTerm>,
) -> Option<Vec<crate::surface::AlgebraicMatchArm>> {
    let mut arms = Vec::with_capacity(inputs.len());
    for (variant, binding_names, declarations, body) in inputs {
        let mut scopes = ArmScope(Vec::with_capacity(declarations.len()));
        let mut names = Vec::with_capacity(declarations.len());
        for (index, declaration) in declarations.iter().enumerate() {
            let (carrier, variable) = typed_declaration_variable(declaration)?;
            let carrier = match carrier {
                BindingCarrier::C => folds::BinderCarrier::C,
                BindingCarrier::Integer => folds::BinderCarrier::Integer,
                BindingCarrier::Algebraic => folds::BinderCarrier::Algebraic,
            };
            let name = folds::marker(binding_names.get(index));
            scopes
                .0
                .push(folds::Binding::enter((carrier, variable), name.clone()));
            names.push(name);
        }
        let body = raise_body(body)?;
        // Restore in reverse order, including repeated IDs in malformed inputs.
        drop(scopes);
        arms.push(crate::surface::AlgebraicMatchArm {
            type_name: type_name.to_string(),
            variant: variant.to_string(),
            bindings: names,
            body,
        });
    }
    Some(arms)
}

pub(super) fn raise_machine_match(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    let MachineTerm::AlgebraicMatch { scrutinee, arms } = term else {
        return None;
    };
    folds::scope(|| {
        let expression =
            synthesize_surface_algebraic(scrutinee, parameter_binding, state, bound_variables)?;
        let arms = raise_arms(
            &scrutinee.algebraic_type.name,
            arms.iter().map(|arm| {
                (
                    arm.variant.as_str(),
                    &arm.binding_names,
                    arm.bindings.as_slice(),
                    &arm.body,
                )
            }),
            |body| synthesize_surface_bitvector(body, parameter_binding, state, bound_variables),
        )?;
        Some(SurfaceTerm::AlgebraicMatch {
            scrutinee: Box::new(expression),
            arms,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType, BindingNames,
        IntegerTerm, KernelMatchArm, KernelTermImport, PureFunctionArgument,
    };

    #[test]
    fn common_match_surface_retains_each_result_carrier_and_written_name() {
        let variable = Variable(991950);
        let algebraic = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("Payload".into()),
            node: AlgebraicTermNode::Variable(variable),
        };
        for (ty, value) in [
            (
                AlgebraicValueType::C(ProgramType::Bool),
                PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::Variable(variable),
                ))),
            ),
            (
                AlgebraicValueType::Algebraic {
                    name: "Payload".into(),
                    arguments: vec![],
                },
                PureFunctionArgument::Value(ProgramValue::Parameter(Box::new(algebraic.clone()))),
            ),
            (
                AlgebraicValueType::C(ProgramType::Int32),
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(variable))),
            ),
            (
                AlgebraicValueType::C(ProgramType::UInt64),
                PureFunctionArgument::Value(ProgramValue::UInt64(MachineTerm::Variable(variable))),
            ),
            (
                AlgebraicValueType::Integer,
                PureFunctionArgument::Integer(IntegerTerm::Variable(variable).into()),
            ),
            (
                AlgebraicValueType::Algebraic {
                    name: "Payload".into(),
                    arguments: vec![],
                },
                PureFunctionArgument::Algebraic(algebraic),
            ),
        ] {
            let mut import = KernelTermImport::default();
            let scrutinee = KernelMatch::test_scrutinee(vec![ty]);
            let AlgebraicTermNode::Variable(scrutinee_id) = scrutinee.node else {
                panic!()
            };
            let scrutinee = import.argument(&PureFunctionArgument::Algebraic(scrutinee));
            let declaration = import.argument(&value);
            let body = match &value {
                PureFunctionArgument::Value(ProgramValue::Parameter(value)) => {
                    import.argument(&PureFunctionArgument::Algebraic((**value).clone()))
                }
                _ => declaration.clone(),
            };
            let matched = KernelMatch::new(
                body.ty().clone(),
                scrutinee,
                vec![(
                    KernelMatchArm {
                        variant: "Arm".into(),
                        bindings: vec![declaration],
                        binding_names: BindingNames::written(&["item".into()]),
                    },
                    body,
                )],
            )
            .unwrap();
            let names = BTreeMap::from([(scrutinee_id, "payload".into())]);
            let result = raise_match(
                &matched,
                ParameterBinding::default(),
                &ExecutionState::new(),
                &names,
            )
            .unwrap();
            let SurfaceTerm::AlgebraicMatch { scrutinee, arms } = result else {
                panic!()
            };
            assert_eq!(*scrutinee, SurfaceTerm::Binding("payload".into()));
            assert_eq!(arms[0].bindings, vec!["item"]);
            assert!(
                matches!(&arms[0].body, SurfaceTerm::Binding(name) | SurfaceTerm::CFragment(ProgramExpression::Variable(name)) if name == "item")
            );
            assert!(folds::scoped_binder_name(folds::BinderCarrier::Algebraic, variable).is_none());
            assert!(folds::binder_name(true, variable).is_none());
            assert!(folds::binder_name(false, variable).is_none());
        }
    }
    #[test]
    fn common_match_surface_separates_typed_ids_and_avoids_free_name_capture() {
        let mut import = KernelTermImport::default();
        let id = Variable(991960);
        let scrutinee = KernelMatch::test_scrutinee(vec![
            AlgebraicValueType::C(ProgramType::Int32),
            AlgebraicValueType::Integer,
        ]);
        let AlgebraicTermNode::Variable(scrutinee_id) = scrutinee.node else {
            panic!()
        };
        let scrutinee = import.argument(&PureFunctionArgument::Algebraic(scrutinee));
        let c = import.argument(&PureFunctionArgument::Value(ProgramValue::Int32(
            MachineTerm::Variable(id),
        )));
        let integer = import.integer(&IntegerTerm::Variable(id).into());
        let body = IntegerTerm::Add(
            IntegerTerm::Add(
                IntegerTerm::Variable(id).into(),
                IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::Variable(id))
                    .unwrap()
                    .into(),
            )
            .into(),
            IntegerTerm::Variable(Variable(991961)).into(),
        );
        let body = import.integer(&body.into());
        let matched = KernelMatch::new(
            KernelType::Integer,
            scrutinee,
            vec![(
                KernelMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![c, integer],
                    binding_names: BindingNames::written(&["item".into(), "integer_item".into()]),
                },
                body,
            )],
        )
        .unwrap();
        let names = BTreeMap::from([
            (scrutinee_id, "payload".into()),
            (Variable(991961), "item".into()),
        ]);
        let result = raise_match(
            &matched,
            ParameterBinding::default(),
            &ExecutionState::new(),
            &names,
        )
        .unwrap();
        let SurfaceTerm::AlgebraicMatch { arms, .. } = &result else {
            panic!()
        };
        assert_eq!(arms[0].bindings, vec!["__click_binder_0", "integer_item"]);
        let text = crate::surface::diagnostics::describe_contract_expression(&result);
        assert!(
            text.contains("to_integer((__click_binder_0 as int32))"),
            "{text}"
        );
        assert!(text.contains("integer_item"), "{text}");
        assert!(text.contains(" + item"), "{text}");
    }
}
