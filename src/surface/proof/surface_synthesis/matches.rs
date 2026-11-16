//! Match spelling uses the same scoped names as nested folds. Only arm bodies
//! see their declarations; scrutinees are raised in the enclosing scope.
use super::*;
use crate::kernel::proof::term_rewrite::{BindingCarrier, typed_declaration_variable};
use crate::kernel::{KernelMatch, KernelTerm, KernelType};

pub(super) fn raise_match(
    matched: &KernelMatch,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
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
        let arms = raise_arms(
            &ty.name,
            matched
                .arms
                .iter()
                .zip(&matched.arguments[1..])
                .map(|(arm, body)| {
                    (
                        arm.variant.as_str(),
                        &arm.binding_names,
                        arm.bindings.as_slice(),
                        body,
                    )
                }),
            shared_declaration_variable,
            |body| raise_kernel_term(body, parameter_binding, state, bound_variables),
        )?;
        Some(SurfaceTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    })
}

// Declarations name a single typed variable. Read that declaration directly;
// neither arm bodies nor pointer producer metadata participate in its name.
fn shared_declaration_variable(term: &KernelTerm) -> Option<(BindingCarrier, Variable)> {
    use crate::kernel::{KernelMachineLiteral, KernelPointerOffset, KernelTermNode as N};
    crate::instrumentation::record_deterministic_work(1);
    let term = match term.node() {
        N::ProgramParameter { operand } => operand,
        _ => term,
    };
    if let N::Variable(variable) = term.node() {
        let carrier = match term.ty() {
            KernelType::Integer => BindingCarrier::Integer,
            KernelType::Algebraic(_) => BindingCarrier::Algebraic,
            KernelType::Bool => BindingCarrier::Program,
            KernelType::Program(
                ProgramType::Bool
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::Int32
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
                | ProgramType::Float32
                | ProgramType::Float64,
            ) => BindingCarrier::Program,
            _ => return None,
        };
        return Some((carrier, *variable));
    }
    let variable = match term.node() {
        N::PointerValue(value)
        | N::PointerRead { value, .. }
        | N::PointerArithmetic { value, .. }
        | N::PointerCall { value, .. } => {
            let address = value.node().address.node();
            if !matches!(address.offset.node(), KernelPointerOffset::Constant(0)) {
                return None;
            }
            match address.block.native_atom() {
                PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
                    *variable
                }
                _ => return None,
            }
        }
        // C's Boolean binder is the written conversion of one fresh word.
        N::BoolIf { arguments }
            if matches!(arguments[1].node(), N::BoolLiteral(false))
                && matches!(arguments[2].node(), N::BoolLiteral(true)) =>
        {
            let N::BoolCompare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                arguments,
            } = arguments[0].node()
            else {
                return None;
            };
            if !matches!(
                arguments[1].node(),
                N::MachineLiteral(KernelMachineLiteral::Word32(0))
            ) {
                return None;
            }
            let N::Variable(variable) = arguments[0].node() else {
                return None;
            };
            *variable
        }
        // Legacy carriers are already stored descriptors; borrow the declaration
        // reader without exporting a common tree or cloning its payload.
        N::Legacy(value) => {
            let crate::kernel::PureFunctionArgument::Value(value) = value.value() else {
                return None;
            };
            crate::kernel::proof::term_rewrite::program_declaration_variable(value)?
        }
        _ => return None,
    };
    Some((BindingCarrier::Program, variable))
}

struct ArmScope(Vec<folds::Binding>);
impl Drop for ArmScope {
    fn drop(&mut self) {
        while self.0.pop().is_some() {}
    }
}

fn raise_arms<'a, T: 'a, D: 'a>(
    type_name: &str,
    inputs: impl ExactSizeIterator<Item = (&'a str, &'a crate::kernel::BindingNames, &'a [D], &'a T)>,
    declaration_variable: impl Fn(&D) -> Option<(BindingCarrier, Variable)>,
    raise_body: impl Fn(&T) -> Option<SurfaceTerm>,
) -> Option<Vec<crate::surface::AlgebraicMatchArm>> {
    let mut arms = Vec::with_capacity(inputs.len());
    for (variant, binding_names, declarations, body) in inputs {
        let mut scopes = ArmScope(Vec::with_capacity(declarations.len()));
        let mut names = Vec::with_capacity(declarations.len());
        for (index, declaration) in declarations.iter().enumerate() {
            let (carrier, variable) = declaration_variable(declaration)?;
            let carrier = match carrier {
                BindingCarrier::Program => folds::BinderCarrier::Program,
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
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
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
            typed_declaration_variable,
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
    fn shared_declarations_preserve_native_carriers_and_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(991951);
        let word = MachineTerm::Variable(variable);
        let carrier = |value: Option<(BindingCarrier, Variable)>| {
            value.map(|(kind, variable)| {
                (
                    match kind {
                        BindingCarrier::Program => 0,
                        BindingCarrier::Integer => 1,
                        BindingCarrier::Algebraic => 2,
                    },
                    variable,
                )
            })
        };
        let mut values = vec![
            ProgramValue::Int32(word.clone()),
            ProgramValue::Int128(word.clone()),
            ProgramValue::Float32(word.clone()),
            ProgramValue::Bool(word.clone()),
            ProgramValue::typed_pointer(Pointer::symbolic(variable), ProgramType::Int32Pointer),
            ProgramValue::Int32(MachineTerm::constant(0)),
        ];
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            for zero in [MachineTerm::constant(0), MachineTerm::uint32_constant(0)] {
                values.push(ProgramValue::Bool(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::bool_not(ConditionTerm::Compare {
                        format,
                        relation: CompareRelation::Equal,
                        left: Box::new(word.clone()),
                        right: Box::new(zero),
                    }),
                )));
            }
        }
        for width in [MachineIntegerType::UInt8, MachineIntegerType::UInt32] {
            values.push(ProgramValue::Bool(MachineTerm::bool_cast(
                width,
                ConditionTerm::Variable(variable),
            )));
        }
        for value in values {
            let native = crate::kernel::AlgebraicValue::Program(value.clone());
            let root = KernelTermImport::default().argument(&PureFunctionArgument::Value(value));
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            assert_eq!(
                carrier(shared_declaration_variable(&root)),
                carrier(typed_declaration_variable(&native)),
                "{root:?}"
            );
            assert_eq!(
                crate::kernel::KernelTermExport::machine_export_count(),
                exports
            );
        }
    }

    #[test]
    fn common_match_surface_retains_each_result_carrier_and_typed_binding() {
        let variable = Variable(991950);
        let algebraic = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("Payload".into()),
            node: AlgebraicTermNode::Variable(variable),
        };
        for (ty, value) in [
            (
                AlgebraicValueType::Program(ProgramType::Bool),
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
                AlgebraicValueType::Program(ProgramType::Int32),
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(variable))),
            ),
            (
                AlgebraicValueType::Program(ProgramType::UInt64),
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
            assert!(matches!(
                arms[0].bindings.as_slice(),
                [SurfaceBinder::Generated(_)]
            ));
            assert_eq!(arms[0].body, arms[0].bindings[0].reference());
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
            AlgebraicValueType::Program(ProgramType::Int32),
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
        assert!(
            arms[0]
                .bindings
                .iter()
                .all(|name| matches!(name, SurfaceBinder::Generated(_)))
        );
        assert_ne!(arms[0].bindings[0], arms[0].bindings[1]);
        let text = crate::surface::diagnostics::describe_contract_expression(&result);
        assert!(
            text.contains(&format!("to_integer(({} as int32))", arms[0].bindings[0])),
            "{text}"
        );
        assert!(text.contains(&arms[0].bindings[1].to_string()), "{text}");
        assert!(text.contains(" + item"), "{text}");
    }
}
