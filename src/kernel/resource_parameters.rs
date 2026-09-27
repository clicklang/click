//! Scoped description arguments, separate from selected owned occurrences.

use super::{
    AlgebraicValue, CExpression, CResource, CResourceFact, CResourceSnapshot, CResourceSpec,
    CResourceSpecError, CResourceTerm, CState, OpaqueResourceParameter, PureFactContext,
    ResourceDescription, Variable,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceParameterSubstitution {
    descriptions: Arc<BTreeMap<Variable, ResourceDescription>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceParameterError {
    Arity {
        expected: usize,
        supplied: usize,
    },
    DuplicateParameter(Variable),
    UnknownParameter(Variable),
    DuplicateOccurrence(Variable),
    MissingOwnership(Variable),
    UnsupportedDescriptionArgument {
        parameter: Variable,
        index: usize,
    },
    InvalidSpecification(CResourceSpecError),
    DescriptionMismatch {
        parameter: Variable,
        occurrence: Variable,
    },
}

impl ResourceParameterSubstitution {
    /// Capture exactly this declaration's arguments. This supplies no owned
    /// facts, and does not inspect or unfold a resource body.
    pub fn new(
        parameters: &[Variable],
        arguments: &[ResourceDescription],
    ) -> Result<Self, ResourceParameterError> {
        if parameters.len() != arguments.len() {
            return Err(ResourceParameterError::Arity {
                expected: parameters.len(),
                supplied: arguments.len(),
            });
        }
        let mut descriptions = BTreeMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            if descriptions.insert(*parameter, argument.clone()).is_some() {
                return Err(ResourceParameterError::DuplicateParameter(*parameter));
            }
        }
        Ok(Self {
            descriptions: Arc::new(descriptions),
        })
    }

    pub fn description(&self, parameter: Variable) -> Option<&ResourceDescription> {
        self.descriptions.get(&parameter)
    }

    /// Substitute captured descriptions into one resource clause. This is a
    /// syntax operation, not certification of a function or resource transfer.
    /// Ordinary clauses retain their metadata and are otherwise unchanged.
    pub fn instantiate_spec(
        &self,
        spec: &CResourceSpec,
    ) -> Result<CResourceSpec, ResourceParameterError> {
        let Some((parameter, identity, binder)) = spec.parameter_binding() else {
            return Ok(spec.clone());
        };
        let description = self
            .description(parameter)
            .ok_or(ResourceParameterError::UnknownParameter(parameter))?;
        let mut arguments = Vec::with_capacity(description.arguments().len());
        let mut parameter_types = Vec::with_capacity(description.arguments().len());
        for (index, argument) in description.arguments().iter().enumerate() {
            let AlgebraicValue::C(value) = argument else {
                // Existing C resource clauses have C-typed ordinary arguments.
                // Do not cast logical arguments to machine values to fit them.
                return Err(ResourceParameterError::UnsupportedDescriptionArgument {
                    parameter,
                    index,
                });
            };
            parameter_types.push(value.c_type());
            arguments.push(CExpression::Value(value.clone()));
        }
        let term = CResourceTerm::Instance {
            identity,
            binder: binder.to_owned(),
            schema: description.schema().clone(),
            resource: Box::new(CResourceTerm::Composite {
                name: description.family().to_owned(),
                argument_snapshots: vec![CResourceSnapshot::Entry; arguments.len()],
                arguments,
                parameter_types,
            }),
        };
        let mut result = CResourceSpec::new(
            term,
            spec.access(),
            spec.quantity().clone(),
            spec.role(),
            spec.snapshot(),
        )
        .map_err(ResourceParameterError::InvalidSpecification)?;
        if let Some(guard) = spec.guard() {
            result = result.with_guard(guard.clone());
        }
        if let Some((index, total)) = spec.clause_position() {
            result = result.with_clause_position(index, total);
        }
        if let Some(arguments) = spec.source_arguments() {
            result = result.with_source_arguments(arguments.to_vec());
        }
        Ok(result)
    }

    /// Select a whole input map against actual ownership. Two formal owned
    /// occurrences cannot be supplied by the same actual occurrence, even
    /// when their descriptions agree. No resource transfer happens here;
    /// the ordinary call transition must consume the returned checked inputs.
    pub fn check_inputs(
        &self,
        inputs: &[(OpaqueResourceParameter, Variable)],
        state: &CState,
        assumptions: &PureFactContext,
    ) -> Result<Vec<CResourceFact>, ResourceParameterError> {
        let mut formals = BTreeSet::new();
        let mut actuals = BTreeSet::new();
        let mut facts = Vec::with_capacity(inputs.len());
        for (formal, actual) in inputs {
            let description = self
                .description(formal.parameter())
                .ok_or(ResourceParameterError::UnknownParameter(formal.parameter()))?;
            if !formals.insert(formal.occurrence()) {
                return Err(ResourceParameterError::DuplicateOccurrence(
                    formal.occurrence(),
                ));
            }
            if !actuals.insert(*actual) {
                return Err(ResourceParameterError::DuplicateOccurrence(*actual));
            }
            let instance = state
                .owned_resource_instance(*actual)
                .ok_or(ResourceParameterError::MissingOwnership(*actual))?;
            if !description.matches_instance(instance, assumptions) {
                return Err(ResourceParameterError::DescriptionMismatch {
                    parameter: formal.parameter(),
                    occurrence: *actual,
                });
            }
            facts.push(CResourceFact::own(CResource::Instance(instance.clone())));
        }
        Ok(facts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CType, ResourceContext, ResourceFieldSchema, ResourceFieldType, ResourceInstance, int32,
    };

    fn instance(identity: u64, argument: u32) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            "state".into(),
            vec![int32(argument).into()].into(),
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap(),
            vec![int32(10).into()].into(),
        )
        .unwrap()
    }

    #[test]
    fn substitution_captures_arguments_and_retains_the_owned_binder_and_transfer() {
        use crate::kernel::CResourceTransferRole;
        let description = ResourceDescription::from_instance(&instance(20, 7));
        let substitution =
            ResourceParameterSubstitution::new(&[Variable(1)], &[description]).unwrap();
        let input = CResourceSpec::parameter(
            Variable(1),
            Variable(10),
            "item".into(),
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap()
        .with_clause_position(2, 4);
        let output = input.clone().with_snapshot(CResourceSnapshot::Post);
        let resolved = substitution.instantiate_spec(&input).unwrap();
        assert_eq!(resolved.instance_identity(), Some(Variable(10)));
        assert_eq!(resolved.instance_binder(), Some("item"));
        assert_eq!(resolved.role(), CResourceTransferRole::Borrow);
        assert_eq!(resolved.clause_position(), Some((2, 4)));
        let CResourceTerm::Instance { resource, .. } = resolved.term() else {
            panic!("concrete instance")
        };
        let CResourceTerm::Composite {
            name, arguments, ..
        } = resource.as_ref()
        else {
            panic!("captured description")
        };
        assert_eq!(name, "state");
        assert_eq!(arguments, &[CExpression::Value(int32(7))]);
        let resolved_output = substitution.instantiate_spec(&output).unwrap();
        assert_eq!(resolved_output.snapshot(), CResourceSnapshot::Post);
        assert_eq!(resolved_output.instance_identity(), Some(Variable(10)));
        // Substitution exposes a schema, never entry observations. The
        // ordinary call return will mint fields for this output occurrence.
        assert_eq!(
            resolved.instance_schema(),
            resolved_output.instance_schema()
        );
    }

    #[test]
    fn description_arguments_do_not_supply_ownership_or_cross_parameter_scopes() {
        let instance = instance(20, 7);
        let description = ResourceDescription::from_instance(&instance);
        let substitution =
            ResourceParameterSubstitution::new(&[Variable(1)], std::slice::from_ref(&description))
                .unwrap();
        let formal = OpaqueResourceParameter::new(Variable(1), Variable(10));
        let assumptions = PureFactContext::new();
        assert_eq!(
            substitution.check_inputs(
                &[(formal.clone(), Variable(20))],
                &CState::new(),
                &assumptions
            ),
            Err(ResourceParameterError::MissingOwnership(Variable(20)))
        );
        let fact = CResourceFact::own(CResource::Instance(instance));
        let state = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(fact.clone()));
        assert_eq!(
            substitution
                .check_inputs(&[(formal, Variable(20))], &state, &assumptions)
                .unwrap(),
            vec![fact]
        );
        assert_eq!(
            substitution.check_inputs(
                &[(
                    OpaqueResourceParameter::new(Variable(2), Variable(10)),
                    Variable(20)
                )],
                &state,
                &assumptions
            ),
            Err(ResourceParameterError::UnknownParameter(Variable(2)))
        );
        assert_eq!(
            ResourceParameterSubstitution::new(&[Variable(1)], &[]),
            Err(ResourceParameterError::Arity {
                expected: 1,
                supplied: 0
            })
        );
        assert_eq!(
            ResourceParameterSubstitution::new(
                &[Variable(1), Variable(1)],
                &[description.clone(), description]
            ),
            Err(ResourceParameterError::DuplicateParameter(Variable(1)))
        );
    }

    #[test]
    fn repeated_parameter_requires_separate_owned_occurrences_with_matching_descriptions() {
        let first = instance(20, 7);
        let second = instance(21, 7);
        let wrong = instance(22, 8);
        let substitution = ResourceParameterSubstitution::new(
            &[Variable(1)],
            &[ResourceDescription::from_instance(&first)],
        )
        .unwrap();
        let state = CState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts(
                [first, second, wrong]
                    .into_iter()
                    .map(|instance| CResourceFact::own(CResource::Instance(instance))),
            ),
        );
        let a = OpaqueResourceParameter::new(Variable(1), Variable(10));
        let b = OpaqueResourceParameter::new(Variable(1), Variable(11));
        let assumptions = PureFactContext::new();
        assert_eq!(
            substitution.check_inputs(
                &[(a.clone(), Variable(20)), (b.clone(), Variable(20))],
                &state,
                &assumptions
            ),
            Err(ResourceParameterError::DuplicateOccurrence(Variable(20)))
        );
        assert_eq!(
            substitution.check_inputs(
                &[(a.clone(), Variable(20)), (a.clone(), Variable(21))],
                &state,
                &assumptions
            ),
            Err(ResourceParameterError::DuplicateOccurrence(Variable(10)))
        );
        assert_eq!(
            substitution.check_inputs(&[(a.clone(), Variable(22))], &state, &assumptions),
            Err(ResourceParameterError::DescriptionMismatch {
                parameter: Variable(1),
                occurrence: Variable(22)
            })
        );
        assert_eq!(
            substitution
                .check_inputs(
                    &[(a, Variable(20)), (b, Variable(21))],
                    &state,
                    &assumptions
                )
                .unwrap()
                .len(),
            2
        );
    }
}
