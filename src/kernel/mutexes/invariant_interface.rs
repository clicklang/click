//! The declaration-level protected assertion, without acquisition observations.

use super::*;
use crate::kernel::{
    AlgebraicValue, CMutexGuardDeclaration, CValue, ResourceArguments, ResourceFieldSchema,
    ResourceInstance,
};
use std::collections::BTreeMap;

/// This description grants no ownership and retains neither an instance binder
/// nor its observed fields. Initialization identity and use authority must be
/// supplied separately before an abstract acquisition can use such an interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MutexInvariantInterface {
    family: String,
    arguments: ResourceArguments,
    schema: ResourceFieldSchema,
    mutex: Pointer,
}

impl MutexInvariantInterface {
    pub(super) fn check(
        instance: &ResourceInstance,
        mutex: &Pointer,
        declarations: &BTreeMap<String, CMutexGuardDeclaration>,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let declaration = declarations
            .get(instance.name())
            .ok_or("selected resource has no `guarded_by` mutex field")?;
        let Some(AlgebraicValue::C(CValue::Pointer(base))) =
            instance.arguments().get(declaration.parameter_index)
        else {
            return Err("guarded resource parameter is not a pointer");
        };
        let expected = base
            .pointer()
            .offset_by_bytes(declaration.field_offset_bytes);
        if !crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &expected,
            mutex,
            assumptions,
        ) {
            return Err("selected resource is guarded by a different mutex");
        }
        Ok(Self {
            family: instance.name.clone(),
            arguments: instance.arguments.clone(),
            schema: instance.schema.clone(),
            mutex: expected,
        })
    }

    pub(super) fn mutex(&self) -> &Pointer {
        &self.mutex
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{CType, ResourceContext, ResourceFieldType, Variable, int32};

    fn instance(identity: u64, value: u32) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            "counter_state".into(),
            vec![CValue::pointer(Pointer::symbolic(Variable(70))).into()].into(),
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap(),
            vec![int32(value).into()].into(),
        )
        .unwrap()
    }

    fn declarations() -> BTreeMap<String, CMutexGuardDeclaration> {
        BTreeMap::from([(
            "counter_state".into(),
            CMutexGuardDeclaration {
                parameter_index: 0,
                field_offset_bytes: 8,
            },
        )])
    }

    fn address() -> Pointer {
        Pointer::symbolic(Variable(70)).offset_by_bytes(8)
    }

    #[test]
    fn invariant_interface_retains_parameters_but_not_observed_values_or_binders() {
        let assumptions = PureFactContext::new();
        let first = MutexInvariantInterface::check(
            &instance(1, 10),
            &address(),
            &declarations(),
            &assumptions,
        )
        .unwrap();
        let later = MutexInvariantInterface::check(
            &instance(2, 20),
            &address(),
            &declarations(),
            &assumptions,
        )
        .unwrap();
        assert_eq!(first, later);
        let mut other_argument = instance(2, 20);
        other_argument.arguments =
            vec![CValue::pointer(Pointer::symbolic(Variable(71))).into()].into();
        assert!(
            MutexInvariantInterface::check(
                &other_argument,
                &address(),
                &declarations(),
                &assumptions
            )
            .is_err()
        );
    }

    #[test]
    fn invariant_interface_checks_family_parameter_and_exact_mutex_field() {
        let assumptions = PureFactContext::new();
        let resource = instance(1, 10);
        assert!(
            MutexInvariantInterface::check(&resource, &address(), &BTreeMap::new(), &assumptions)
                .is_err()
        );
        assert!(
            MutexInvariantInterface::check(
                &resource,
                &address().offset_by_bytes(8),
                &declarations(),
                &assumptions
            )
            .is_err()
        );
        let mut malformed = resource.clone();
        malformed.arguments = vec![int32(0).into()].into();
        assert!(
            MutexInvariantInterface::check(&malformed, &address(), &declarations(), &assumptions)
                .is_err()
        );
        malformed.arguments = vec![].into();
        assert!(
            MutexInvariantInterface::check(&malformed, &address(), &declarations(), &assumptions)
                .is_err()
        );
        let mut wrong_family = resource;
        wrong_family.name = "other_state".into();
        assert!(
            MutexInvariantInterface::check(
                &wrong_family,
                &address(),
                &declarations(),
                &assumptions
            )
            .is_err()
        );
    }

    #[test]
    fn declared_publication_requires_owned_folded_instance_and_escrows_it() {
        let assumptions = PureFactContext::new();
        let resource = instance(1, 10);
        let empty = MutexContext::new(CState::new());
        assert!(
            empty
                .publish_declared(
                    &address(),
                    resource.identity(),
                    &declarations(),
                    &assumptions,
                    40
                )
                .is_err()
        );
        let fact = CResourceFact::own(CResource::Instance(resource.clone()));
        let context = MutexContext::new(
            CState::new()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(fact.clone())),
        );
        assert!(
            context
                .publish_declared(
                    &address().offset_by_bytes(8),
                    resource.identity(),
                    &declarations(),
                    &assumptions,
                    40
                )
                .is_err()
        );
        let published = context
            .publish_declared(
                &address(),
                resource.identity(),
                &declarations(),
                &assumptions,
                40,
            )
            .unwrap();
        assert!(
            !published
                .state
                .resources
                .contains_exact_representation(&fact)
        );
        let (held, _) = published.acquire(&address(), &assumptions).unwrap();
        assert!(held.state.resources.contains_exact_representation(&fact));
    }
}
