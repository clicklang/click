//! The declaration-level protected assertion, without acquisition observations.

use super::*;
use crate::kernel::{
    AlgebraicValue, CMutexGuardDeclaration, CValue, ResourceDescription, ResourceInstance,
};
#[cfg(test)]
use std::collections::BTreeMap;

/// This description grants no ownership and retains neither an instance binder
/// nor its observed fields. Initialization identity and use authority must be
/// supplied separately before an abstract acquisition can use such an interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MutexInvariantInterface {
    description: ResourceDescription,
    mutex: Pointer,
}

impl MutexInvariantInterface {
    /// Initialization authenticates the protected assertion from an owned
    /// instance. A declaration may constrain the mutex, but is not itself
    /// the source of the association or of ownership.
    pub(super) fn check_definition(
        instance: &ResourceInstance,
        mutex: &Pointer,
        definition: &crate::kernel::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        if definition.name() != instance.name()
            || definition.instance_field_schema() != Some(instance.schema())
            || definition.parameters().len() != instance.arguments().len()
            || definition
                .parameters()
                .iter()
                .zip(instance.arguments())
                .any(|(parameter, argument)| {
                    argument.as_c_value().map(|value| value.c_type()) != Some(parameter.c_type())
                })
        {
            return Err("selected mutex resource does not match its declaration");
        }
        Self::check_association(instance, mutex, definition.mutex_guard(), assumptions)
    }

    #[cfg(test)]
    pub(super) fn check(
        instance: &ResourceInstance,
        mutex: &Pointer,
        declarations: &BTreeMap<String, CMutexGuardDeclaration>,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let declaration = declarations
            .get(instance.name())
            .ok_or("selected resource has no `guarded_by` mutex field")?;
        Self::check_association(instance, mutex, Some(declaration), assumptions)
    }

    fn check_association(
        instance: &ResourceInstance,
        mutex: &Pointer,
        declaration: Option<&CMutexGuardDeclaration>,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let Some(declaration) = declaration else {
            return Ok(Self {
                description: ResourceDescription::from_instance(instance),
                mutex: mutex.clone(),
            });
        };
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
            description: ResourceDescription::from_instance(instance),
            mutex: expected,
        })
    }

    pub(super) fn description(&self) -> &ResourceDescription {
        &self.description
    }

    pub(super) fn mutex(&self) -> &Pointer {
        &self.mutex
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CType, ResourceContext, ResourceFieldSchema, ResourceFieldType, Variable, int32,
    };

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

    fn definitions() -> BTreeMap<String, crate::kernel::CCompositeResourceDefinition> {
        let definition = crate::kernel::CCompositeResourceDefinition::new(
            "counter_state",
            vec![crate::kernel::CParameter::new("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )
        .with_instance_schema(Some(instance(1, 0).schema().clone()))
        .with_mutex_guard(declarations().remove("counter_state"));
        BTreeMap::from([("counter_state".into(), definition)])
    }

    #[test]
    fn unannotated_publication_requires_owned_state_and_preserves_its_type() {
        let assumptions = PureFactContext::new();
        let resource = instance(1, 7);
        let mut definitions = definitions();
        let definition = definitions.remove("counter_state").unwrap();
        definitions.insert("counter_state".into(), definition.with_mutex_guard(None));
        let context = MutexContext::new(
            CState::new()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(
                    CResourceFact::own(CResource::Instance(resource.clone())),
                )),
        );
        let mutex = Pointer::symbolic(Variable(99));
        let published = context
            .publish_declared(&mutex, resource.identity(), &definitions, &assumptions, 40)
            .unwrap();
        assert_eq!(
            published
                .state
                .mutex_ledger
                .as_ref()
                .unwrap()
                .protected_type(&mutex),
            Some(&ResourceDescription::from_instance(&resource))
        );
        assert!(
            published
                .publish_declared(
                    &address(),
                    resource.identity(),
                    &definitions,
                    &assumptions,
                    40
                )
                .is_err()
        );
        let (held, guard) = published.acquire(&mutex, &assumptions).unwrap();
        let released = held
            .release(
                guard,
                CResourceFact::own(CResource::Instance(resource.clone())),
                &assumptions,
            )
            .unwrap();
        let recovered = released.destroy(&mutex, &assumptions).unwrap();
        assert!(
            recovered
                .state
                .resources
                .owned_instance(resource.identity())
                .is_some()
        );
    }

    #[test]
    fn publication_rejects_unchecked_or_mismatched_schemas_without_annotations() {
        let assumptions = PureFactContext::new();
        let resource = instance(1, 7);
        let context = MutexContext::new(
            CState::new()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(
                    CResourceFact::own(CResource::Instance(resource.clone())),
                )),
        );
        assert!(
            context
                .publish_declared(
                    &address(),
                    resource.identity(),
                    &BTreeMap::new(),
                    &assumptions,
                    40
                )
                .is_err()
        );
        let mut definitions = definitions();
        let definition = definitions.remove("counter_state").unwrap();
        let wrong_schema = ResourceFieldSchema::new(vec![(
            "different".into(),
            ResourceFieldType::C(CType::Int32),
        )])
        .unwrap();
        definitions.insert(
            "counter_state".into(),
            definition
                .with_mutex_guard(None)
                .with_instance_schema(Some(wrong_schema)),
        );
        assert!(
            context
                .publish_declared(
                    &address(),
                    resource.identity(),
                    &definitions,
                    &assumptions,
                    40
                )
                .is_err()
        );
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
        assert_eq!(
            first.description(),
            &ResourceDescription::from_instance(&instance(1, 20))
        );
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
                    &definitions(),
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
                    &definitions(),
                    &assumptions,
                    40
                )
                .is_err()
        );
        let published = context
            .publish_declared(
                &address(),
                resource.identity(),
                &definitions(),
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
    fn published() -> (MutexContext, CResourceFact) {
        let resource = instance(1, 10);
        let fact = CResourceFact::own(CResource::Instance(resource.clone()));
        let context = MutexContext::new(
            CState::new()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(fact.clone())),
        );
        (
            context
                .publish_declared(
                    &address(),
                    resource.identity(),
                    &definitions(),
                    &PureFactContext::new(),
                    40,
                )
                .unwrap(),
            fact,
        )
    }

    fn binding(context: &MutexContext) -> Arc<InitializedMutexInterface> {
        context
            .state
            .mutex_ledger
            .as_ref()
            .unwrap()
            .get(&address())
            .unwrap()
            .interface()
            .unwrap()
            .clone()
    }

    #[test]
    fn declared_release_accepts_owned_replacement_with_the_full_description() {
        let assumptions = PureFactContext::new();
        let (published, original) = published();
        let replacement = CResourceFact::own(CResource::Instance(instance(2, 99)));
        let (mut held, guard) = published.acquire(&address(), &assumptions).unwrap();
        held.state.resources = held
            .state
            .resources
            .clone()
            .without_fact(&original, &assumptions)
            .unwrap()
            .try_compose_with_facts_delaying_normalization([replacement.clone()], &assumptions)
            .unwrap();
        let released = held
            .release(guard, replacement.clone(), &assumptions)
            .unwrap();
        assert!(
            !released
                .state
                .resources
                .contains_exact_representation(&replacement)
        );
        assert!(Arc::ptr_eq(&binding(&published), &binding(&released)));
        let (acquired, _) = released.acquire(&address(), &assumptions).unwrap();
        assert!(
            acquired
                .state
                .resources
                .contains_exact_representation(&replacement)
        );
        assert!(
            !acquired
                .state
                .resources
                .contains_exact_representation(&original)
        );
    }

    #[test]
    fn declared_release_requires_evidence_for_equal_description_arguments() {
        let assumptions = PureFactContext::new();
        let (published, original) = published();
        let mut replacement = instance(2, 99);
        let other = Pointer::symbolic(Variable(71));
        replacement.arguments = vec![CValue::pointer(other.clone()).into()].into();
        let replacement = CResourceFact::own(CResource::Instance(replacement));
        let (mut held, guard) = published.acquire(&address(), &assumptions).unwrap();
        held.state.resources = held
            .state
            .resources
            .clone()
            .without_fact(&original, &assumptions)
            .unwrap()
            .try_compose_with_facts_delaying_normalization([replacement.clone()], &assumptions)
            .unwrap();
        assert_eq!(
            held.release(
                MutexGuard {
                    mutex: guard.mutex.clone(),
                    initialization: guard.initialization,
                    epoch: guard.epoch,
                },
                replacement.clone(),
                &assumptions
            )
            .err(),
            Some(MutexTransitionError::MissingInvariant(original))
        );
        let equality = assumptions.assume_condition(
            crate::kernel::ConditionTerm::PointerEqual(
                Box::new(Pointer::symbolic(Variable(70))),
                Box::new(other),
            ),
            true,
        );
        let released = held.release(guard, replacement.clone(), &equality).unwrap();
        let (acquired, _) = released.acquire(&address(), &equality).unwrap();
        assert!(
            acquired
                .state
                .resources
                .contains_exact_representation(&replacement)
        );
    }

    #[test]
    fn declared_release_checks_schema_arguments_family_and_actual_ownership() {
        let assumptions = PureFactContext::new();
        let (published, original) = published();
        // An equal description alone is insufficient: this instance is not owned.
        let absent = CResourceFact::own(CResource::Instance(instance(2, 99)));
        let (held, guard) = published.acquire(&address(), &assumptions).unwrap();
        assert_eq!(
            held.release(guard, absent.clone(), &assumptions).err(),
            Some(MutexTransitionError::MissingInvariant(absent))
        );
        let mut wrong_family = instance(2, 99);
        wrong_family.name = "other_state".into();
        let mut wrong_arguments = instance(2, 99);
        wrong_arguments.arguments =
            vec![CValue::pointer(Pointer::symbolic(Variable(71))).into()].into();
        let mut wrong_schema = instance(2, 99);
        wrong_schema.schema =
            ResourceFieldSchema::new(vec![("other".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        for candidate in [wrong_family, wrong_arguments, wrong_schema] {
            let (mut held, guard) = published.acquire(&address(), &assumptions).unwrap();
            let candidate = CResourceFact::own(CResource::Instance(candidate));
            held.state.resources = held
                .state
                .resources
                .clone()
                .unchecked_with_fact(candidate.clone());
            assert_eq!(
                held.release(guard, candidate, &assumptions).err(),
                Some(MutexTransitionError::MissingInvariant(original.clone()))
            );
        }
    }

    #[test]
    fn initialized_interface_survives_exchange_but_not_reinitialization() {
        let assumptions = PureFactContext::new();
        let (published, fact) = published();
        let original = binding(&published);
        let ledger = published.state.mutex_ledger.as_ref().unwrap();
        assert_eq!(
            original.initialization,
            ledger.get(&address()).unwrap().initialization().0
        );
        let (held, guard) = published.acquire(&address(), &assumptions).unwrap();
        assert!(Arc::ptr_eq(&original, &binding(&held)));
        let released = held.release(guard, fact, &assumptions).unwrap();
        assert!(Arc::ptr_eq(&original, &binding(&released)));
        ledger
            .check_protocol_state_since(released.state.mutex_ledger.as_ref().unwrap())
            .unwrap();
        let destroyed = released.destroy(&address(), &assumptions).unwrap();
        assert!(destroyed.state.mutex_ledger.is_none());
        // Both initialization paths must accept the state after the last
        // initialization was destroyed, without rebuilding the context.
        let empty = destroyed.initialize_empty(address(), 40).unwrap();
        assert!(
            empty
                .state
                .mutex_ledger
                .as_ref()
                .unwrap()
                .get(&address())
                .unwrap()
                .interface()
                .is_none()
        );

        let republished = destroyed
            .publish_declared(
                &address(),
                crate::kernel::Variable(1),
                &definitions(),
                &assumptions,
                40,
            )
            .unwrap();
        let replacement = binding(&republished);
        assert_eq!(original.declaration, replacement.declaration);
        assert_ne!(original.initialization, replacement.initialization);
        assert!(!Arc::ptr_eq(&original, &replacement));
    }

    #[test]
    fn loop_continuity_rejects_replaced_or_removed_interface_binding() {
        let (published, _) = published();
        let before = published.state.mutex_ledger.as_ref().unwrap();
        for replacement in [None, Some(Arc::new((*binding(&published)).clone()))] {
            let mut entry = before.get(&address()).unwrap().clone();
            let MutexEntry::Unlocked { interface, .. } = &mut entry else {
                unreachable!()
            };
            *interface = replacement;
            let next = before.with_inserted(address(), entry);
            assert_eq!(
                before.check_protocol_state_since(&next),
                Err(MutexProtocolMismatch::State)
            );
        }
    }

    #[test]
    fn initialized_interface_exchange_scales_independently_of_resource_frame() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let (mut published, fact) = published();
            for index in 0..size {
                published.state.resources =
                    published
                        .state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let before = published.state.mutex_ledger.as_ref().unwrap();
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (held, guard) = published.acquire(&address(), &assumptions).unwrap();
                    let released = held.release(guard, fact, &assumptions).unwrap();
                    before
                        .check_protocol_state_since(released.state.mutex_ledger.as_ref().unwrap())
                        .unwrap();
                    released
                })
            });
            assert!(Arc::ptr_eq(&binding(&published), &binding(&returned)));
            assert_eq!(returned.state.resources.facts().len(), size + 1);
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "interface transport scans unrelated resources: {samples:?}"
            );
        }
    }
    #[test]
    fn preserving_use_calls_bind_concrete_interface_through_nested_reborrows() {
        use crate::kernel::loans::mutex_calls::MutexUseCallTransfer;
        let assumptions = PureFactContext::new();
        let (published, payload) = published();
        let protocols = published.state.mutex_ledger.as_ref().unwrap();
        let owner = protocols.live_resource(&address()).unwrap();
        let loans = LoanLedger::new();
        let caller = loans.fresh_participant().unwrap();
        let helper = loans.fresh_participant().unwrap();
        let nested = loans.fresh_participant().unwrap();
        let mut transfer = MutexUseCallTransfer::prepare(
            &loans,
            caller,
            helper,
            &published.state.resources,
            &owner,
            &assumptions,
        )
        .unwrap();
        transfer.bind_interface(protocols).unwrap();
        transfer.recheck_entry(&loans).unwrap();
        let usage = transfer
            .ledger
            .mutex_use_resource(transfer.usage, helper)
            .unwrap();
        assert!(binding(&published).matches_use(&usage));
        assert!(
            !transfer
                .callee_resources
                .contains_exact_representation(&payload)
        );
        assert!(
            !transfer
                .callee_resources
                .contains_exact_representation(&owner)
        );
        let mut child = MutexUseCallTransfer::prepare(
            &transfer.ledger,
            helper,
            nested,
            &transfer.callee_resources,
            &usage,
            &assumptions,
        )
        .unwrap();
        child.bind_interface(protocols).unwrap();
        let child_use = child
            .ledger
            .mutex_use_resource(child.usage, nested)
            .unwrap();
        assert!(binding(&published).matches_use(&child_use));
        let returned_child = child
            .finish(
                &child.ledger,
                nested,
                &child.callee_resources,
                &[],
                &assumptions,
            )
            .unwrap();
        let mut evidence = vec![child.entry_transition.clone()];
        evidence.extend(returned_child.exit_transitions);
        let returned = transfer
            .finish(
                &returned_child.ledger,
                helper,
                &returned_child.caller_resources,
                &evidence,
                &assumptions,
            )
            .unwrap();
        assert!(
            returned
                .caller_resources
                .contains_exact_representation(&owner)
        );
        assert!(
            !returned
                .caller_resources
                .contains_exact_representation(&payload)
        );
    }

    #[test]
    fn use_call_interface_rejects_stale_initialization_and_binding_erasure() {
        use crate::kernel::loans::mutex_calls::MutexUseCallTransfer;
        let assumptions = PureFactContext::new();
        let (first, _) = published();
        let (replacement, _) = published();
        let first_protocols = first.state.mutex_ledger.as_ref().unwrap();
        let owner = first_protocols.live_resource(&address()).unwrap();
        let loans = LoanLedger::new();
        let caller = loans.fresh_participant().unwrap();
        let helper = loans.fresh_participant().unwrap();
        let mut transfer = MutexUseCallTransfer::prepare(
            &loans,
            caller,
            helper,
            &first.state.resources,
            &owner,
            &assumptions,
        )
        .unwrap();
        assert!(
            transfer
                .bind_interface(replacement.state.mutex_ledger.as_ref().unwrap())
                .is_err()
        );
        transfer.bind_interface(first_protocols).unwrap();
        transfer.bind_interface(first_protocols).unwrap();
        let empty = MutexContext::new(CState::new());
        assert!(
            transfer
                .bind_interface(empty.state.mutex_ledger.as_ref().unwrap())
                .is_err()
        );
        // Failed rebinding leaves the original checked call usable.
        transfer
            .finish(
                &transfer.ledger,
                helper,
                &transfer.callee_resources,
                &[],
                &assumptions,
            )
            .unwrap();
    }
    #[test]
    fn use_interface_call_binding_scales_independently_of_resource_frame() {
        use crate::kernel::loans::mutex_calls::MutexUseCallTransfer;
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let (mut context, _) = published();
            for index in 0..size {
                context.state.resources =
                    context
                        .state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let protocols = context.state.mutex_ledger.as_ref().unwrap();
            let owner = protocols.live_resource(&address()).unwrap();
            let loans = LoanLedger::new();
            let caller = loans.fresh_participant().unwrap();
            let helper = loans.fresh_participant().unwrap();
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut transfer = MutexUseCallTransfer::prepare(
                        &loans,
                        caller,
                        helper,
                        &context.state.resources,
                        &owner,
                        &assumptions,
                    )
                    .unwrap();
                    transfer.bind_interface(protocols).unwrap();
                    transfer
                        .finish(
                            &transfer.ledger,
                            helper,
                            &transfer.callee_resources,
                            &[],
                            &assumptions,
                        )
                        .unwrap()
                })
            });
            assert_eq!(returned.caller_resources.facts().len(), size + 1);
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "use interface binding scans unrelated resources: {samples:?}"
            );
        }
    }
}
