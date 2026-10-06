//! Local mutex custody for a counted body. External units are opaque while
//! unlocked. This slice cannot lend use authority or transfer units to workers.
use super::*;
use crate::kernel::{
    Bitvector32Term, CCompositeResourceDefinition, CExpression, CResourceAccessMode, CResourceTerm,
    ExecutionBudget, ResourceArguments, ResourceContext, ResourceInstance,
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PopulationCustody {
    name: String,
    arguments: ResourceArguments,
    definition: Arc<CCompositeResourceDefinition>,
}

impl PopulationCustody {
    pub(super) fn key(&self) -> (String, ResourceArguments) {
        (self.name.clone(), self.arguments.clone())
    }

    pub(super) fn select(
        state: &CState,
        instance: &ResourceInstance,
        definition: &CCompositeResourceDefinition,
        definitions: &BTreeMap<String, CCompositeResourceDefinition>,
        assumptions: &PureFactContext,
    ) -> Result<Option<Self>, &'static str> {
        let mut selected = None;
        for spec in &definition.contains {
            let CResourceTerm::Composite {
                name, arguments, ..
            } = spec.term()
            else {
                continue;
            };
            let Some(child) = definitions.get(name) else {
                continue;
            };
            if !child.is_thread_confined() {
                continue;
            }
            if selected.is_some() || definition.contains.len() != 1
                || !child.is_counted_population() || child.recursive || child.matched.is_some()
                || child.condition.is_some() || !child.children.is_empty() || !child.witnesses.is_empty()
                || child.contains.iter().any(|c| c.family() != crate::kernel::ResourceFamily::Memory)
                || definition.recursive || definition.condition.is_some() || definition.matched.is_some()
                || !definition.children.is_empty() || !definition.witnesses.is_empty()
                || spec.access() != CResourceAccessMode::Own
                || spec.guard().is_some()
                || arguments.iter().any(|a| !matches!(a, CExpression::Variable(name) if definition.parameters().iter().any(|p| p.name() == name)))
            {
                return Err("counted mutex body requires one unconditional population with parameter-only arguments");
            }
            let evaluation =
                crate::kernel::functions::instance_body_evaluation(state, instance, definition)?;
            let fact = crate::kernel::functions::evaluate_function_resource_spec(
                &evaluation,
                spec,
                assumptions,
                &mut ExecutionBudget::beside_live_state(),
            )
            .map_err(|_| "counted mutex body evaluation exceeded its budget")?
            .map_err(|_| "could not evaluate the counted mutex body")?;
            let CResource::Composite { name, arguments } = fact.resource() else {
                unreachable!()
            };
            let (name, arguments, _) = state
                .counted_population_proven_equal(name, arguments, assumptions)
                .ok_or("Requires a current count for the protected population")?;
            if state.mutex_ledger.as_ref().is_some_and(|l| {
                l.storage
                    .populations
                    .contains_key(&(name.clone(), arguments.clone()))
            }) {
                return Err("population already has a mutex custodian");
            }
            let population = Self {
                name,
                arguments,
                definition: Arc::new(definition.clone()),
            };
            population.check_closed(state, assumptions)?;
            population.check_complete(
                state,
                &state.resources,
                &population.body(),
                &fact,
                assumptions,
            )?;
            selected = Some(population);
        }
        if selected.is_none() && definition.is_thread_confined() {
            return Err("nested counted mutex bodies are not implemented");
        }
        Ok(selected)
    }

    fn body(&self) -> CResource {
        CResource::Composite {
            name: self.name.clone(),
            arguments: self.arguments.clone(),
        }
    }

    fn quantity(
        &self,
        resources: &ResourceContext,
        resource: &CResource,
        assumptions: &PureFactContext,
    ) -> Result<Bitvector32Term, &'static str> {
        let mut total = 0u32.into();
        for fact in resources.exact_resource_facts(resource) {
            let quantity = fact
                .owned_quantity_term()
                .ok_or("population body has an outstanding view")?;
            total = crate::kernel::population_quantity_sum(&total, quantity, assumptions)
                .ok_or("Requires a representable owned population quantity")?;
        }
        Ok(total)
    }

    fn check_closed(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
    ) -> Result<(), &'static str> {
        if state.population_body_is_open(&self.name, &self.arguments, assumptions) {
            return Err("Requires the protected population body to be closed");
        }
        if state
            .population_effects
            .pending_counts
            .get(&self.name, &self.arguments, false)
            .is_some()
        {
            return Err("counted mutex custody with pending workers is not implemented");
        }
        Ok(())
    }

    fn contained(
        &self,
        state: &CState,
        payload: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<CResourceFact, &'static str> {
        let CResource::Instance(instance) = payload.resource() else {
            return Err("Requires the folded population wrapper");
        };
        let evaluation =
            crate::kernel::functions::instance_body_evaluation(state, instance, &self.definition)?;
        let fact = crate::kernel::functions::evaluate_function_resource_spec(
            &evaluation,
            &self.definition.contains[0],
            assumptions,
            &mut ExecutionBudget::beside_live_state(),
        )
        .map_err(|_| "counted mutex body evaluation exceeded its budget")?
        .map_err(|_| "could not evaluate the counted mutex body")?;
        if fact.resource() != &self.body() {
            return Err("Requires the original protected population");
        }
        Ok(fact)
    }

    fn check_complete(
        &self,
        state: &CState,
        resources: &ResourceContext,
        from: &CResource,
        contained: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<(), &'static str> {
        let count = state
            .counted_population(&self.name, &self.arguments)
            .ok_or("Requires a current count for the protected population")?;
        let escrow = contained
            .owned_quantity_term()
            .ok_or("Requires ownership of the protected population")?;
        let external = self.quantity(resources, from, assumptions)?;
        if assumptions.decide(&ConditionTerm::signed_less_than(
            0u32.into(),
            escrow.clone(),
        )) != Some(true)
            || assumptions.decide(&ConditionTerm::signed_less_equal(
                0u32.into(),
                external.clone(),
            )) != Some(true)
            || assumptions.decide(&ConditionTerm::signed_less_than(0u32.into(), count.clone()))
                != Some(true)
            || assumptions.decide(&ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::add(external, escrow.clone())),
                Box::new(count.clone()),
            )) != Some(true)
        {
            return Err(
                "Requires ownership of the complete protected population (owned quantity == count)",
            );
        }
        Ok(())
    }

    pub(super) fn exchange(
        &self,
        state: &CState,
        mut resources: ResourceContext,
        authority: &crate::kernel::MutexIdentity,
        payload: &CResourceFact,
        expose: bool,
        assumptions: &PureFactContext,
    ) -> Result<ResourceContext, &'static str> {
        self.check_closed(state, assumptions)?;
        let member = CResource::GuardedPopulation {
            name: self.name.clone(),
            arguments: self.arguments.clone(),
            mutex: authority.clone(),
        };
        let (from, to) = if expose {
            (member, self.body())
        } else {
            (self.body(), member)
        };
        let contained = self.contained(state, payload, assumptions)?;
        self.check_complete(state, &resources, &from, &contained, assumptions)?;
        for fact in resources.exact_resource_facts(&from) {
            let quantity = fact.owned_quantity_term().unwrap().clone();
            resources = resources
                .without_fact_delaying_normalization(&fact, assumptions)
                .ok_or("protected population ownership changed during transfer")?;
            resources = resources
                .try_compose_with_facts_delaying_normalization(
                    [CResourceFact::Own(to.clone(), Box::new(quantity))],
                    assumptions,
                )
                .map_err(|_| "protected population units conflict with current ownership")?;
        }
        Ok(resources)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CParameter, CResourceSpec, CType, CValue, ResourceFieldSchema, ResourceFieldType,
        SpecProposition, Variable, int32,
    };

    fn fixture(
        unrelated: usize,
        total: u32,
    ) -> (
        MutexContext,
        ResourceInstance,
        BTreeMap<String, CCompositeResourceDefinition>,
        CResource,
    ) {
        let parameter = CParameter::new("p", CType::Int32Pointer);
        let arguments: ResourceArguments =
            vec![CValue::pointer(Pointer::symbolic(Variable(71))).into()].into();
        let body = CResource::Composite {
            name: "member".into(),
            arguments: arguments.clone(),
        };
        let population = CCompositeResourceDefinition::counted_population(
            "member",
            vec![parameter.clone()],
            None,
            vec![],
            vec![SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "population_property".into(),
                arguments: vec![],
            }],
        );
        let schema =
            ResourceFieldSchema::new(vec![("model".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let wrapper = CCompositeResourceDefinition::new(
            "wrapper",
            vec![parameter],
            None,
            false,
            vec![CResourceSpec::composite(
                CResourceAccessMode::Own,
                "member".into(),
                vec![CExpression::Variable("p".into())],
                vec![CType::Int32Pointer],
            )],
            vec![],
        )
        .with_instance_schema(Some(schema.clone()));
        let instance = ResourceInstance::new(
            Variable(72),
            "wrapper".into(),
            arguments.clone(),
            schema,
            vec![int32(0).into()].into(),
        )
        .unwrap();
        let mut resources = ResourceContext::new().unchecked_with_facts([
            CResourceFact::own(CResource::Instance(instance.clone())),
            CResourceFact::Own(body.clone(), Box::new(2u32.into())),
        ]);
        for i in 0..unrelated {
            resources = resources.unchecked_with_fact(CResourceFact::own(CResource::Token {
                name: format!("unrelated-{i}"),
                arguments: Arc::from([]),
            }));
        }
        let state = CState::new()
            .with_resource_context(resources)
            .with_counted_population("member", arguments, total.into());
        (
            MutexContext::new(state),
            instance,
            BTreeMap::from([("member".into(), population), ("wrapper".into(), wrapper)]),
            body,
        )
    }

    #[test]
    fn authority_mode_publication_takes_no_population_custody() {
        let (context, instance, definitions, body) = fixture(0, 3);
        let context = MutexContext::new(context.state.with_population_creation_tracking());
        let assumptions = PureFactContext::new();
        let mutex = Pointer::symbolic(Variable(70));
        let unit = CResourceFact::Own(body, Box::new(2u32.into()));
        let no_custody = |state: &CState| {
            state
                .mutex_ledger
                .as_ref()
                .is_none_or(|ledger| ledger.storage.populations.is_empty())
                && state.resources.satisfies_fact(&unit, &assumptions)
        };
        let published = context
            .publish_declared(&mutex, instance.identity(), &definitions, &assumptions, 40)
            .unwrap();
        assert!(no_custody(&published.state));
        let Some(MutexEntry::Unlocked {
            interface: Some(interface),
            ..
        }) = published.state.mutex_ledger.as_ref().unwrap().get(&mutex)
        else {
            panic!("authority-mode publication deposits a declared invariant");
        };
        assert!(interface.declaration.population.is_none());
        assert_eq!(
            super::super::missing_population_guard(&published.state, &unit, &assumptions),
            None
        );
        let (held, guard) = published.acquire(&mutex, &assumptions).unwrap();
        assert!(no_custody(&held.state));
        let released = held
            .release(
                guard,
                CResourceFact::own(CResource::Instance(instance.clone())),
                &assumptions,
            )
            .unwrap();
        assert!(no_custody(&released.state));
        let recovered = released.destroy(&mutex, &assumptions).unwrap();
        assert!(no_custody(&recovered.state));
        assert!(
            recovered
                .state
                .resources
                .owned_instance(instance.identity())
                .is_some()
        );
    }

    #[test]
    fn publication_revokes_units_and_destroy_restores_the_same_population() {
        let (context, instance, definitions, body) = fixture(0, 3);
        let assumptions = PureFactContext::new();
        let mutex = Pointer::symbolic(Variable(70));
        let published = context
            .publish_declared(&mutex, instance.identity(), &definitions, &assumptions, 40)
            .unwrap();
        let unit = CResourceFact::own(body.clone());
        assert!(
            !published
                .state
                .resources
                .satisfies_fact(&unit, &assumptions)
        );
        assert_eq!(
            super::super::missing_population_guard(&published.state, &unit, &assumptions),
            Some(mutex.clone())
        );
        assert!(published.lend_use(&mutex, &assumptions).is_err());
        let (held, guard) = published.acquire(&mutex, &assumptions).unwrap();
        assert!(held.state.resources.satisfies_fact(&unit, &assumptions));
        assert!(
            held.publish_declared(
                &Pointer::symbolic(Variable(73)),
                instance.identity(),
                &definitions,
                &assumptions,
                40
            )
            .is_err()
        );
        let released = held
            .release(
                guard,
                CResourceFact::own(CResource::Instance(instance.clone())),
                &assumptions,
            )
            .unwrap();
        assert!(!released.state.resources.satisfies_fact(&unit, &assumptions));
        let recovered = released.destroy(&mutex, &assumptions).unwrap();
        assert!(
            recovered
                .state
                .resources
                .satisfies_fact(&unit, &assumptions)
        );
        assert!(
            recovered
                .state
                .resources
                .owned_instance(instance.identity())
                .is_some()
        );
        assert_eq!(
            recovered
                .state
                .counted_population("member", instance.arguments()),
            Some(&3u32.into())
        );
    }

    #[test]
    fn incomplete_population_cannot_be_published() {
        let (context, instance, definitions, _) = fixture(0, 4);
        assert!(
            context
                .publish_declared(
                    &Pointer::symbolic(Variable(70)),
                    instance.identity(),
                    &definitions,
                    &PureFactContext::new(),
                    40
                )
                .is_err()
        );
    }

    #[test]
    fn guarded_membership_is_not_body_authority_or_a_different_initialization() {
        let arguments: ResourceArguments = Arc::from([]);
        let identity = crate::kernel::MutexIdentity {
            epoch: Some(1),
            mutex: Pointer::symbolic(Variable(70)),
        };
        let member = CResource::GuardedPopulation {
            name: "member".into(),
            arguments: arguments.clone(),
            mutex: identity.clone(),
        };
        let context =
            ResourceContext::new().unchecked_with_fact(CResourceFact::own(member.clone()));
        let assumptions = PureFactContext::new();
        assert!(context.satisfies_fact(&CResourceFact::own(member), &assumptions));
        assert!(!context.satisfies_fact(
            &CResourceFact::own(CResource::Composite {
                name: "member".into(),
                arguments: arguments.clone()
            }),
            &assumptions
        ));
        assert!(!context.satisfies_fact(
            &CResourceFact::own(CResource::GuardedPopulation {
                name: "member".into(),
                arguments,
                mutex: crate::kernel::MutexIdentity {
                    epoch: Some(2),
                    ..identity
                }
            }),
            &assumptions
        ));
    }

    #[test]
    fn custody_transitions_do_not_scan_unrelated_resources() {
        for size in [8usize, 32, 128, 512] {
            let (context, instance, definitions, _) = fixture(size, 3);
            let assumptions = PureFactContext::new();
            let mutex = Pointer::symbolic(Variable(70));
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                let published = context
                    .publish_declared(&mutex, instance.identity(), &definitions, &assumptions, 40)
                    .unwrap();
                let (held, guard) = published.acquire(&mutex, &assumptions).unwrap();
                let released = held
                    .release(
                        guard,
                        CResourceFact::own(CResource::Instance(instance.clone())),
                        &assumptions,
                    )
                    .unwrap();
                released.destroy(&mutex, &assumptions).unwrap()
            });
            assert!(
                work > 0 && work < 2000 * (size.ilog2() as usize + 1),
                "size {size}: {work}"
            );
        }
    }
}
