//! Finite anonymous resource witnesses retained by their producing operations.
//!
//! Height counts the selected family's direct owned children: zero for a
//! body without a positive child, otherwise one plus their maximum height.
//! Other families do not participate in this order. An unfold produces strict
//! children; a fold constructs its bound from every selected owned child.
//! Owned constructions name fresh occurrences. An observation can also supply
//! a child proof for an existing duplicable view. The entry authority freezes
//! the original witness independently of these later proof operations.
use super::*;
use crate::kernel::primitives::ResourceContextStorage;
use crate::kernel::primitives::ResourceOccurrenceId;
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Clone, Debug)]
pub(crate) struct ResourceDescent {
    pub requirement: usize,
    authority: Arc<()>,
    root: ResourceOccurrenceId,
    family: String,
    declaration: ResourceSpec,
    entry_resource: Resource,
}

impl PartialEq for ResourceDescent {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.authority, &other.authority)
    }
}
impl Eq for ResourceDescent {}

#[derive(Clone)]
pub(crate) struct ResourceWitnesses {
    descent: ResourceDescent,
    // A distance d certifies height(witness) <= height(entry witness) - d.
    // These are native construction bounds, not additional pure facts.
    bounds: PersistentMap<ResourceOccurrenceId, WitnessBound>,
    owned_epoch: u64,
    has_owned_bounds: bool,
    minimum_height: i64,
    protected: PersistentSet<Resource>,
}

impl std::fmt::Debug for ResourceWitnesses {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResourceWitnesses")
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WitnessBound {
    distance: i64,
    owned_epoch: Option<u64>,
}
impl ResourceWitnesses {
    fn bound(&self, occurrence: ResourceOccurrenceId) -> Option<WitnessBound> {
        self.bounds.get(&occurrence).copied().filter(|bound| {
            bound
                .owned_epoch
                .is_none_or(|epoch| epoch == self.owned_epoch)
        })
    }
}

#[derive(Clone)]
pub(crate) struct ResourceWitnessOpening {
    witnesses: Arc<ResourceWitnesses>,
    distance: i64,
    owned_epoch: Option<u64>,
    before: Arc<ResourceContextStorage>,
}

pub(crate) struct ResourceWitnessFold {
    witnesses: Arc<ResourceWitnesses>,
    distance: i64,
    owned_epoch: Option<u64>,
    before: Arc<ResourceContextStorage>,
}

impl ResourceDescent {
    pub(super) fn open(
        function: &ProgramFunction,
        state: &ExecutionState,
        requirement: usize,
        assumptions: &PureFactContext,
        budget: &mut ExecutionBudget,
    ) -> Result<Self, String> {
        let spec = function
            .resource_requires()
            .get(requirement)
            .ok_or("the structural recursion measure names no entry resource")?;
        let fact = crate::kernel::functions::evaluate_function_resource_spec(
            state,
            spec,
            assumptions,
            budget,
        )
        .map_err(|error| format!("could not read the structural entry measure: {error:?}"))?
        .map_err(|error| format!("could not read the structural entry measure: {error:?}"))?;
        if !fact.is_view() && !fact.has_proven_positive_quantity(assumptions) {
            return Err(
                "the structural entry measure needs a positive owned quantity or a view".into(),
            );
        }
        let Resource::Composite { name, .. } = fact.resource() else {
            return Err("the structural recursion measure must name a composite resource".into());
        };
        let root = state
            .resources()
            .structural_witness_occurrence(&fact, assumptions)
            .ok_or("the structural recursion measure has no selected entry witness")?;
        Ok(Self {
            requirement,
            authority: Arc::new(()),
            root,
            family: name.clone(),
            declaration: spec.clone(),
            entry_resource: fact.resource().clone(),
        })
    }

    pub(crate) fn matches_declaration(&self, interface: &FunctionContractInterface) -> bool {
        interface.resource_requires().get(self.requirement) == Some(&self.declaration)
    }

    pub(crate) fn at_entry(&self, state: &ExecutionState) -> ExecutionState {
        let mut resources = state.resources().clone();
        resources.structural_witnesses = Some(Arc::new(ResourceWitnesses {
            descent: self.clone(),
            bounds: PersistentMap::default().with_inserted(
                self.root,
                WitnessBound {
                    distance: 0,
                    owned_epoch: (!self.declaration.is_view()).then_some(0),
                },
            ),
            owned_epoch: 0,
            has_owned_bounds: !self.declaration.is_view(),
            minimum_height: 0,
            protected: PersistentSet::default().with_value(self.entry_resource.clone()),
        }));
        state.clone().with_resource_context(resources)
    }

    pub(crate) fn check(
        &self,
        state: &ExecutionState,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<(), &'static str> {
        if !fact.is_view() && !fact.has_proven_positive_quantity(assumptions) {
            return Err("the supplied owned quantity is not positive");
        }
        let witnesses = state
            .resources()
            .structural_witnesses
            .as_deref()
            .ok_or("the operation did not retain this contract's witness context")?;
        if witnesses.descent != *self {
            return Err("the supplied witness belongs to another contract entry");
        }
        let occurrence = state
            .resources()
            .structural_witness_occurrence(fact, assumptions)
            .ok_or("the supplied resource has no selected witness occurrence")?;
        charge_termination_work(1);
        let distance = witnesses
            .bound(occurrence)
            .ok_or("the supplied occurrence has no retained bound relative to the entry witness")?;
        if distance.distance > 0 {
            Ok(())
        } else {
            Err("the supplied witness is not smaller than the entry witness")
        }
    }

    #[cfg(test)]
    fn accepts(
        &self,
        state: &ExecutionState,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        self.check(state, fact, assumptions).is_ok()
    }
}

impl ResourceWitnesses {
    pub(crate) fn contains(&self, occurrence: ResourceOccurrenceId) -> bool {
        self.bounds.contains_key(&occurrence)
    }
}

impl ResourceContext {
    pub(crate) fn protects_structural_resource(&self, resource: &Resource) -> bool {
        self.structural_witnesses
            .as_ref()
            .is_some_and(|witnesses| witnesses.protected.contains(resource))
    }

    /// A case join retains only bounds every arm supplies for the same
    /// occurrence. Persistent-map differences visit changed paths only.
    pub(crate) fn meet_structural_witnesses(&mut self, other: &ResourceContext) {
        let (Some(left), Some(right)) = (
            self.structural_witnesses.as_ref(),
            other.structural_witnesses.as_ref(),
        ) else {
            self.structural_witnesses = None;
            return;
        };
        if Arc::ptr_eq(left, right) {
            return;
        }
        if left.descent != right.descent {
            self.structural_witnesses = None;
            return;
        }
        let mut next = (**left).clone();
        next.minimum_height = next.minimum_height.min(right.minimum_height);
        next.owned_epoch = next.owned_epoch.max(right.owned_epoch);
        next.has_owned_bounds = left.has_owned_bounds || right.has_owned_bounds;
        for (occurrence, left_entry, right_entry) in left.bounds.diff(&right.bounds) {
            charge_termination_work(1);
            match (left_entry, right_entry) {
                (Some(left_bound), Some(right_bound))
                    if left.bound(*occurrence).is_some() && right.bound(*occurrence).is_some() =>
                {
                    next.bounds.insert(
                        *occurrence,
                        WitnessBound {
                            distance: left_bound.distance.min(right_bound.distance),
                            owned_epoch: (left_bound.owned_epoch.is_some()
                                || right_bound.owned_epoch.is_some())
                            .then_some(next.owned_epoch),
                        },
                    );
                }
                _ => {
                    next.bounds.remove(occurrence);
                }
            }
        }
        // Only retained bound occurrences need protection. Keeping the left
        // index's extra keys is conservative and requires no ambient scan.
        self.structural_witnesses = Some(Arc::new(next));
    }

    pub(crate) fn same_structural_witness_context(&self, other: &Self) -> bool {
        match (&self.structural_witnesses, &other.structural_witnesses) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }

    /// An abstract loop head forgets owned witnesses it may have changed in
    /// previous iterations, without walking the caller's resource frame.
    pub(crate) fn havoc_owned_structural_witnesses(&mut self) {
        if let Some(witnesses) = self.structural_witnesses.as_mut() {
            if !witnesses.has_owned_bounds {
                return;
            }
            let witnesses = Arc::make_mut(witnesses);
            witnesses.has_owned_bounds = false;
            witnesses.owned_epoch = witnesses
                .owned_epoch
                .checked_add(1)
                .expect("witness epoch exhausted");
        }
    }

    /// An owned call input may be returned with a different hidden witness.
    /// Retire only the selected occurrence's bound, leaving its frame intact.
    pub(crate) fn forget_structural_witness(&mut self, occurrence: ResourceOccurrenceId) {
        if let Some(witnesses) = self.structural_witnesses.as_mut()
            && witnesses.bounds.contains_key(&occurrence)
        {
            Arc::make_mut(witnesses).bounds.remove(&occurrence);
        }
    }

    pub(crate) fn retire_owned_structural_input(
        &mut self,
        caller: &ResourceContext,
        input: &ResourceFact,
        assumptions: &PureFactContext,
    ) {
        if !input.is_own() {
            return;
        }
        let Some(witnesses) = self.structural_witnesses.as_ref() else {
            return;
        };
        let Resource::Composite { name, .. } = input.resource() else {
            return;
        };
        if name != &witnesses.descent.family {
            return;
        }
        if let Some(occurrence) = caller.structural_witness_occurrence(input, assumptions) {
            self.forget_structural_witness(occurrence);
        } else {
            // A legacy transfer without a nominated occurrence cannot promise
            // which hidden witness it returns. Never keep an ambiguous bound.
            Arc::make_mut(self.structural_witnesses.as_mut().unwrap()).bounds =
                PersistentMap::default();
        }
    }

    /// Called by the same definition-opening operation that produces the body.
    pub(crate) fn open_structural_witness(
        &self,
        parent: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceWitnessOpening> {
        if !parent.is_view() && !parent.has_proven_positive_quantity(assumptions) {
            return None;
        }
        let witnesses = self.structural_witnesses.as_ref()?;
        let Resource::Composite { name, .. } = parent.resource() else {
            return None;
        };
        if name != &witnesses.descent.family {
            return None;
        }
        let occurrence = self.structural_witness_occurrence(parent, assumptions)?;
        let bound = witnesses.bound(occurrence)?;
        let distance = bound.distance.checked_add(1)?;
        Some(ResourceWitnessOpening {
            witnesses: witnesses.clone(),
            distance,
            owned_epoch: bound.owned_epoch,
            before: self.storage.clone(),
        })
    }

    /// Publish only fresh occurrences of the owned children the opening produced.
    /// Observing a body projects those owned children to views of the same witness.
    pub(crate) fn with_opened_structural_witnesses(
        mut self,
        opening: Option<ResourceWitnessOpening>,
        owned_children: &[ResourceFact],
        viewed: bool,
        assumptions: &PureFactContext,
    ) -> Self {
        let Some(mut opening) = opening else {
            return self;
        };
        for child in owned_children {
            charge_termination_work(1);
            if !child.is_own() {
                continue;
            }
            let Resource::Composite { name, .. } = child.resource() else {
                continue;
            };
            if name != &opening.witnesses.descent.family {
                continue;
            }
            if !child.has_proven_positive_quantity(assumptions) {
                continue;
            }
            let projected = if viewed {
                ResourceFact::View(child.resource().clone())
            } else {
                child.clone()
            };
            let Some(occurrence) = self.structural_witness_occurrence(&projected, assumptions)
            else {
                continue;
            };
            let actual = self
                .structural_fact_at_occurrence(occurrence)
                .expect("selected live witness");
            // A view description may already exist. This opening supplies its
            // selected child proof without manufacturing owned authority.
            if opening.before.entry_by_occurrence.contains_key(&occurrence)
                && (!actual.is_view() || occurrence == opening.witnesses.descent.root)
            {
                continue;
            }
            let witnesses = Arc::make_mut(&mut opening.witnesses);
            witnesses.minimum_height = witnesses.minimum_height.max(opening.distance);
            witnesses.has_owned_bounds |= actual.is_own() || opening.owned_epoch.is_some();
            witnesses.bounds = witnesses.bounds.with_inserted(
                occurrence,
                WitnessBound {
                    distance: opening.distance,
                    owned_epoch: if actual.is_own() {
                        Some(witnesses.owned_epoch)
                    } else {
                        opening.owned_epoch
                    },
                },
            );
            witnesses.protected = witnesses.protected.with_value(actual.resource().clone());
        }
        self.structural_witnesses = Some(opening.witnesses);
        self
    }

    /// A fold constructs one parent above every same-family owned child.
    /// New or unrelated children cannot inherit an old witness's bound.
    pub(crate) fn prepare_structural_witness_fold(
        &self,
        children: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Option<ResourceWitnessFold> {
        let witnesses = self.structural_witnesses.as_ref()?;
        let mut distance: Option<i64> = None;
        let mut owned_epoch = None;
        for child in children {
            charge_termination_work(1);
            if !child.is_own() {
                continue;
            }
            let Resource::Composite { name, .. } = child.resource() else {
                continue;
            };
            if name != &witnesses.descent.family {
                continue;
            }
            if child.owned_quantity() == Some(0) {
                continue;
            }
            if !child.has_proven_positive_quantity(assumptions) {
                return None;
            }
            let occurrence = self
                .structural_witness_occurrence(child, assumptions)
                .or_else(|| {
                    self.structural_witness_occurrence(
                        &ResourceFact::View(child.resource().clone()),
                        assumptions,
                    )
                })?;
            let bound = witnesses.bound(occurrence)?;
            if bound.owned_epoch.is_some() {
                owned_epoch = Some(witnesses.owned_epoch);
            }
            distance =
                Some(distance.map_or(bound.distance, |previous| previous.min(bound.distance)));
        }
        Some(ResourceWitnessFold {
            witnesses: witnesses.clone(),
            distance: match distance {
                Some(distance) => distance.checked_sub(1)?,
                None => witnesses.minimum_height,
            },
            owned_epoch,
            before: self.storage.clone(),
        })
    }

    pub(crate) fn with_folded_structural_witness(
        mut self,
        fold: Option<ResourceWitnessFold>,
        parent: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Self {
        let Some(mut fold) = fold else {
            return self;
        };
        let Resource::Composite { name, .. } = parent.resource() else {
            return self;
        };
        if name != &fold.witnesses.descent.family {
            return self;
        }
        if let Some(occurrence) = self.structural_witness_occurrence(parent, assumptions) {
            if fold.before.entry_by_occurrence.contains_key(&occurrence)
                && fold.witnesses.bound(occurrence).is_some()
            {
                return self;
            }
            let actual = self
                .structural_fact_at_occurrence(occurrence)
                .expect("selected live fold");
            let witnesses = Arc::make_mut(&mut fold.witnesses);
            witnesses.has_owned_bounds |= actual.is_own() || fold.owned_epoch.is_some();
            witnesses.bounds = witnesses.bounds.with_inserted(
                occurrence,
                WitnessBound {
                    distance: fold.distance,
                    owned_epoch: if actual.is_own() {
                        Some(witnesses.owned_epoch)
                    } else {
                        fold.owned_epoch
                    },
                },
            );
            witnesses.protected = witnesses.protected.with_value(actual.resource().clone());
            self.structural_witnesses = Some(fold.witnesses);
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fact(family: &str, value: u32) -> ResourceFact {
        ResourceFact::own(Resource::Composite {
            name: family.into(),
            arguments: vec![AlgebraicValue::Program(crate::kernel::int32(
                MachineTerm::constant(value),
            ))]
            .into(),
        })
    }

    fn entry() -> (ResourceDescent, ExecutionState, ResourceFact) {
        let parent = fact("list", 0);
        let state = ExecutionState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(parent.clone()));
        let root = state
            .resources()
            .structural_witness_occurrence(&parent, &PureFactContext::new())
            .unwrap();
        let descent = ResourceDescent {
            requirement: 0,
            authority: Arc::new(()),
            root,
            family: "list".into(),
            entry_resource: parent.resource().clone(),
            declaration: ResourceSpec::composite(
                ResourceAccessMode::Own,
                "list".into(),
                vec![ProgramExpression::Value(crate::kernel::int32(
                    MachineTerm::constant(0),
                ))],
                vec![ProgramType::Int32],
            ),
        };
        let state = descent.at_entry(&state);
        (descent, state, parent)
    }

    fn unfold(
        state: &ExecutionState,
        parent: &ResourceFact,
        child: &ResourceFact,
    ) -> ExecutionState {
        let assumptions = PureFactContext::new();
        let opening = state
            .resources()
            .open_structural_witness(parent, &assumptions);
        let resources = state
            .resources()
            .clone()
            .without_fact_incrementally(parent, &assumptions)
            .unwrap()
            .unchecked_with_fact(child.clone())
            .with_opened_structural_witnesses(
                opening,
                std::slice::from_ref(child),
                false,
                &assumptions,
            );
        state.clone().with_resource_context(resources)
    }

    #[test]
    fn only_the_produced_child_occurrence_has_descent() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        assert!(descent.accepts(&next, &child, &PureFactContext::new()));
        assert!(!descent.accepts(&state, &parent, &PureFactContext::new()));
        let replaced = next
            .resources()
            .clone()
            .without_fact_incrementally(&child, &PureFactContext::new())
            .unwrap()
            .unchecked_with_fact(child.clone());
        assert!(!descent.accepts(
            &next.with_resource_context(replaced),
            &child,
            &PureFactContext::new()
        ));
    }

    #[test]
    fn ambiguous_owned_occurrences_cannot_supply_a_selected_witness() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let resources = next.resources().clone().unchecked_with_fact(child.clone());
        assert!(!descent.accepts(
            &next.with_resource_context(resources),
            &child,
            &PureFactContext::new()
        ));
    }

    #[test]
    fn folding_a_layer_back_does_not_turn_the_parent_into_a_child() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let assumptions = PureFactContext::new();
        let fold = next
            .resources()
            .prepare_structural_witness_fold(std::slice::from_ref(&child), &assumptions);
        let resources = next
            .resources()
            .clone()
            .without_fact_incrementally(&child, &assumptions)
            .unwrap()
            .unchecked_with_fact(parent.clone())
            .with_folded_structural_witness(fold, &parent, &assumptions);
        assert!(!descent.accepts(
            &next.with_resource_context(resources),
            &parent,
            &assumptions
        ));
    }

    #[test]
    fn a_leaf_fold_uses_only_its_branchs_retained_height_bound() {
        let (descent, state, parent) = entry();
        let leaf = fact("list", 1);
        let assumptions = PureFactContext::new();
        let opened = unfold(&state, &parent, &leaf);
        for (branch, expected) in [(state, false), (opened, true)] {
            let fold = branch
                .resources()
                .prepare_structural_witness_fold(&[], &assumptions);
            let folded = fact("list", 2);
            let resources = branch
                .resources()
                .clone()
                .unchecked_with_fact(folded.clone())
                .with_folded_structural_witness(fold, &folded, &assumptions);
            assert_eq!(
                descent.accepts(
                    &branch.with_resource_context(resources),
                    &folded,
                    &assumptions
                ),
                expected
            );
        }
    }

    #[test]
    fn returned_ownership_and_unknown_fold_children_do_not_reuse_a_bound() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let assumptions = PureFactContext::new();
        let mut resources = next.resources().clone();
        let occurrence = resources
            .structural_witness_occurrence(&child, &assumptions)
            .unwrap();
        resources.forget_structural_witness(occurrence);
        assert!(!descent.accepts(
            &next.clone().with_resource_context(resources),
            &child,
            &assumptions
        ));
        let unknown = fact("list", 2);
        let resources = next
            .resources()
            .clone()
            .unchecked_with_fact(unknown.clone());
        assert!(
            resources
                .prepare_structural_witness_fold(&[child, unknown], &assumptions)
                .is_none()
        );
    }

    #[test]
    fn zero_quantity_does_not_establish_a_strict_child_or_a_height_bound() {
        let (descent, state, parent) = entry();
        let assumptions = PureFactContext::new();
        let child = ResourceFact::Own(
            fact("list", 1).resource().clone(),
            Box::new(MachineTerm::constant(0).into()),
        );
        let opening = state
            .resources()
            .open_structural_witness(&parent, &assumptions);
        let resources = state
            .resources()
            .clone()
            .unchecked_with_fact(child.clone())
            .with_opened_structural_witnesses(
                opening,
                std::slice::from_ref(&child),
                false,
                &assumptions,
            );
        assert!(!descent.accepts(
            &state.clone().with_resource_context(resources.clone()),
            &child,
            &assumptions
        ));
        let leaf = fact("list", 2);
        let fold = resources.prepare_structural_witness_fold(&[], &assumptions);
        let resources = resources
            .unchecked_with_fact(leaf.clone())
            .with_folded_structural_witness(fold, &leaf, &assumptions);
        assert!(!descent.accepts(&state.with_resource_context(resources), &leaf, &assumptions));
    }

    #[test]
    fn a_viewed_child_is_still_a_constructor_child_when_folding() {
        let (descent, state, parent) = entry();
        let assumptions = PureFactContext::new();
        let child = fact("list", 1);
        let viewed_child = ResourceFact::View(child.resource().clone());
        let opening = state
            .resources()
            .open_structural_witness(&parent, &assumptions);
        let resources = state
            .resources()
            .clone()
            .unchecked_with_fact(viewed_child)
            .with_opened_structural_witnesses(
                opening,
                std::slice::from_ref(&child),
                true,
                &assumptions,
            );
        let fold = resources.prepare_structural_witness_fold(&[child], &assumptions);
        assert!(fold.is_some());
        let viewed_parent = ResourceFact::View(parent.resource().clone());
        let resources = resources
            .unchecked_with_fact(viewed_parent.clone())
            .with_folded_structural_witness(fold, &viewed_parent, &assumptions);
        assert!(!descent.accepts(
            &state.with_resource_context(resources),
            &viewed_parent,
            &assumptions
        ));
    }

    #[test]
    fn a_fold_never_reassigns_the_witness_of_an_existing_occurrence() {
        let (descent, state, parent) = entry();
        let assumptions = PureFactContext::new();
        let child = fact("list", 1);
        let opening = state
            .resources()
            .open_structural_witness(&parent, &assumptions);
        let resources = state
            .resources()
            .clone()
            .unchecked_with_fact(child.clone())
            .with_opened_structural_witnesses(opening, &[child], false, &assumptions);
        let fold = resources.prepare_structural_witness_fold(&[], &assumptions);
        let resources = resources.with_folded_structural_witness(fold, &parent, &assumptions);
        assert!(!descent.accepts(
            &state.with_resource_context(resources),
            &parent,
            &assumptions
        ));
    }

    #[test]
    fn case_join_drops_branch_local_bounds_and_height_information() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let assumptions = PureFactContext::new();
        let opened = unfold(&state, &parent, &child);
        let mut joined = opened.resources().clone();
        joined.meet_structural_witnesses(state.resources());
        assert!(!descent.accepts(
            &opened.clone().with_resource_context(joined.clone()),
            &child,
            &assumptions
        ));
        let leaf = fact("list", 2);
        let fold = joined.prepare_structural_witness_fold(&[], &assumptions);
        let joined = joined
            .unchecked_with_fact(leaf.clone())
            .with_folded_structural_witness(fold, &leaf, &assumptions);
        assert!(!descent.accepts(
            &opened.clone().with_resource_context(joined),
            &leaf,
            &assumptions
        ));
        let mut common = opened.resources().clone();
        common.meet_structural_witnesses(opened.resources());
        assert!(descent.accepts(&opened.with_resource_context(common), &child, &assumptions));
    }

    #[test]
    fn reopening_the_same_occurrence_does_not_reuse_an_entry_authority() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let mut reopened = descent.clone();
        reopened.authority = Arc::new(());
        assert!(!reopened.accepts(&next, &child, &PureFactContext::new()));
    }

    #[test]
    fn abstract_loop_heads_forget_owned_but_preserve_readonly_witnesses() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let mut resources = next.resources().clone();
        resources.havoc_owned_structural_witnesses();
        assert!(!descent.accepts(
            &next.with_resource_context(resources),
            &child,
            &PureFactContext::new()
        ));

        let viewed_parent = ResourceFact::View(parent.resource().clone());
        let resources = ResourceContext::new().unchecked_with_fact(viewed_parent.clone());
        let mut readonly = descent;
        readonly.authority = Arc::new(());
        readonly.root = resources
            .structural_witness_occurrence(&viewed_parent, &PureFactContext::new())
            .unwrap();
        readonly.declaration =
            ResourceSpec::composite(ResourceAccessMode::View, "list".into(), vec![], vec![]);
        let state = readonly.at_entry(&ExecutionState::new().with_resource_context(resources));
        let assumptions = PureFactContext::new();
        let opening = state
            .resources()
            .open_structural_witness(&viewed_parent, &assumptions);
        let viewed_child = ResourceFact::View(child.resource().clone());
        let mut resources = state
            .resources()
            .clone()
            .unchecked_with_fact(viewed_child.clone())
            .with_opened_structural_witnesses(opening, &[child], true, &assumptions);
        resources.havoc_owned_structural_witnesses();
        assert!(readonly.accepts(
            &state.with_resource_context(resources),
            &viewed_child,
            &assumptions
        ));
    }

    #[test]
    fn normalization_keeps_the_selected_child_occurrence() {
        let (descent, state, parent) = entry();
        let child = fact("list", 1);
        let next = unfold(&state, &parent, &child);
        let assumptions = PureFactContext::new();
        let resources = next.resources().clone().normalized(&assumptions);
        assert!(descent.accepts(&next.with_resource_context(resources), &child, &assumptions));
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/resource_descent.rs");
    }
}
