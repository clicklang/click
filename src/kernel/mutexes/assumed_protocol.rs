//! Opaque mutex protocols supplied by an independent contract input.
//!
//! A rooted use input authenticates its protected resource type. Acquisitions
//! produce fresh folded state; releases consume an owned instance of that type
//! while retaining the caller's lifetime obligation.

use super::*;
use crate::kernel::loans::{
    CheckedLoanCallEvidence, CheckedLoanCallEvidenceSequence, CheckedLoanTransition, LoanRefusal,
    append_checked_loan_evidence, empty_checked_loan_evidence_sequence,
};

/// A description backed by one actual, rooted use input, not by its address.
/// It supplies neither lifecycle ownership nor protected memory ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AssumedMutexProtocol {
    pub(super) usage: MutexUseBinding,
    pub(super) holder: LoanParticipantId,
    pub(super) use_fact: CResourceFact,
    pub(super) lifetime: CResourceFact,
}

/// An exact acquisition receipt. The guard atom and its loan hold must also
/// remain in the state; copying this receipt never copies ownership.
#[derive(Clone, Debug)]
pub(super) struct AssumedMutexGuard {
    pub(super) protocol: AssumedMutexProtocol,
    pub(super) fact: CResourceFact,
    pub(super) hold: LoanHoldId,
    pub(super) payload: Option<crate::kernel::ResourceInstance>,
}

pub(super) struct AssumedMutexTransition {
    pub(super) state: CState,
    pub(super) evidence: CheckedLoanCallEvidenceSequence,
}

impl AssumedMutexProtocol {
    pub(super) fn bind(
        state: &CState,
        usage: MutexUseBinding,
    ) -> Result<Self, MutexTransitionError> {
        if !state.preserves_mutex_protocols {
            return Err("abstract mutex protocols require independent contract input state".into());
        }
        let holder = state
            .loan_participant
            .ok_or("missing mutex use participant")?;
        let loans = state.loan_ledger.as_ref().ok_or("missing mutex use loan")?;
        let use_fact = loans
            .mutex_use_resource(usage, holder)
            .map_err(|_| MutexTransitionError::Refusal("missing rooted mutex use input"))?;
        let CResource::MutexUse(identity) = use_fact.resource() else {
            unreachable!()
        };
        if state
            .resources
            .unique_owned_occurrence_for_fact(&use_fact)
            .is_none()
        {
            return Err(MutexTransitionError::MissingUse(identity.mutex.clone()));
        }
        let initialization = identity
            .initialization
            .ok_or_else(|| MutexTransitionError::MissingUse(identity.mutex.clone()))?;
        let lifetime = CResourceFact::own(CResource::MutexLive(super::super::MutexIdentity {
            epoch: Some(initialization),
            mutex: identity.mutex.clone(),
        }));
        Ok(Self {
            usage,
            holder,
            use_fact,
            lifetime,
        })
    }

    pub(super) fn mutex(&self) -> &Pointer {
        let CResource::MutexUse(identity) = self.use_fact.resource() else {
            unreachable!()
        };
        &identity.mutex
    }

    pub(super) fn loans<'a>(
        &self,
        state: &'a CState,
    ) -> Result<&'a LoanLedger, MutexTransitionError> {
        let missing = || MutexTransitionError::MissingUse(self.mutex().clone());
        if !state.preserves_mutex_protocols
            || state.loan_participant != Some(self.holder)
            || state
                .resources
                .unique_owned_occurrence_for_fact(&self.use_fact)
                .is_none()
        {
            return Err(missing());
        }
        let ledger = state.loan_ledger.as_ref().ok_or_else(missing)?;
        if ledger
            .mutex_use_resource(self.usage, self.holder)
            .map_err(|_| missing())?
            != self.use_fact
        {
            return Err(missing());
        }
        Ok(ledger)
    }

    pub(super) fn acquire(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
    ) -> Result<(AssumedMutexTransition, AssumedMutexGuard), MutexTransitionError> {
        self.acquire_with_payload(
            state,
            assumptions,
            None,
            None,
            &mut crate::kernel::ExecutionBudget::beside_live_state(),
        )
    }

    pub(super) fn acquire_with_payload(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
        definition: Option<&crate::kernel::CCompositeResourceDefinition>,
        output: Option<crate::kernel::Variable>,
        budget: &mut crate::kernel::ExecutionBudget,
    ) -> Result<(AssumedMutexTransition, AssumedMutexGuard), MutexTransitionError> {
        let loans = self.loans(state)?;
        // A hidden or removed guard still pins the scope. Do not decide local
        // heldness by merely searching the visible resource context.
        loans
            .check_mutex_use_available(self.usage, self.holder, &state.resources)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "mutex_use has an outstanding mutex_guard or reborrow",
                )
            })?;
        if state.resources.mutex_guard_at(self.mutex()).is_some() {
            return Err("mutex is already guarded".into());
        }
        let (next, hold, transition) = loans
            .hold_mutex_use_with_transition(self.usage, &self.lifetime, self.holder)
            .map_err(|_| MutexTransitionError::MissingUse(self.mutex().clone()))?;
        let fact = CResourceFact::own(CResource::MutexGuard(super::super::MutexIdentity {
            epoch: Some(fresh_acquisition_epoch()?),
            mutex: self.mutex().clone(),
        }));
        let (memory, payload) =
            self.acquire_payload(state, assumptions, definition, output, budget)?;
        let resources = state
            .resources
            .clone()
            .try_compose_with_facts_delaying_normalization([fact.clone()], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal("mutex guard conflicts with current authority")
            })?;
        let evidence = self.evidence(loans, transition, &next)?;
        let mut state = state.clone();
        state.resources = if let Some(payload) = &payload {
            resources
                .try_compose_with_facts_delaying_normalization(
                    [CResourceFact::own(CResource::Instance(payload.clone()))],
                    assumptions,
                )
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "protected resource conflicts with current ownership",
                    )
                })?
        } else {
            resources
        };
        state.memory = memory;
        state.loan_ledger = Some(next);
        Ok((
            AssumedMutexTransition { state, evidence },
            AssumedMutexGuard {
                protocol: self.clone(),
                fact,
                hold,
                payload,
            },
        ))
    }

    fn acquire_payload(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
        definition: Option<&crate::kernel::CCompositeResourceDefinition>,
        output: Option<crate::kernel::Variable>,
        budget: &mut crate::kernel::ExecutionBudget,
    ) -> Result<
        (
            crate::kernel::CMemory,
            Option<crate::kernel::ResourceInstance>,
        ),
        MutexTransitionError,
    > {
        let CResource::MutexUse(usage) = self.use_fact.resource() else {
            unreachable!()
        };
        let Some(description) = &usage.protected else {
            if output.is_some() {
                return Err("mutex_use has no protected resource type".into());
            }
            return Ok((state.memory.clone(), None));
        };
        fresh_protected_payload(
            state,
            assumptions,
            self.mutex(),
            description,
            definition,
            output,
            budget,
        )
    }

    pub(super) fn release(
        &self,
        state: &CState,
        guard: &AssumedMutexGuard,
        assumptions: &PureFactContext,
    ) -> Result<AssumedMutexTransition, MutexTransitionError> {
        self.release_with_payload(state, guard, assumptions, None)
    }

    pub(super) fn release_with_payload(
        &self,
        state: &CState,
        guard: &AssumedMutexGuard,
        assumptions: &PureFactContext,
        selected: Option<crate::kernel::Variable>,
    ) -> Result<AssumedMutexTransition, MutexTransitionError> {
        if guard.protocol != *self {
            return Err(MutexTransitionError::MissingGuard(self.mutex().clone()));
        }
        let loans = self.loans(state)?;
        if state
            .resources
            .unique_owned_occurrence_for_fact(&guard.fact)
            .is_none()
        {
            return Err(MutexTransitionError::MissingGuard(self.mutex().clone()));
        }
        let restored = if let Some(acquired) = &guard.payload {
            let CResource::MutexUse(usage) = self.use_fact.resource() else {
                unreachable!()
            };
            let required = CResourceFact::own(CResource::Instance(acquired.clone()));
            let current = match selected {
                Some(identity) => state.owned_resource_instance(identity),
                None => state.resources.owned_instance(acquired.identity()),
            }
            .ok_or_else(|| MutexTransitionError::MissingInvariant(required.clone()))?;
            if !usage
                .protected
                .as_ref()
                .is_some_and(|description| description.matches_instance(current, assumptions))
            {
                return Err(MutexTransitionError::MissingInvariant(required));
            }
            if loans.has_active_memory_loans() || state.loan_view_bindings.iter().next().is_some() {
                return Err("protected mutex release requires returned memory loans".into());
            }
            Some(CResourceFact::own(CResource::Instance(current.clone())))
        } else {
            if selected.is_some() {
                return Err("mutex_use has no protected resource type".into());
            }
            None
        };
        let (next, transition) = loans
            .release_mutex_use_hold_with_transition(
                self.usage,
                &self.lifetime,
                guard.hold,
                self.holder,
            )
            .map_err(|_| MutexTransitionError::MissingGuard(self.mutex().clone()))?;
        let resources = state
            .resources
            .clone()
            .without_fact_delaying_normalization(&guard.fact, assumptions)
            .ok_or_else(|| MutexTransitionError::MissingGuard(self.mutex().clone()))?;
        let resources = if let Some(restored) = restored {
            resources
                .without_fact_delaying_normalization(&restored, assumptions)
                .ok_or_else(|| MutexTransitionError::MissingInvariant(restored))?
        } else {
            resources
        };
        let evidence = self.evidence(loans, transition, &next)?;
        let mut state = state.clone();
        state.resources = resources;
        state.loan_ledger = Some(next);
        Ok(AssumedMutexTransition { state, evidence })
    }

    #[cfg(test)]
    pub(super) fn check_return(&self, state: &CState) -> Result<(), MutexTransitionError> {
        self.loans(state)?
            .check_assumed_mutex_use_return(self.usage, self.holder, &state.resources)
            .map_err(|_| MutexTransitionError::MissingUse(self.mutex().clone()))
    }

    fn evidence(
        &self,
        before: &LoanLedger,
        transition: CheckedLoanTransition,
        after: &LoanLedger,
    ) -> Result<CheckedLoanCallEvidenceSequence, MutexTransitionError> {
        let evidence = CheckedLoanCallEvidence::runtime_mutex_transition(
            before,
            self.holder,
            transition,
            after,
        )
        .map_err(|_: LoanRefusal| {
            MutexTransitionError::Refusal("invalid mutex lifetime transition")
        })?;
        Ok(append_checked_loan_evidence(
            &empty_checked_loan_evidence_sequence(),
            Some(Arc::new(evidence)),
        ))
    }
}

/// Branch-local receipts, separate from immutable descriptions of entry guards.
/// Removing a visible guard does not remove its receipt or lifetime hold.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct OpaqueMutexAcquisitions {
    pub(super) identity: u64,
    pub(super) receipts: PersistentMap<Pointer, Arc<AssumedMutexGuard>>,
    pub(super) storage: MutexLedger,
    pub(super) holders: PersistentMap<LoanParticipantId, usize>,
}

impl OpaqueMutexAcquisitions {
    pub(in crate::kernel) fn has_local_hold(&self, participant: Option<LoanParticipantId>) -> bool {
        participant.is_none_or(|holder| self.holders.contains_key(&holder))
    }
    pub(super) fn guard_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        self.receipts.get(mutex).map(|guard| guard.fact.clone())
    }
    pub(super) fn acquisition_conflicts(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        let bytes = crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
            .mutex_storage_bytes;
        ledger_storage_write_refusal(&self.storage, &storage_range(mutex, bytes), assumptions)
            .is_some()
    }
}

impl PartialEq for OpaqueMutexAcquisitions {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for OpaqueMutexAcquisitions {}
impl PartialOrd for OpaqueMutexAcquisitions {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}
impl Ord for OpaqueMutexAcquisitions {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        self.identity.cmp(&other.identity)
    }
}
impl Hash for OpaqueMutexAcquisitions {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

#[cfg(test)]
pub(in crate::kernel) fn opaque_runtime_transition(
    state: &CState,
    mutex: &Pointer,
    acquire: bool,
    assumptions: &PureFactContext,
) -> Result<(CState, CheckedLoanCallEvidenceSequence), MutexTransitionError> {
    opaque_runtime_transition_with_payload(
        state,
        mutex,
        acquire,
        assumptions,
        None,
        None,
        &mut crate::kernel::ExecutionBudget::beside_live_state(),
    )
}

pub(in crate::kernel) fn opaque_runtime_transition_with_payload(
    state: &CState,
    mutex: &Pointer,
    acquire: bool,
    assumptions: &PureFactContext,
    definition: Option<&crate::kernel::CCompositeResourceDefinition>,
    payload_identity: Option<crate::kernel::Variable>,
    budget: &mut crate::kernel::ExecutionBudget,
) -> Result<(CState, CheckedLoanCallEvidenceSequence), MutexTransitionError> {
    opaque_runtime_transition_with_selected_use(
        state,
        mutex,
        acquire,
        assumptions,
        definition,
        payload_identity,
        budget,
        None,
    )
}

pub(super) fn opaque_runtime_transition_with_selected_use(
    state: &CState,
    mutex: &Pointer,
    acquire: bool,
    assumptions: &PureFactContext,
    definition: Option<&crate::kernel::CCompositeResourceDefinition>,
    payload_identity: Option<crate::kernel::Variable>,
    budget: &mut crate::kernel::ExecutionBudget,
    selected_use: Option<&CResourceFact>,
) -> Result<(CState, CheckedLoanCallEvidenceSequence), MutexTransitionError> {
    if !state.preserves_mutex_protocols {
        return Err("opaque mutex transitions require preserving use authority".into());
    }
    if acquire {
        let fact = selected_use
            .or_else(|| state.resources.mutex_use_candidate_at(mutex))
            .ok_or_else(|| MutexTransitionError::MissingUse(mutex.clone()))?;
        let CResource::MutexUse(identity) = fact.resource() else {
            unreachable!()
        };
        let usage = identity
            .binding
            .ok_or_else(|| MutexTransitionError::MissingUse(mutex.clone()))?;
        let protocol = AssumedMutexProtocol::bind(state, usage)?;
        if protocol.mutex() != mutex || protocol.use_fact != *fact {
            return Err(MutexTransitionError::MissingUse(mutex.clone()));
        }
        if let Some(error) = super::acquisition_availability_refusal(state, mutex, assumptions) {
            return Err(error);
        }
        if let Some(ledger) = &state.mutex_ledger {
            ledger.check_use_acquisition(fact)?;
        }
        let (mut transition, guard) = protocol.acquire_with_payload(
            state,
            assumptions,
            definition,
            payload_identity,
            budget,
        )?;
        let mut holders = state
            .opaque_mutex_acquisitions
            .as_ref()
            .map(|held| held.holders.clone())
            .unwrap_or_default();
        let count = holders.get(&protocol.holder).copied().unwrap_or(0);
        holders.insert(protocol.holder, count + 1);
        let receipts = state
            .opaque_mutex_acquisitions
            .as_ref()
            .map(|held| held.receipts.clone())
            .unwrap_or_default()
            .with_inserted(mutex.clone(), Arc::new(guard));
        let storage = state
            .opaque_mutex_acquisitions
            .as_ref()
            .map(|held| held.storage.clone())
            .unwrap_or_else(MutexLedger::new)
            .with_inserted(
                mutex.clone(),
                MutexEntry::Unlocked {
                    initialization: MutexInitialization(
                        MutexInitializationId(
                            identity.initialization.expect("checked initialization"),
                        ),
                        crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
                            .mutex_storage_bytes,
                    ),
                    invariant: None,
                    interface: None,
                },
            );
        transition.state.opaque_mutex_acquisitions = Some(OpaqueMutexAcquisitions {
            identity: MutexLedger::fresh_identity(),
            receipts,
            storage,
            holders,
        });
        Ok((transition.state, transition.evidence))
    } else {
        let held = state
            .opaque_mutex_acquisitions
            .as_ref()
            .ok_or_else(|| MutexTransitionError::MissingGuard(mutex.clone()))?;
        let guard = held
            .receipts
            .get(mutex)
            .ok_or_else(|| MutexTransitionError::MissingGuard(mutex.clone()))?;
        if selected_use.is_some_and(|selected| selected != &guard.protocol.use_fact) {
            return Err("guard lifetime belongs to a different selected mutex_use".into());
        }
        let mut transition =
            guard
                .protocol
                .release_with_payload(state, guard, assumptions, payload_identity)?;
        let receipts = held.receipts.without_key(mutex);
        let holder = guard.protocol.holder;
        let count = held
            .holders
            .get(&holder)
            .copied()
            .ok_or("missing opaque acquisition holder")?;
        let holders = if count == 1 {
            held.holders.without_key(&holder)
        } else {
            held.holders.with_inserted(holder, count - 1)
        };
        transition.state.opaque_mutex_acquisitions =
            (!receipts.is_empty()).then(|| OpaqueMutexAcquisitions {
                identity: MutexLedger::fresh_identity(),
                receipts,
                storage: held.storage.without(mutex),
                holders,
            });
        Ok((transition.state, transition.evidence))
    }
}

pub(super) fn fresh_protected_payload(
    state: &CState,
    assumptions: &PureFactContext,
    mutex: &Pointer,
    description: &crate::kernel::ResourceDescription,
    definition: Option<&crate::kernel::CCompositeResourceDefinition>,
    output: Option<crate::kernel::Variable>,
    budget: &mut crate::kernel::ExecutionBudget,
) -> Result<
    (
        crate::kernel::CMemory,
        Option<crate::kernel::ResourceInstance>,
    ),
    MutexTransitionError,
> {
    use crate::kernel::{ResourceInstance, functions::ModelFieldMintSite, model_fields::ModelMint};
    let definition =
        definition.ok_or("protected mutex acquisition requires its resource declaration")?;
    if definition.name() != description.family()
        || definition.instance_field_schema() != Some(description.schema())
        || definition.recursive
        || definition.matched.is_some()
        || definition.condition.is_some()
        || !definition.witnesses.is_empty()
        || !definition.children.is_empty()
        || !definition.resource_parameters().is_empty()
        || !description.resource_arguments().is_empty()
    {
        return Err("protected mutex acquisition requires an unconditional leaf resource".into());
    }
    if let Some(declaration) = definition.guarded_by.as_ref() {
        let Some(crate::kernel::AlgebraicValue::C(crate::kernel::CValue::Pointer(base))) =
            description.arguments().get(declaration.parameter_index)
        else {
            return Err("guarded resource parameter is not a pointer".into());
        };
        let expected = base
            .pointer()
            .offset_by_bytes(declaration.field_offset_bytes);
        if !crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &expected,
            mutex,
            assumptions,
        ) {
            return Err("protected resource is guarded by a different mutex".into());
        }
    }
    let identity = match output {
        Some(identity) => identity,
        None => budget
            .allocate_kernel_variable()
            .map_err(|_| "protected resource identity allocation exceeded its budget")?,
    };
    let fields = crate::kernel::functions::arbitrary_resource_instance_fields(
        description.schema(),
        ModelFieldMintSite {
            identity,
            minted_by: &ModelMint::Produced {
                callee: Arc::from("pthread_mutex_lock"),
            },
        },
        budget,
    )
    .map_err(|_| "protected resource model allocation exceeded its budget")?;
    let instance = ResourceInstance::new(
        identity,
        description.family().into(),
        description.arguments().iter().cloned().collect(),
        description.schema().clone(),
        fields,
    )
    .ok_or("protected mutex type requires an exclusive resource")?;
    let fact = CResourceFact::own(CResource::Instance(instance.clone()));
    let ranges = crate::kernel::functions::checked_owned_memory_ranges(
        &fact,
        std::slice::from_ref(definition),
        state,
        assumptions,
    )
    .ok_or("protected mutex resource has no checked memory footprint")?;
    // Resource types do not promise that an observed model controls a stable
    // footprint. This bounded interface accepts only footprints unchanged
    // under an independent arbitrary model instantiation.
    let other_identity = budget
        .allocate_kernel_variable()
        .map_err(|_| "protected footprint checking exceeded its budget")?;
    let other_fields = crate::kernel::functions::arbitrary_resource_instance_fields(
        description.schema(),
        ModelFieldMintSite {
            identity: other_identity,
            minted_by: &ModelMint::Produced {
                callee: Arc::from("pthread_mutex_lock"),
            },
        },
        budget,
    )
    .map_err(|_| "protected footprint checking exceeded its budget")?;
    let other = ResourceInstance::new(
        other_identity,
        description.family().into(),
        description.arguments().iter().cloned().collect(),
        description.schema().clone(),
        other_fields,
    )
    .ok_or("protected mutex type requires an exclusive resource")?;
    let other_ranges = crate::kernel::functions::checked_owned_memory_ranges(
        &CResourceFact::own(CResource::Instance(other)),
        std::slice::from_ref(definition),
        state,
        assumptions,
    )
    .ok_or("protected mutex resource has no checked memory footprint")?;
    if ranges != other_ranges {
        return Err(
            "protected mutex resource requires a model-independent memory footprint".into(),
        );
    }
    if ranges
        .iter()
        .any(crate::kernel::CMemoryRange::is_unnamed_footprint)
    {
        return Err("protected mutex resource requires a bounded memory footprint".into());
    }
    let memory = if ranges.is_empty() {
        state.memory.clone()
    } else {
        state.memory.clone().with_call_memory_havoc(
            budget
                .allocate_kernel_variable()
                .map_err(|_| "protected memory acquisition exceeded its budget")?,
            &ranges,
            assumptions,
            None,
        )
    };
    Ok((memory, Some(instance)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MutexUseIdentity, ResourceContext, Variable};

    fn input() -> (CState, AssumedMutexProtocol) {
        let mutex = Pointer::symbolic(Variable(765));
        let description = CResourceFact::own(CResource::MutexUse(MutexUseIdentity {
            protected: None,
            binding: None,
            initialization: None,
            mutex: mutex.clone(),
        }));
        let resources = ResourceContext::new().unchecked_with_fact(description.clone());
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(&description)
            .unwrap();
        let ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let (ledger, root) = ledger
            .borrowed_mutex_use_input(holder, support, mutex)
            .unwrap();
        let fact = ledger.mutex_use_resource(root.usage, holder).unwrap();
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        state.loan_ledger = Some(ledger);
        state.loan_participant = Some(holder);
        state.resources = ResourceContext::new().unchecked_with_fact(fact);
        let protocol = AssumedMutexProtocol::bind(&state, root.usage).unwrap();
        (state, protocol)
    }

    fn typed_input() -> (
        CState,
        AssumedMutexProtocol,
        crate::kernel::CCompositeResourceDefinition,
    ) {
        use crate::kernel::*;
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let mutex = Pointer::symbolic(Variable(765));
        let description = ResourceDescription::new(
            "counter_state".into(),
            vec![CValue::pointer(mutex.clone()).into()].into(),
            schema.clone(),
        );
        let fact = CResourceFact::own(CResource::MutexUse(MutexUseIdentity {
            protected: Some(description.clone()),
            binding: None,
            initialization: None,
            mutex: mutex.clone(),
        }));
        let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        let (support, _) = resources.unique_owned_occurrence_for_fact(&fact).unwrap();
        let ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let (ledger, root) = ledger
            .borrowed_mutex_use_input_with_protected(holder, support, mutex, Some(description))
            .unwrap();
        let fact = ledger.mutex_use_resource(root.usage, holder).unwrap();
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        state.loan_participant = Some(holder);
        state.resources = ResourceContext::new().unchecked_with_fact(fact);
        state.loan_ledger = Some(ledger);
        let protocol = AssumedMutexProtocol::bind(&state, root.usage).unwrap();
        let definition = CCompositeResourceDefinition::new(
            "counter_state",
            vec![CParameter::new("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )
        .with_instance_schema(Some(schema))
        .with_mutex_guard(Some(CMutexGuardDeclaration {
            parameter_index: 0,
            field_offset_bytes: 0,
        }));
        (state, protocol, definition)
    }

    #[test]
    fn typed_acquisition_refreshes_fields_and_release_requires_owned_same_type() {
        let (state, protocol, definition) = typed_input();
        let assumptions = PureFactContext::new();
        let mut budget = crate::kernel::ExecutionBudget::new();
        let (first, guard) = protocol
            .acquire_with_payload(
                &state,
                &assumptions,
                Some(&definition),
                Some(Variable(810)),
                &mut budget,
            )
            .unwrap();
        let payload = guard.payload.as_ref().unwrap();
        assert!(
            first
                .state
                .resources
                .owned_instance(payload.identity())
                .is_some()
        );
        let mut missing = first.state.clone();
        missing.resources = missing
            .resources
            .without_fact_delaying_normalization(
                &CResourceFact::own(CResource::Instance(payload.clone())),
                &assumptions,
            )
            .unwrap();
        assert!(protocol.release(&missing, &guard, &assumptions).is_err());
        let replacement = crate::kernel::ResourceInstance::new(
            Variable(812),
            payload.name().into(),
            payload.arguments().to_vec().into(),
            payload.schema().clone(),
            payload.fields().to_vec().into(),
        )
        .unwrap();
        let mut replaced = missing.clone();
        replaced.resources = replaced
            .resources
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(replacement.clone())));
        let restored = protocol
            .release_with_payload(
                &replaced,
                &guard,
                &assumptions,
                Some(replacement.identity()),
            )
            .unwrap();
        assert!(
            restored
                .state
                .resources
                .owned_instance(replacement.identity())
                .is_none()
        );
        let wrong = crate::kernel::ResourceInstance::new(
            Variable(813),
            "different_type".into(),
            payload.arguments().to_vec().into(),
            payload.schema().clone(),
            payload.fields().to_vec().into(),
        )
        .unwrap();
        let mut wrong_state = missing.clone();
        wrong_state.resources = wrong_state
            .resources
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(wrong.clone())));
        assert!(
            protocol
                .release_with_payload(&wrong_state, &guard, &assumptions, Some(wrong.identity()))
                .is_err()
        );
        let released = protocol
            .release(&first.state, &guard, &assumptions)
            .unwrap();
        assert!(
            released
                .state
                .resources
                .owned_instance(payload.identity())
                .is_none()
        );
        let (_, second) = protocol
            .acquire_with_payload(
                &released.state,
                &assumptions,
                Some(&definition),
                Some(Variable(811)),
                &mut budget,
            )
            .unwrap();
        assert_ne!(payload.fields(), second.payload.unwrap().fields());
        let mut wrong = definition;
        wrong.guarded_by.as_mut().unwrap().field_offset_bytes = 4;
        assert!(
            protocol
                .acquire_with_payload(&state, &assumptions, Some(&wrong), None, &mut budget)
                .is_err()
        );
    }

    #[test]
    fn abstract_protocol_requires_actual_rooted_input_and_grants_no_payload_or_owner() {
        let (state, protocol) = input();
        assert_eq!(state.resources.facts().len(), 1);
        assert!(state.mutex_ledger.is_none());
        assert!(
            !state
                .resources
                .satisfies_fact(&protocol.lifetime, &PureFactContext::new())
        );
        let mut missing = state.clone();
        missing.resources = ResourceContext::new();
        assert!(AssumedMutexProtocol::bind(&missing, protocol.usage).is_err());
        assert!(protocol.acquire(&missing, &PureFactContext::new()).is_err());
        let mut concrete = state.clone();
        concrete.preserves_mutex_protocols = false;
        assert!(AssumedMutexProtocol::bind(&concrete, protocol.usage).is_err());
        let mut wrong = state.clone();
        wrong.loan_participant = Some(
            state
                .loan_ledger
                .as_ref()
                .unwrap()
                .fresh_participant()
                .unwrap(),
        );
        assert!(protocol.acquire(&wrong, &PureFactContext::new()).is_err());
        let (_, other) = input();
        assert!(other.acquire(&state, &PureFactContext::new()).is_err());
        // The ordinary C runtime entry remains frozen.
        assert!(
            MutexContext::new(state)
                .acquire_current(protocol.mutex(), &PureFactContext::new())
                .is_err()
        );
    }

    #[test]
    fn abstract_acquire_release_preserves_opaque_payload_and_retains_checked_evidence() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let (held, guard) = protocol.acquire(&state, &assumptions).unwrap();
        assert_eq!(held.state.memory, state.memory);
        assert!(held.state.mutex_ledger.is_none());
        assert_eq!(held.state.resources.facts().len(), 2);
        assert!(
            held.state
                .resources
                .satisfies_fact(&guard.fact, &assumptions)
        );
        assert!(
            held.state
                .resources
                .satisfies_fact(&protocol.use_fact, &assumptions)
        );
        assert!(
            !held
                .state
                .resources
                .satisfies_fact(&protocol.lifetime, &assumptions)
        );
        assert!(protocol.check_return(&held.state).is_err());
        assert!(protocol.acquire(&held.state, &assumptions).is_err());
        let released = protocol.release(&held.state, &guard, &assumptions).unwrap();
        assert_eq!(released.state.memory, state.memory);
        assert!(protocol.check_return(&released.state).is_ok());
        assert_eq!(released.state.resources.facts(), state.resources.facts());
        let evidence =
            crate::kernel::loans::concat_checked_loan_evidence(&held.evidence, &released.evidence);
        assert_eq!(evidence.len(), 2);
        assert!(evidence.is_valid());
        assert_eq!(
            evidence.recovered_ledger_for(
                state.loan_ledger.as_ref().unwrap(),
                protocol.holder,
                false
            ),
            released.state.loan_ledger
        );
        let (again, next_guard) = protocol.acquire(&released.state, &assumptions).unwrap();
        assert_ne!(guard.fact, next_guard.fact);
        assert!(
            protocol
                .release(&again.state, &guard, &assumptions)
                .is_err()
        );
        assert!(
            protocol
                .release(&again.state, &next_guard, &assumptions)
                .is_ok()
        );
    }

    #[test]
    fn hidden_guard_and_wrong_receipts_cannot_end_the_lifetime_hold() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let (held, mut guard) = protocol.acquire(&state, &assumptions).unwrap();
        let mut hidden = held.state.clone();
        hidden.resources = hidden
            .resources
            .without_fact(&guard.fact, &assumptions)
            .unwrap();
        assert!(protocol.acquire(&hidden, &assumptions).is_err());
        assert!(protocol.release(&hidden, &guard, &assumptions).is_err());
        assert!(protocol.check_return(&hidden).is_err());
        let (other_state, other) = input();
        let (_, other_guard) = other.acquire(&other_state, &assumptions).unwrap();
        assert!(
            protocol
                .release(&held.state, &other_guard, &assumptions)
                .is_err()
        );
        // Even a hostile receipt retaining the correct guard atom cannot
        // substitute another loan's hold and release its lifetime early.
        guard.hold = other_guard.hold;
        assert!(protocol.release(&held.state, &guard, &assumptions).is_err());
    }

    #[test]
    fn release_cannot_substitute_a_different_scope_hold_in_the_same_ledger() {
        let assumptions = PureFactContext::new();
        let (mut state, first) = input();
        let marker = CResourceFact::own(CResource::Token {
            name: "second input".into(),
            arguments: vec![].into(),
        });
        let resources = ResourceContext::new().unchecked_with_fact(marker.clone());
        let (support, _) = resources.unique_owned_occurrence_for_fact(&marker).unwrap();
        let (ledger, root) = state
            .loan_ledger
            .as_ref()
            .unwrap()
            .borrowed_mutex_use_input(first.holder, support, Pointer::symbolic(Variable(766)))
            .unwrap();
        let second_fact = ledger.mutex_use_resource(root.usage, first.holder).unwrap();
        state.resources = state.resources.unchecked_with_fact(second_fact);
        state.loan_ledger = Some(ledger);
        let second = AssumedMutexProtocol::bind(&state, root.usage).unwrap();
        let (held_first, mut first_guard) = first.acquire(&state, &assumptions).unwrap();
        let (held_both, second_guard) = second.acquire(&held_first.state, &assumptions).unwrap();
        let correct_hold = first_guard.hold;
        first_guard.hold = second_guard.hold;
        assert!(
            first
                .release(&held_both.state, &first_guard, &assumptions)
                .is_err()
        );
        assert!(second.check_return(&held_both.state).is_err());
        first_guard.hold = correct_hold;
        let released_first = first
            .release(&held_both.state, &first_guard, &assumptions)
            .unwrap();
        let released_both = second
            .release(&released_first.state, &second_guard, &assumptions)
            .unwrap();
        first.check_return(&released_both.state).unwrap();
        second.check_return(&released_both.state).unwrap();
    }

    #[test]
    fn abstract_protocol_transitions_ignore_unrelated_resource_frames() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let (mut state, protocol) = input();
            for index in 0..size {
                state.resources =
                    state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (held, guard) = protocol.acquire(&state, &assumptions).unwrap();
                    let released = protocol.release(&held.state, &guard, &assumptions).unwrap();
                    protocol.check_return(&released.state).unwrap();
                    released
                })
            });
            assert_eq!(returned.state.resources.facts().len(), size + 1);
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "abstract protocol scans unrelated resources: {samples:?}"
            );
        }
    }

    #[test]
    fn opaque_runtime_balanced_transition_retains_receipt_hold_and_evidence() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let mutex = protocol.mutex();
        let (held, acquired) =
            opaque_runtime_transition(&state, mutex, true, &assumptions).unwrap();
        let receipt = held
            .opaque_mutex_acquisitions
            .as_ref()
            .unwrap()
            .guard_resource(mutex)
            .unwrap();
        assert!(held.resources.satisfies_fact(&receipt, &assumptions));
        assert!(protocol.check_return(&held).is_err());
        assert_eq!(held.memory, state.memory);
        let (released, returned) =
            opaque_runtime_transition(&held, mutex, false, &assumptions).unwrap();
        assert!(released.opaque_mutex_acquisitions.is_none());
        assert!(protocol.check_return(&released).is_ok());
        assert_eq!(released.resources.facts(), state.resources.facts());
        assert_eq!(released.memory, state.memory);
        let evidence = crate::kernel::loans::concat_checked_loan_evidence(&acquired, &returned);
        assert_eq!(evidence.len(), 2);
        assert!(evidence.is_valid());
        assert_eq!(
            evidence.recovered_ledger_for(
                state.loan_ledger.as_ref().unwrap(),
                protocol.holder,
                false
            ),
            released.loan_ledger
        );
    }

    #[test]
    fn opaque_runtime_hidden_guard_does_not_release_its_lifetime_hold() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let mutex = protocol.mutex();
        let (held, _) = opaque_runtime_transition(&state, mutex, true, &assumptions).unwrap();
        let receipt = held
            .opaque_mutex_acquisitions
            .as_ref()
            .unwrap()
            .guard_resource(mutex)
            .unwrap();
        let mut hidden = held.clone();
        hidden.resources = hidden
            .resources
            .without_fact(&receipt, &assumptions)
            .unwrap();
        assert!(opaque_runtime_transition(&hidden, mutex, false, &assumptions).is_err());
        assert!(opaque_runtime_transition(&hidden, mutex, true, &assumptions).is_err());
        assert!(protocol.check_return(&hidden).is_err());
    }

    #[test]
    fn opaque_runtime_rejects_duplicate_lock_and_wrong_mutex_unlock() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let mutex = protocol.mutex();
        let (held, _) = opaque_runtime_transition(&state, mutex, true, &assumptions).unwrap();
        assert!(opaque_runtime_transition(&held, mutex, true, &assumptions).is_err());
        let wrong = Pointer::symbolic(Variable(766));
        assert!(opaque_runtime_transition(&held, &wrong, false, &assumptions).is_err());
        assert!(protocol.check_return(&held).is_err());
        let (released, _) = opaque_runtime_transition(&held, mutex, false, &assumptions).unwrap();
        assert!(protocol.check_return(&released).is_ok());
    }

    #[test]
    fn opaque_runtime_stale_receipt_cannot_release_a_later_acquisition() {
        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let mutex = protocol.mutex();
        let (first, _) = opaque_runtime_transition(&state, mutex, true, &assumptions).unwrap();
        let old = first
            .opaque_mutex_acquisitions
            .as_ref()
            .unwrap()
            .receipts
            .get(mutex)
            .unwrap()
            .clone();
        let (between, _) = opaque_runtime_transition(&first, mutex, false, &assumptions).unwrap();
        let (second, _) = opaque_runtime_transition(&between, mutex, true, &assumptions).unwrap();
        let current = second
            .opaque_mutex_acquisitions
            .as_ref()
            .unwrap()
            .guard_resource(mutex)
            .unwrap();
        assert_ne!(old.fact, current);
        let mut stale = second.clone();
        let held = stale.opaque_mutex_acquisitions.as_mut().unwrap();
        held.receipts = held.receipts.with_inserted(mutex.clone(), old);
        assert!(opaque_runtime_transition(&stale, mutex, false, &assumptions).is_err());
        assert!(protocol.check_return(&stale).is_err());
        let (released, _) = opaque_runtime_transition(&second, mutex, false, &assumptions).unwrap();
        assert!(protocol.check_return(&released).is_ok());
    }

    #[test]
    fn opaque_runtime_void_fallthrough_rejects_an_outstanding_local_acquisition() {
        use crate::kernel::functions::{ResourceTransitionPurpose, contract_exit_outcome};
        use crate::kernel::{
            CFunctionOutcome, CRuntimeError, CStatement, CStatementOutcome, CType, ExecutionBudget,
            c_function,
        };

        let assumptions = PureFactContext::new();
        let (state, protocol) = input();
        let (held, _) =
            opaque_runtime_transition(&state, protocol.mutex(), true, &assumptions).unwrap();
        let (released, _) =
            opaque_runtime_transition(&held, protocol.mutex(), false, &assumptions).unwrap();
        let function = c_function(CType::Void, "fallthrough", vec![], CStatement::Skip);
        for (exit, outstanding) in [(held, true), (released, false)] {
            let (outcome, _, _) = contract_exit_outcome(
                &state,
                &function,
                &[],
                CStatementOutcome::Normal(Box::new(exit)),
                vec![],
                &assumptions,
                &mut ExecutionBudget::default(),
                ResourceTransitionPurpose::FunctionBoundary,
            )
            .expect("bounded exit")
            .expect("exit outcome");
            if outstanding {
                assert!(matches!(outcome, CFunctionOutcome::RuntimeError(
                    CRuntimeError::FunctionContract(ref message)
                ) if message.contains("cannot return with a held mutex")));
            } else {
                assert!(matches!(outcome, CFunctionOutcome::Return { .. }));
            }
        }
    }

    #[test]
    fn opaque_runtime_transitions_ignore_unrelated_resource_frames() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let (mut state, protocol) = input();
            for index in 0..size {
                state.resources =
                    state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (held, _) =
                        opaque_runtime_transition(&state, protocol.mutex(), true, &assumptions)
                            .unwrap();
                    let (released, _) =
                        opaque_runtime_transition(&held, protocol.mutex(), false, &assumptions)
                            .unwrap();
                    protocol.check_return(&released).unwrap();
                    released
                })
            });
            assert_eq!(returned.resources.facts().len(), size + 1);
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "opaque runtime transition scans unrelated resources: {samples:?}"
            );
        }
    }
}
