//! Internal, checked fork/join ownership transitions.
//!
//! The modeled pthread binding connects these transitions to checked C calls.
//! A successful creation reserves a verified, terminating worker's task once,
//! havocs only its checked mutable footprint, and withholds its outputs until
//! join. The opaque completion right lives in a persistent, linear registry;
//! an integer or a resource with a convenient name cannot manufacture it.
//!
//! The initial profile supports explicit external-memory ownership and stable views with
//! no escaping borrows, allocation, exceptions, cancellation, or detachment.
//! Join assumes success only for this context's live, unique, terminating child.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::persistent::PersistentMap;

use super::functions::suspend_verified_worker;
use super::loans::{LoanLedger, LoanViewBinding, LoanViewBindings, StableViewTransferPlan};
use super::{
    Bitvector32Term, CExecutionEnvironment, CMemory, CMemoryRange, CResourceFact, CRuntimeError,
    CState, CValue, CVerifiedFunctionRule, CVerifiedFunctionTerminationRule, ConditionTerm,
    ExecutionBudget, ExecutionPureFact, ExecutionResult, Pointer, PointerBlock, Proposition,
    PureFactContext, ResourceContext,
};

/// A kernel identity, not the integer representation of `pthread_t`. The C
/// binding writes an opaque value carrying this identity to a checked slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct ThreadHandle(u64);

/// An explicit runtime assumption, scoped by `join` to a live child of this
/// parent with matching termination evidence. It grants no right by itself.
#[derive(Clone, Copy, Debug)]
pub(super) enum JoinRuntimeAssumption {
    ValidJoinSucceeds,
}

/// Constructed only by the shared verified-call engine, before synchronous
/// recovery. The worker's output delta is separate from the caller's frame.
#[derive(Clone, Debug)]
pub(super) struct WorkerCompletion {
    plan: StableViewTransferPlan,
    outputs: ResourceContext,
    memory: CMemory,
    effects: Vec<CMemoryRange>,
    facts: Vec<ExecutionPureFact>,
    mutex_ledger: Option<super::mutexes::MutexLedger>,
    population_counts: Vec<WorkerPopulationCount>,
    creation: Option<WorkerCreation>,
}

/// Authority-mode creation ledger transport. Create applies the worker's
/// checked contract under its call identity, exactly as a sequential call
/// does before it returns, and gives the parent that ledger back without
/// returning the worker's resources. Join performs the sequential return:
/// the worker's outputs move back to the parent and the call must retain
/// nothing. Join itself authorizes no population transition.
#[derive(Clone, Debug)]
pub(super) struct WorkerCreation {
    pub(super) parent_after_create: super::population_authority::c_creation::CreationEvents,
    pub(super) worker: super::population_authority::c_creation::CreationEvents,
    pub(super) definitions: Vec<super::CCompositeResourceDefinition>,
    pub(super) deferred: Option<DeferredMemberExchange>,
}

/// A locked worker's declared member change. Its authority stays in the
/// mutex escrow while the worker is outstanding, and the worker may lock at
/// any time before it finishes, so create records nothing. Join is the first
/// point at which the change is known to have happened; it lends the
/// escrowed authority to the worker's call identity, applies the change, and
/// takes the authority back, exactly as a sequential locked call returns.
/// Until then the parent cannot observe that population's total.
#[derive(Clone, Debug)]
pub(super) struct DeferredMemberExchange {
    pub(super) block: PointerBlock,
    pub(super) description: super::ResourceDescription,
    pub(super) produce: bool,
    pub(super) quantity: Bitvector32Term,
    pub(super) exclusive: bool,
}

/// A checked contract effect accumulated into a reserved final total. That
/// total becomes observable only after every outstanding worker has joined.
/// Fixed non-increasing abstract effects can overlap; stateful populations
/// remain thread confined until shared-body custody is supported.
#[derive(Clone, Debug)]
pub(super) struct WorkerPopulationCount {
    pub(super) name: String,
    pub(super) arguments: super::ResourceArguments,
    pub(super) before: Bitvector32Term,
    pub(super) after: Bitvector32Term,
    pub(super) overlap_safe: bool,
}

/// Keep a fixed-effect worker cohort's symbolic total bounded in size.
/// Repeated subtraction must not build a path-length expression that every
/// later create/join clones. Count effects are nonnegative fixed quantities.
pub(super) fn consume_reserved_population(
    prior: Bitvector32Term,
    quantity: u32,
) -> Option<Bitvector32Term> {
    crate::instrumentation::record_deterministic_work(1);
    match prior {
        Bitvector32Term::Subtract(base, previous) if previous.as_const().is_some() => {
            let total = previous.as_const()?.checked_add(quantity)?;
            Some(Bitvector32Term::subtract(*base, total.into()))
        }
        prior => Some(Bitvector32Term::subtract(prior, quantity.into())),
    }
}

impl WorkerPopulationCount {
    fn reserve(&self, state: &mut CState) {
        Arc::make_mut(&mut state.population_effects)
            .pending_counts
            .insert(super::CCountedPopulation {
                name: self.name.clone(),
                arguments: self.arguments.clone(),
                count: self.after.clone(),
                family_observation_marker: false,
            });
        self.ensure_count_entry(state);
    }

    fn ensure_count_entry(&self, state: &mut CState) {
        // Absence already denotes zero for an observed family. Record the
        // key in both create outcomes so pending wildcard observations can
        // find it, without changing the total or creating any resource unit.
        if state
            .counted_population(&self.name, &self.arguments)
            .is_none()
        {
            *state = state.clone().with_counted_population(
                self.name.clone(),
                self.arguments.clone(),
                self.before.clone(),
            );
        }
    }

    fn can_complete(&self, state: &CState) -> bool {
        state
            .population_effects
            .pending_counts
            .get(&self.name, &self.arguments, false)
            .is_some()
            && state.counted_population(&self.name, &self.arguments) == Some(&self.before)
    }

    fn complete(&self, state: &mut CState) {
        let final_count = state
            .population_effects
            .pending_counts
            .get(&self.name, &self.arguments, false)
            .expect("registered population completion")
            .count
            .clone();
        Arc::make_mut(&mut state.population_effects)
            .pending_counts
            .remove(&self.name, &self.arguments);
        *state = state.clone().with_counted_population(
            self.name.clone(),
            self.arguments.clone(),
            final_count,
        );
    }
}

impl WorkerCompletion {
    pub(super) fn checked(
        plan: StableViewTransferPlan,
        outputs: ResourceContext,
        memory: CMemory,
        effects: Vec<CMemoryRange>,
        facts: Vec<ExecutionPureFact>,
        mutex_ledger: Option<super::mutexes::MutexLedger>,
        population_counts: Vec<WorkerPopulationCount>,
        creation: Option<WorkerCreation>,
    ) -> Self {
        Self {
            plan,
            outputs,
            memory,
            effects,
            facts,
            mutex_ledger,
            population_counts,
            creation,
        }
    }
}

#[derive(Clone, Debug)]
struct CompletionRight {
    // Retain the exact callback, task argument, and checked resource plan.
    worker: Arc<CVerifiedFunctionRule>,
    argument: CValue,
    completion: WorkerCompletion,
}

#[derive(Clone)]
pub(super) struct PendingThreadCreate {
    storage: Arc<PendingThreadCreateStorage>,
}

/// Checked operations on the authority common to both create outcomes.
/// Failure already contains these operations in the visible C state; success
/// applies them to the worker's checked post-create memory in source order.
#[derive(Clone, Debug)]
pub(super) enum PendingThreadMemoryDelta {
    Declare { block: PointerBlock, bytes: u32 },
    Store { pointer: Pointer, value: CValue },
}

/// Only the authority changed by create is guarded. The visible C state keeps
/// the caller's current locals and memory, including disjoint intervening
/// stores; selecting an outcome never restores a captured parent state.
struct PendingCreateAuthority {
    resources: ResourceContext,
    pending_population_counts: super::primitives::CountedPopulations,
    loan_ledger: Option<LoanLedger>,
    loan_view_bindings: LoanViewBindings,
    thread_ledger: Option<ThreadLedger>,
    mutex_ledger: Option<super::mutexes::MutexLedger>,
    mutex_input_reservations: Option<super::mutexes::MutexInputReservations>,
    opaque_mutex_acquisitions: Option<super::mutexes::OpaqueMutexAcquisitions>,
    named_mutex_authorities: Option<Arc<super::named_authority::NamedMutexAuthorities>>,
    creation: Option<super::population_authority::c_creation::CreationEvents>,
}

impl PendingCreateAuthority {
    fn from_state(state: &CState) -> Self {
        Self {
            resources: state.resources.clone(),
            pending_population_counts: state.population_effects.pending_counts.clone(),
            loan_ledger: state.loan_ledger.clone(),
            loan_view_bindings: state.loan_view_bindings.clone(),
            thread_ledger: state.thread_ledger.clone(),
            mutex_ledger: state.mutex_ledger.clone(),
            mutex_input_reservations: state.mutex_input_reservations.clone(),
            opaque_mutex_acquisitions: state.opaque_mutex_acquisitions.clone(),
            named_mutex_authorities: state.named_mutex_authorities.clone(),
            creation: state.population_effects.creation.clone(),
        }
    }

    fn install(&self, state: &mut CState) {
        state.resources = self.resources.clone();
        Arc::make_mut(&mut state.population_effects).pending_counts =
            self.pending_population_counts.clone();
        state.loan_ledger = self.loan_ledger.clone();
        state.loan_view_bindings = self.loan_view_bindings.clone();
        state.thread_ledger = self.thread_ledger.clone();
        state.mutex_ledger = self.mutex_ledger.clone();
        state.mutex_input_reservations = self.mutex_input_reservations.clone();
        state.opaque_mutex_acquisitions = self.opaque_mutex_acquisitions.clone();
        state.named_mutex_authorities = self.named_mutex_authorities.clone();
        Arc::make_mut(&mut state.population_effects).creation = self.creation.clone();
    }
}

struct PendingThreadCreateStorage {
    identity: u64,
    status: Bitvector32Term,
    handle_slot: Pointer,
    handle_value: CValue,
    success_memory: CMemory,
    success: PendingCreateAuthority,
    failure: PendingCreateAuthority,
    deltas: PersistentMap<u64, PendingThreadMemoryDelta>,
    next_delta: u64,
}

impl PendingThreadCreate {
    fn fresh_identity() -> u64 {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    pub(super) fn protects_local(&self, state: &CState, name: &str) -> bool {
        state
            .locals
            .slots
            .get(&self.storage.handle_slot)
            .is_some_and(|output| output == name)
    }

    pub(super) fn has_local_handle_slot(&self, state: &CState) -> bool {
        state.locals.slots.contains_key(&self.storage.handle_slot)
    }

    pub(super) fn new(
        status: Bitvector32Term,
        handle_slot: Pointer,
        handle_value: CValue,
        success: &CState,
        failure: &CState,
    ) -> Self {
        debug_assert!(success.pending_thread_create.is_none());
        debug_assert!(failure.pending_thread_create.is_none());
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status,
                handle_slot,
                handle_value,
                success_memory: success.memory.clone(),
                success: PendingCreateAuthority::from_state(success),
                failure: PendingCreateAuthority::from_state(failure),
                deltas: PersistentMap::default(),
                next_delta: 0,
            }),
        }
    }

    pub(super) fn with_delta(&self, delta: PendingThreadMemoryDelta) -> Self {
        let storage = &self.storage;
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status: storage.status.clone(),
                handle_slot: storage.handle_slot.clone(),
                handle_value: storage.handle_value.clone(),
                success_memory: storage.success_memory.clone(),
                success: PendingCreateAuthority {
                    resources: storage.success.resources.clone(),
                    pending_population_counts: storage.success.pending_population_counts.clone(),
                    loan_ledger: storage.success.loan_ledger.clone(),
                    loan_view_bindings: storage.success.loan_view_bindings.clone(),
                    thread_ledger: storage.success.thread_ledger.clone(),
                    mutex_ledger: storage.success.mutex_ledger.clone(),
                    mutex_input_reservations: storage.success.mutex_input_reservations.clone(),
                    opaque_mutex_acquisitions: storage.success.opaque_mutex_acquisitions.clone(),
                    named_mutex_authorities: storage.success.named_mutex_authorities.clone(),
                    creation: storage.success.creation.clone(),
                },
                failure: PendingCreateAuthority {
                    resources: storage.failure.resources.clone(),
                    pending_population_counts: storage.failure.pending_population_counts.clone(),
                    loan_ledger: storage.failure.loan_ledger.clone(),
                    loan_view_bindings: storage.failure.loan_view_bindings.clone(),
                    thread_ledger: storage.failure.thread_ledger.clone(),
                    mutex_ledger: storage.failure.mutex_ledger.clone(),
                    mutex_input_reservations: storage.failure.mutex_input_reservations.clone(),
                    opaque_mutex_acquisitions: storage.failure.opaque_mutex_acquisitions.clone(),
                    named_mutex_authorities: storage.failure.named_mutex_authorities.clone(),
                    creation: storage.failure.creation.clone(),
                },
                deltas: storage.deltas.with_inserted(storage.next_delta, delta),
                next_delta: storage.next_delta + 1,
            }),
        }
    }

    pub(super) fn map_terms(
        &self,
        status: impl Fn(&Bitvector32Term) -> Bitvector32Term,
        resources: impl Fn(&ResourceContext) -> ResourceContext,
        pointer: impl Fn(&Pointer) -> Pointer,
        value: impl Fn(&CValue) -> CValue,
        memory: impl Fn(&CMemory) -> CMemory,
        counts: impl Fn(&super::primitives::CountedPopulations) -> super::primitives::CountedPopulations,
    ) -> Self {
        let storage = &self.storage;
        let map_authority = |authority: &PendingCreateAuthority| PendingCreateAuthority {
            resources: resources(&authority.resources),
            pending_population_counts: counts(&authority.pending_population_counts),
            loan_ledger: authority.loan_ledger.clone(),
            loan_view_bindings: authority.loan_view_bindings.clone(),
            thread_ledger: authority.thread_ledger.clone(),
            mutex_ledger: authority.mutex_ledger.clone(),
            mutex_input_reservations: authority.mutex_input_reservations.clone(),
            opaque_mutex_acquisitions: authority.opaque_mutex_acquisitions.clone(),
            named_mutex_authorities: authority.named_mutex_authorities.clone(),
            creation: authority.creation.clone(),
        };
        let mut deltas = PersistentMap::default();
        for (index, delta) in &storage.deltas {
            let mapped = match delta {
                PendingThreadMemoryDelta::Declare { block, bytes } => {
                    PendingThreadMemoryDelta::Declare {
                        block: block.clone(),
                        bytes: *bytes,
                    }
                }
                PendingThreadMemoryDelta::Store {
                    pointer: address,
                    value: stored,
                } => PendingThreadMemoryDelta::Store {
                    pointer: pointer(address),
                    value: value(stored),
                },
            };
            deltas = deltas.with_inserted(*index, mapped);
        }
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status: status(&storage.status),
                handle_slot: pointer(&storage.handle_slot),
                handle_value: value(&storage.handle_value),
                success_memory: memory(&storage.success_memory),
                success: map_authority(&storage.success),
                failure: map_authority(&storage.failure),
                deltas,
                next_delta: storage.next_delta,
            }),
        }
    }

    /// Select Count authority without applying memory deltas or acquiring
    /// join rights. Before status is known, reserve anything success reserves.
    pub(super) fn count_authority(
        &self,
        assumptions: &PureFactContext,
    ) -> &super::primitives::CountedPopulations {
        let zero = ConditionTerm::Bitvector32Equal(
            Box::new(self.storage.status.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let selected = if assumptions.decide(&zero) == Some(false) {
            &self.storage.failure
        } else {
            &self.storage.success
        };
        &selected.pending_population_counts
    }

    pub(super) fn resolve(
        &self,
        visible: &CState,
        assumptions: &PureFactContext,
    ) -> Option<CState> {
        let zero = ConditionTerm::Bitvector32Equal(
            Box::new(self.storage.status.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let success = assumptions.decide(&zero)?;
        let mut selected = visible.clone();
        selected.pending_thread_create = None;
        if success {
            self.storage.success.install(&mut selected);
            let mut memory = self.storage.success_memory.clone();
            for (_, delta) in &self.storage.deltas {
                crate::instrumentation::record_deterministic_work(1);
                memory = match delta {
                    PendingThreadMemoryDelta::Declare { block, bytes } => {
                        memory.with_block(block.clone(), *bytes)
                    }
                    PendingThreadMemoryDelta::Store { pointer, value } => memory
                        .without_possible_aliasing_cells(pointer, value.byte_width(), assumptions)
                        .store_with_context(pointer.clone(), value.clone(), assumptions),
                };
            }
            selected.set_memory(memory);
            if let Some(name) = selected
                .locals
                .slots
                .get(&self.storage.handle_slot)
                .cloned()
            {
                let binding = selected.locals.binding(&name).cloned();
                if let Some(
                    super::CLocalBinding::Object {
                        c_type,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                        ..
                    }
                    | super::CLocalBinding::UninitializedObject {
                        c_type,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                        ..
                    },
                ) = binding
                {
                    selected.locals.set_typed_with_all_qualifiers(
                        name,
                        self.storage.handle_value.clone(),
                        c_type,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    );
                }
            }
        } else {
            self.storage.failure.install(&mut selected);
        }
        Some(selected)
    }
}

impl std::fmt::Debug for PendingThreadCreate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PendingThreadCreate")
            .field("identity", &self.storage.identity)
            .field("status", &self.storage.status)
            .field("intervening_steps", &self.storage.next_delta)
            .finish()
    }
}

impl PartialEq for PendingThreadCreate {
    fn eq(&self, other: &Self) -> bool {
        self.storage.identity == other.storage.identity
    }
}
impl Eq for PendingThreadCreate {}
impl Hash for PendingThreadCreate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.identity.hash(state);
    }
}
impl PartialOrd for PendingThreadCreate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PendingThreadCreate {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.identity.cmp(&other.storage.identity)
    }
}

/// Path-local completion authority stored with ordinary C execution state.
/// Clones share the root; an insertion or removal touches only one map path.
/// Like the loan ledger, equality uses a fresh state identity so ordinary
/// state comparisons never walk unrelated live children.
#[derive(Clone)]
pub(super) struct ThreadLedger {
    storage: Arc<ThreadLedgerStorage>,
}

struct ThreadLedgerStorage {
    state: u64,
    rights: PersistentMap<ThreadHandle, Arc<CompletionRight>>,
    loan_trace: Option<ThreadLoanTrace>,
    local_views: PersistentMap<CResourceFact, LoanViewBinding>,
    mutex_workers: PersistentMap<Pointer, usize>,
    population_workers: PersistentMap<(String, super::ResourceArguments), (usize, bool)>,
}

/// The checked loan root before the first outstanding create and the root
/// reached by subsequent checked creates and joins on this path. This is
/// retained beside the linear rights, so contract certification can check a
/// view-bearing parent after every child has joined without reconstructing
/// unrelated ledger history.
#[derive(Clone)]
struct ThreadLoanTrace {
    origin: LoanLedger,
    current: LoanLedger,
    participant: super::loans::LoanParticipantId,
}

impl ThreadLedger {
    fn fresh_state() -> u64 {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    pub(super) fn new() -> Self {
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: PersistentMap::default(),
                loan_trace: None,
                local_views: PersistentMap::default(),
                mutex_workers: PersistentMap::default(),
                population_workers: PersistentMap::default(),
            }),
        }
    }

    fn right(&self, handle: ThreadHandle) -> Option<&Arc<CompletionRight>> {
        self.storage.rights.get(&handle)
    }

    /// Whether an outstanding worker returns this exact authority at join.
    /// Used only to explain a refused observation; work is linear in the
    /// live workers of this path.
    pub(super) fn lends_population_authority(
        &self,
        description: &super::ResourceDescription,
    ) -> bool {
        self.storage.rights.iter().any(|(_, right)| {
            crate::instrumentation::record_deterministic_work(1);
            right.completion.creation.is_some()
                && right.completion.outputs.facts().iter().any(|fact| {
                    matches!(
                        fact,
                        CResourceFact::Own(super::CResource::PopulationAuthority(lent), _)
                            if lent == description
                    )
                })
        })
    }

    /// Whether an outstanding locked worker will change this population at
    /// its join. Work is linear in the live workers of this path.
    pub(super) fn defers_population_change(
        &self,
        description: &super::ResourceDescription,
    ) -> bool {
        self.storage.rights.iter().any(|(_, right)| {
            crate::instrumentation::record_deterministic_work(1);
            right
                .completion
                .creation
                .as_ref()
                .and_then(|creation| creation.deferred.as_ref())
                .is_some_and(|deferred| {
                    deferred.description.family() == description.family()
                        && deferred.description.arguments() == description.arguments()
                })
        })
    }

    pub(super) fn has_mutex_workers(&self, mutex: &Pointer) -> bool {
        self.storage.mutex_workers.contains_key(mutex)
    }

    pub(super) fn population_allows_overlap(
        &self,
        name: &str,
        arguments: &super::ResourceArguments,
    ) -> bool {
        self.storage
            .population_workers
            .get(&(name.into(), arguments.clone()))
            .is_some_and(|(_, safe)| *safe)
    }

    fn population_workers(&self, effect: &WorkerPopulationCount) -> usize {
        self.storage
            .population_workers
            .get(&(effect.name.clone(), effect.arguments.clone()))
            .map_or(0, |(count, _)| *count)
    }

    pub(super) fn has_live_rights(&self) -> bool {
        !self.storage.rights.is_empty()
    }

    pub(super) fn local_view_binding(&self, fact: &CResourceFact) -> Option<&LoanViewBinding> {
        self.storage.local_views.get(fact)
    }

    pub(super) fn witnesses_loan_recovery(
        &self,
        origin: &LoanLedger,
        current: &LoanLedger,
        participant: super::loans::LoanParticipantId,
    ) -> bool {
        self.storage.rights.is_empty()
            && self.storage.local_views.is_empty()
            && self.storage.mutex_workers.is_empty()
            && self.storage.population_workers.is_empty()
            && self.storage.loan_trace.as_ref().is_some_and(|trace| {
                trace.origin == *origin
                    && trace.current == *current
                    && trace.participant == participant
            })
    }

    fn advanced_loan_trace(
        &self,
        before: &LoanLedger,
        after: &LoanLedger,
        participant: super::loans::LoanParticipantId,
    ) -> Option<ThreadLoanTrace> {
        match self.storage.loan_trace.as_ref() {
            Some(trace) if trace.current == *before && trace.participant == participant => {
                Some(ThreadLoanTrace {
                    origin: trace.origin.clone(),
                    current: after.clone(),
                    participant,
                })
            }
            _ if self.storage.rights.is_empty() => Some(ThreadLoanTrace {
                origin: before.clone(),
                current: after.clone(),
                participant,
            }),
            _ => None,
        }
    }

    fn with_right(
        &self,
        handle: ThreadHandle,
        right: CompletionRight,
        before: &LoanLedger,
        after: &LoanLedger,
        participant: super::loans::LoanParticipantId,
    ) -> Self {
        let mut local_views = self.storage.local_views.clone();
        let mut mutex_workers = self.storage.mutex_workers.clone();
        for usage in &right.completion.plan.mutex_uses {
            let fact = usage.required_resource();
            let super::CResource::MutexUse(identity) = fact.resource() else {
                unreachable!()
            };
            let count = mutex_workers.get(&identity.mutex).copied().unwrap_or(0);
            mutex_workers = mutex_workers.with_inserted(identity.mutex.clone(), count + 1);
        }
        let mut population_workers = self.storage.population_workers.clone();
        for effect in &right.completion.population_counts {
            let key = (effect.name.clone(), effect.arguments.clone());
            let (count, safe) = population_workers.get(&key).copied().unwrap_or((0, true));
            population_workers =
                population_workers.with_inserted(key, (count + 1, safe && effect.overlap_safe));
        }
        for (fact, binding) in right.completion.plan.suspended_local_parents() {
            local_views = local_views.with_inserted(fact.clone(), binding.clone());
        }
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: self.storage.rights.with_inserted(handle, Arc::new(right)),
                loan_trace: self.advanced_loan_trace(before, after, participant),
                local_views,
                mutex_workers,
                population_workers,
            }),
        }
    }

    fn without_right(
        &self,
        handle: ThreadHandle,
        before: &LoanLedger,
        after: &LoanLedger,
        participant: super::loans::LoanParticipantId,
        local_updates: &BTreeMap<CResourceFact, Option<LoanViewBinding>>,
    ) -> Self {
        let mut local_views = self.storage.local_views.clone();
        let mut mutex_workers = self.storage.mutex_workers.clone();
        let mut population_workers = self.storage.population_workers.clone();
        if let Some(right) = self.right(handle) {
            for effect in &right.completion.population_counts {
                let key = (effect.name.clone(), effect.arguments.clone());
                let (count, safe) = *population_workers
                    .get(&key)
                    .expect("registered population worker");
                population_workers = if count == 1 {
                    population_workers.without_key(&key)
                } else {
                    population_workers.with_inserted(key, (count - 1, safe))
                };
            }
            for usage in &right.completion.plan.mutex_uses {
                let fact = usage.required_resource();
                let super::CResource::MutexUse(identity) = fact.resource() else {
                    unreachable!()
                };
                let count = *mutex_workers
                    .get(&identity.mutex)
                    .expect("registered mutex worker");
                mutex_workers = if count == 1 {
                    mutex_workers.without_key(&identity.mutex)
                } else {
                    mutex_workers.with_inserted(identity.mutex.clone(), count - 1)
                };
            }
        }
        for (fact, binding) in local_updates {
            local_views = match binding {
                Some(binding) => local_views.with_inserted(fact.clone(), binding.clone()),
                None => local_views.without_key(fact),
            };
        }
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: self.storage.rights.without_key(&handle),
                loan_trace: self.advanced_loan_trace(before, after, participant),
                local_views,
                mutex_workers,
                population_workers,
            }),
        }
    }
}

impl ThreadHandle {
    pub(super) fn c_value(self) -> CValue {
        CValue::UInt64(super::Bitvector32Term::PureFunctionApplication {
            // This name cannot be spelled by C or Click source. The term is
            // copied as an opaque pthread_t value, never derived from its
            // machine integer representation.
            name: format!("\0click.pthread.handle:{}", self.0),
            arguments: vec![],
        })
    }

    pub(super) fn from_c_value(value: &CValue) -> Option<Self> {
        match value {
            CValue::UInt64(super::Bitvector32Term::PureFunctionApplication { name, arguments })
                if arguments.is_empty() =>
            {
                name.strip_prefix("\0click.pthread.handle:")?
                    .parse()
                    .ok()
                    .map(Self)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod handle_tests {
    use super::*;

    #[test]
    fn handle_identity_survives_symbolic_variable_substitution() {
        let handle = ThreadHandle(42);
        let value = handle.c_value();
        let substituted = super::super::reasoning::substitute_bitvector_variable_in_c_value(
            &value,
            super::super::Variable(42),
            &super::super::Bitvector32Term::Variable(super::super::Variable(43)),
        );
        assert_eq!(substituted, value);
        assert_eq!(ThreadHandle::from_c_value(&substituted), Some(handle));
        assert_ne!(substituted, ThreadHandle(43).c_value());
    }
}

impl std::fmt::Debug for ThreadLedger {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ThreadLedger")
            .field("state", &self.storage.state)
            .field("live_rights", &self.storage.rights.len())
            .finish()
    }
}

impl PartialEq for ThreadLedger {
    fn eq(&self, other: &Self) -> bool {
        self.storage.state == other.storage.state
    }
}

impl Eq for ThreadLedger {}

impl Hash for ThreadLedger {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.state.hash(state);
    }
}

impl PartialOrd for ThreadLedger {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ThreadLedger {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.state.cmp(&other.storage.state)
    }
}

/// A checked task application before the runtime chooses whether creation
/// succeeded. Both outcomes are available only after the worker contract and
/// exact termination evidence have been validated against this parent.
pub(super) struct PreparedThreadCreate<'a> {
    parent: &'a ThreadContext,
    worker: &'a CVerifiedFunctionRule,
    argument: CValue,
    completion: WorkerCompletion,
    retained_names: Option<Arc<super::named_authority::NamedMutexAuthorities>>,
}

impl PreparedThreadCreate<'_> {
    pub(super) fn failure(&self) -> ThreadContext {
        let mut next = self.parent.clone();
        for count in &self.completion.population_counts {
            count.ensure_count_entry(&mut next.parent);
        }
        next
    }

    pub(super) fn success(self) -> (ThreadContext, ThreadHandle, ExecutionPureFact) {
        static NEXT_HANDLE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let handle = ThreadHandle(NEXT_HANDLE.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
        let effect = ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
            before: self.parent.parent.memory().clone(),
            after: self.completion.memory.clone(),
            mutable_ranges: self.completion.effects.clone(),
        })
        .into_certified();
        let mut next = self.parent.clone();
        next.parent = next
            .parent
            .with_resource_context(
                self.completion
                    .plan
                    .caller_resources_after_requirements
                    .clone(),
            )
            .with_loan_ledger(Some(self.completion.plan.ledger.clone()))
            .with_loan_view_bindings(
                self.completion
                    .plan
                    .caller_view_bindings_after_requirements()
                    .clone(),
            )
            .with_memory(self.completion.memory.clone());
        for count in &self.completion.population_counts {
            count.reserve(&mut next.parent);
        }
        if let Some(creation) = &self.completion.creation {
            Arc::make_mut(&mut next.parent.population_effects).creation =
                Some(creation.parent_after_create.clone());
        }
        next.parent.mutex_ledger = self.completion.mutex_ledger.clone();
        next.parent.named_mutex_authorities = self.retained_names;
        let before_loans = self.parent.parent.loan_ledger().expect("parent ledger");
        let after_loans = next.parent.loan_ledger().expect("spawn ledger").clone();
        let participant = next.parent.loan_participant().expect("parent participant");
        let ledger = next.parent.thread_ledger.as_ref().expect("thread ledger");
        next.parent.thread_ledger = Some(ledger.with_right(
            handle,
            CompletionRight {
                worker: Arc::new(self.worker.clone()),
                argument: self.argument,
                completion: self.completion,
            },
            before_loans,
            &after_loans,
            participant,
        ));
        (next, handle, effect)
    }
}

/// One parent path. Clones share immutable roots, just like ordinary C state;
/// a successful join consumes its entry in the successor path's registry.
#[derive(Clone)]
pub(super) struct ThreadContext {
    parent: CState,
}

impl ThreadContext {
    pub(super) fn new(mut parent: CState) -> Result<Self, CRuntimeError> {
        if parent
            .mutex_ledger
            .as_ref()
            .is_some_and(super::mutexes::MutexLedger::has_locked_guard)
        {
            return Err(CRuntimeError::UnsupportedConcurrentMutex);
        }
        match (parent.loan_ledger(), parent.loan_participant()) {
            (None, None) => {
                let ledger = LoanLedger::new();
                let participant = ledger.fresh_participant().map_err(|_| {
                    CRuntimeError::FunctionContract("invalid parent participant".to_string())
                })?;
                parent = parent
                    .with_loan_ledger(Some(ledger))
                    .with_loan_participant(Some(participant));
            }
            (Some(ledger), Some(participant)) if ledger.contains_participant(participant) => {}
            _ => {
                return Err(CRuntimeError::FunctionContract(
                    "inconsistent parent loan context".to_string(),
                ));
            }
        }
        if parent.thread_ledger.is_none() {
            parent.thread_ledger = Some(ThreadLedger::new());
        }
        Ok(Self { parent })
    }

    pub(super) fn parent(&self) -> &CState {
        &self.parent
    }

    pub(super) fn prepare_create<'a>(
        &'a self,
        worker: &'a CVerifiedFunctionRule,
        termination: Option<&CVerifiedFunctionTerminationRule>,
        argument: CValue,
        assumptions: &PureFactContext,
        environment: &CExecutionEnvironment,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Result<PreparedThreadCreate<'a>, String>> {
        if termination.is_none_or(|termination| termination.function != worker.function) {
            return Ok(Err(
                "spawn requires termination evidence for the exact worker".to_string(),
            ));
        }
        let completion = match suspend_verified_worker(
            &self.parent,
            worker,
            argument.clone(),
            assumptions,
            environment,
            budget,
        )? {
            Ok(completion) => completion,
            Err(error) => return Ok(Err(error)),
        };
        if completion.plan.caller_participant()
            != self.parent.loan_participant().expect("parent participant")
        {
            return Ok(Err(
                "worker partition belongs to a different parent".to_string()
            ));
        }
        if completion
            .plan
            .recheck_entry(self.parent.loan_ledger().expect("parent ledger"))
            .is_err()
        {
            return Ok(Err("invalid worker entry evidence".to_string()));
        }
        let retained_names = if let Some(named) = &self.parent.named_mutex_authorities {
            let target = self
                .parent
                .clone()
                .with_resource_context(completion.plan.caller_resources_after_requirements.clone());
            let updates: Vec<_> = completion
                .plan
                .mutex_uses
                .iter()
                .filter_map(|usage| usage.retained_authority_update(self.parent.resources()))
                .collect();
            match named.apply_checked_mutex_updates(&updates, &target) {
                Ok(names) => Some(Arc::new(names)),
                Err(_) => {
                    return Ok(Err(
                        "retained mutex authority cannot transport its proof name".to_string(),
                    ));
                }
            }
        } else {
            None
        };
        Ok(Ok(PreparedThreadCreate {
            parent: self,
            worker,
            argument,
            completion,
            retained_names,
        }))
    }

    pub(super) fn spawn(
        &self,
        worker: &CVerifiedFunctionRule,
        termination: Option<&CVerifiedFunctionTerminationRule>,
        argument: CValue,
        assumptions: &PureFactContext,
        environment: &CExecutionEnvironment,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Result<(Self, ThreadHandle, ExecutionPureFact), String>> {
        Ok(self
            .prepare_create(
                worker,
                termination,
                argument,
                assumptions,
                environment,
                budget,
            )?
            .map(PreparedThreadCreate::success))
    }

    pub(super) fn join(
        &self,
        handle: ThreadHandle,
        _runtime: JoinRuntimeAssumption,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<ExecutionPureFact>), &'static str> {
        let right = self
            .parent
            .thread_ledger
            .as_ref()
            .and_then(|ledger| ledger.right(handle))
            .ok_or("no live completion right for this handle")?;
        let completion = &right.completion;
        if completion
            .population_counts
            .iter()
            .any(|count| !count.can_complete(&self.parent))
        {
            return Err("worker population identity or count changed before join");
        }
        let ledger = self.parent.loan_ledger().expect("parent ledger");
        if self.parent.loan_participant() != Some(completion.plan.caller_participant()) {
            return Err("completion right belongs to a different parent");
        }
        // The worker's preserved `mutex_use` inputs are loans of the parent's
        // authority, not outputs. The sequential return strips them before
        // loan recovery restores the lent source, and join does the same;
        // otherwise the parent would hold the worker's use beside the
        // `mutex_live` or retained share that recovery returns.
        let mut outputs = completion.outputs.clone();
        for fact in completion.plan.mutex_use_requirements.values() {
            outputs = outputs
                .without_fact_delaying_normalization(fact, assumptions)
                .ok_or("worker did not return its mutex use")?;
        }
        // Compose only this worker's checked output delta into today's frame.
        // No saved parent memory, ledger, bindings or resource frame is restored.
        let resources = self
            .parent
            .resources()
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                outputs.facts().iter().cloned(),
                assumptions,
            )
            .map_err(|_| "worker outputs conflict with the current parent frame")?;
        let local_bindings = completion
            .plan
            .suspended_local_parents()
            .keys()
            .filter_map(|fact| {
                self.parent
                    .thread_ledger
                    .as_ref()?
                    .local_view_binding(fact)
                    .map(|binding| (fact.clone(), binding.clone()))
            })
            .collect();
        let recovery = completion
            .plan
            .clone()
            .recover_suspended_views(
                ledger.clone(),
                resources,
                self.parent.loan_view_bindings().clone(),
                local_bindings,
                assumptions,
            )
            .map_err(|_| "worker loans cannot be recovered in the current parent context")?;
        if recovery
            .recheck_transitions(ledger, completion.plan.caller_participant())
            .map_err(|_| "worker loan recovery evidence is invalid")?
            != recovery.terminal_ledger
        {
            return Err("worker loan recovery evidence is invalid");
        }
        let after_loans = recovery.ledger.clone();
        let mut next = self.clone();
        if let Some(creation) = &completion.creation {
            let current = self
                .parent
                .population_effects
                .creation
                .as_ref()
                .ok_or("worker join lost the parent's creation history")?;
            let mut worker_events = current.return_to(&creation.worker);
            if let Some(deferred) = &creation.deferred {
                let lent = worker_events
                    .transfer_call_fact(current, &creation.worker, &deferred.description, true)
                    .map_err(|_| "a locked worker's population authority is not in its mutex")?;
                let (changed, _) = if deferred.exclusive {
                    lent.checked_exclusive_member_exchange_quantity(
                        &deferred.block,
                        &deferred.description,
                        deferred.produce,
                        &deferred.quantity,
                        assumptions,
                    )
                } else {
                    lent.checked_member_exchange_quantity(
                        &deferred.block,
                        &deferred.description,
                        deferred.produce,
                        &deferred.quantity,
                        assumptions,
                    )
                }
                .map_err(|_| "a locked worker's member change is refused at join")?;
                worker_events = changed
                    .transfer_call_fact(&creation.worker, current, &deferred.description, true)
                    .map_err(|_| "a locked worker did not return its population authority")?;
            }
            let mut worker = self.parent.clone();
            Arc::make_mut(&mut worker.population_effects).creation = Some(worker_events);
            let mut from = self.parent.clone();
            Arc::make_mut(&mut from.population_effects).creation = Some(creation.worker.clone());
            let returned = super::functions::transfer_population_call_facts(
                worker,
                &from,
                &self.parent,
                &self
                    .parent
                    .clone()
                    .with_resource_context(recovery.resources.clone()),
                outputs.facts().iter(),
                &creation.definitions,
                assumptions,
            )
            .map_err(|_| "worker outputs cannot return through the population ledger")?;
            let finished = returned
                .population_effects
                .creation
                .as_ref()
                .expect("returned worker ledger")
                .finish_call(current)
                .map_err(|_| "worker retained population ownership at join")?;
            Arc::make_mut(&mut next.parent.population_effects).creation = Some(finished);
        }
        next.parent = next
            .parent
            .with_resource_context(recovery.resources)
            .with_loan_ledger(Some(recovery.ledger))
            .with_loan_view_bindings(recovery.view_bindings);
        if let Some(named) = &next.parent.named_mutex_authorities {
            next.parent.named_mutex_authorities = Some(Arc::new(
                named
                    .apply_checked_mutex_updates(&recovery.mutex_authority_updates, &next.parent)
                    .map_err(|_| "returned mutex authority cannot transport its proof name")?,
            ));
        }
        next.parent.thread_ledger = Some(
            next.parent
                .thread_ledger
                .as_ref()
                .expect("thread ledger")
                .without_right(
                    handle,
                    ledger,
                    &after_loans,
                    completion.plan.caller_participant(),
                    &recovery.local_view_updates,
                ),
        );
        // Publish the accumulated total only when this population is quiescent.
        // A partial join returns resources, but no current Count observation.
        // Unrelated populations remain untouched.
        for count in &completion.population_counts {
            if next
                .parent
                .thread_ledger
                .as_ref()
                .expect("thread ledger")
                .population_workers(count)
                == 0
            {
                count.complete(&mut next.parent);
            }
        }
        Ok((next, completion.facts.clone()))
    }
}

#[cfg(test)]
mod population_count_tests {
    use super::*;

    fn effect(index: u32) -> WorkerPopulationCount {
        WorkerPopulationCount {
            name: "ticket".into(),
            arguments: vec![super::super::AlgebraicValue::C(CValue::Int32(index.into()))].into(),
            before: 3.into(),
            after: 2.into(),
            overlap_safe: true,
        }
    }

    #[test]
    fn joined_count_is_once_only_and_preserves_intervening_unrelated_counts() {
        let effect = effect(0);
        let mut state = CState::new().with_counted_population(
            effect.name.clone(),
            effect.arguments.clone(),
            effect.before.clone(),
        );
        effect.reserve(&mut state);
        let mut changed = state.clone().with_counted_population(
            effect.name.clone(),
            effect.arguments.clone(),
            1.into(),
        );
        assert!(
            !effect.can_complete(&changed),
            "never overwrite a changed total"
        );
        changed = state.with_counted_population("other", vec![].into(), 17.into());
        assert!(effect.can_complete(&changed));
        effect.complete(&mut changed);
        assert_eq!(
            changed.counted_population("ticket", &effect.arguments),
            Some(&2.into())
        );
        assert_eq!(changed.counted_population("other", &[]), Some(&17.into()));
        assert!(
            !effect.can_complete(&changed),
            "completion cannot be spent twice"
        );
    }

    #[test]
    fn reserved_symbolic_total_stays_bounded_as_workers_accumulate() {
        let base = Bitvector32Term::Variable(super::super::Variable(900_008));
        for size in [8, 64, 512] {
            let (total, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut total = base.clone();
                for _ in 0..size {
                    total = consume_reserved_population(total.clone(), 1).unwrap();
                }
                total
            });
            assert_eq!(total, Bitvector32Term::subtract(base.clone(), size.into()));
            assert_eq!(work, size as usize);
        }
        assert!(
            consume_reserved_population(Bitvector32Term::subtract(base, u32::MAX.into()), 1)
                .is_none()
        );
    }

    #[test]
    fn last_join_uses_accumulated_total_not_its_own_saved_total() {
        let first = effect(0);
        let mut second = first.clone();
        second.after = 1.into();
        for last in [&first, &second] {
            let mut state = CState::new();
            first.reserve(&mut state);
            second.reserve(&mut state);
            assert!(first.can_complete(&state));
            assert!(second.can_complete(&state));
            assert_eq!(
                state.counted_population("ticket", &first.arguments),
                Some(&3.into())
            );
            last.complete(&mut state);
            assert_eq!(
                state.counted_population("ticket", &first.arguments),
                Some(&1.into())
            );
            assert!(!first.can_complete(&state));
            assert!(!second.can_complete(&state));
        }
    }

    #[test]
    fn population_worker_index_queries_ignore_unrelated_workers() {
        let mut samples = Vec::new();
        for size in [8, 64, 512] {
            let mut ledger = ThreadLedger::new();
            let storage = Arc::get_mut(&mut ledger.storage).unwrap();
            for index in 0..size {
                let effect = effect(index);
                storage.population_workers = storage
                    .population_workers
                    .with_inserted((effect.name, effect.arguments), (2, true));
            }
            let selected = effect(0);
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                assert_eq!(ledger.population_workers(&selected), 2);
                assert!(ledger.population_allows_overlap(&selected.name, &selected.arguments));
                assert!(!ledger.population_allows_overlap("absent", &selected.arguments));
            });
            samples.push(work);
        }
        assert!(
            samples[2] <= samples[0] * 4 + 8,
            "worker index scans unrelated populations: {samples:?}"
        );
    }

    #[test]
    fn pending_create_selects_population_authority_with_its_outcome() {
        let effect = effect(0);
        let failure = CState::new().with_counted_population(
            effect.name.clone(),
            effect.arguments.clone(),
            effect.before.clone(),
        );
        let mut success = failure.clone();
        effect.reserve(&mut success);
        for (selected, expected_pending) in [(&success, true), (&failure, false)] {
            let authority = PendingCreateAuthority::from_state(selected);
            let mut restored =
                failure
                    .clone()
                    .with_counted_population("unrelated", vec![].into(), 17.into());
            authority.install(&mut restored);
            assert_eq!(
                restored.counted_population("unrelated", &[]),
                Some(&17.into()),
                "selecting a create result must preserve intervening unrelated counts"
            );
            assert_eq!(effect.can_complete(&restored), expected_pending);
            assert_eq!(
                restored.counted_population("ticket", &effect.arguments),
                Some(&3.into())
            );
        }
    }

    #[test]
    fn count_observations_select_delayed_create_outcomes_without_a_c_step() {
        let effect = effect(0);
        let failure = CState::new()
            .with_counted_population(
                effect.name.clone(),
                effect.arguments.clone(),
                effect.before.clone(),
            )
            .with_observed_population_family("ticket");
        let mut success = failure.clone();
        effect.reserve(&mut success);
        let status = Bitvector32Term::Variable(super::super::Variable(900_007));
        let pending = PendingThreadCreate::new(
            status.clone(),
            Pointer {
                block: "handle".into(),
                offset: super::super::PointerOffsetTerm::Constant(0),
            },
            ThreadHandle(700).c_value(),
            &success,
            &failure,
        );
        let mut visible = failure.clone();
        visible.pending_thread_create = Some(pending);
        let zero = ConditionTerm::Bitvector32Equal(Box::new(status), Box::new(0.into()));
        let arguments = effect
            .arguments
            .iter()
            .cloned()
            .map(Some)
            .collect::<Vec<_>>();
        for snapshot in [visible.clone(), visible.resource_state_snapshot()] {
            assert_eq!(
                snapshot.counted_population_sum("ticket", &arguments, &PureFactContext::new()),
                None
            );
            assert_eq!(
                snapshot.counted_population_sum(
                    "ticket",
                    &arguments,
                    &PureFactContext::new().assume_condition(zero.clone(), true)
                ),
                None
            );
            assert_eq!(
                snapshot.counted_population_sum(
                    "ticket",
                    &arguments,
                    &PureFactContext::new().assume_condition(zero.clone(), false)
                ),
                Some(3.into())
            );
        }
    }

    #[test]
    fn completing_one_population_does_not_scan_other_reservations() {
        let mut samples = Vec::new();
        for size in [8, 64, 512] {
            let mut state = CState::new();
            for index in 0..size {
                effect(index).reserve(&mut state);
            }
            let selected = effect(0);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(selected.can_complete(&state));
                selected.complete(&mut state);
            });
            assert!(effect(size - 1).can_complete(&state));
            samples.push(work);
        }
        assert!(samples[0] > 0);
        assert!(
            samples[2] <= samples[0] * 2,
            "population completion must stay local: {samples:?}"
        );
    }
}
