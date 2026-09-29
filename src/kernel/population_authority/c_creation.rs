//! Provenance of C storage created by the executing proof environment.
//!
//! This optional event ledger binds abstract population authority to checked
//! C storage creation. It grants no C memory permission, and assumed
//! allocation claims never enter it.

use super::{Anchor, AuthorityState, Holder, Refusal};
use crate::kernel::{
    AlgebraicValue, Bitvector32Term, CCompositeResourceDefinition, CResource, CResourceFact,
    CState, CValue, PointerBlock, PointerOffsetTerm, PureFactContext, ResourceDescription,
};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("C population creation identity exhausted")
}

fn same_quantity(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || crate::kernel::quantity_condition_holds(
            assumptions,
            crate::kernel::ConditionTerm::Bitvector32Equal(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ),
        )
}

struct Root {
    identity: u64,
    /// Stable rechecking of the same function-entry transition. Authority-mode C
    /// calls remain closed until each occurrence has its own identity.
    entry_call: OnceLock<CreationEvents>,
    proof_entry: OnceLock<CreationEvents>,
    /// Rechecking a transfer or return uses the same successor identity.
    /// Keys contain only small holder/population IDs, never resource trees.
    transfers:
        Mutex<BTreeMap<(Holder, Holder, super::Population, bool, Bitvector32Term), CreationEvents>>,
    returns: Mutex<BTreeMap<u64, CreationEvents>>,
    c_events: Mutex<BTreeMap<CEvent, CreationEvents>>,
    invocation: Holder,
    pending: PersistentMap<PointerBlock, Holder>,
    creators: PersistentMap<PointerBlock, Holder>,
    anchors: PersistentMap<PointerBlock, Anchor>,
    authority: AuthorityState,
    /// One symbolic member batch per live population, with its owning holder.
    symbolic_batches: PersistentMap<super::Population, SymbolicBatch>,
    symbolic_holders: PersistentMap<Holder, u32>,
    /// Per-storage family history; never inferred from the current owner.
    tainted: PersistentMap<PointerBlock, PersistentSet<String>>,
    /// A standalone helper may assume exactly one declared population input.
    /// It carries no creator right, storage event, or asserted total.
    opaque_import: Option<OpaqueImport>,
}

#[derive(Clone)]
struct SymbolicBatch {
    owner: Holder,
    quantity: Bitvector32Term,
}

#[derive(Clone)]
struct OpaqueImport {
    description: ResourceDescription,
    entry_owned_members: u32,
    owned_members: u32,
    /// Symbolic cardinality is admitted only through a checked control wrapper.
    entry_symbolic_members: Option<Bitvector32Term>,
    symbolic_delta: Option<(bool, Bitvector32Term)>,
    /// Only a checked control wrapper can supply this immutable entry load.
    entry_count: Option<Bitvector32Term>,
    retired_authority: bool,
}

pub(in crate::kernel) struct SymbolicPopulationCount {
    pub entry_count: Bitvector32Term,
    pub delta: i8,
    pub entry_owned_members: u32,
    pub entry_symbolic_members: Option<Bitvector32Term>,
    pub symbolic_delta: Option<(bool, Bitvector32Term)>,
}

/// Inputs of a checked C lifetime event. Each key is proportional to the
/// pointer or family named by that one operation.
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum CEvent {
    Pending(PointerBlock),
    Resolve(PointerBlock, Option<PointerBlock>),
    Created(PointerBlock),
    MemberCreated(PointerBlock, String),
    Retired(PointerBlock),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum CreationRefusal {
    NotCreationEnvironment,
    MembersAlreadyExisted,
    AlreadyEstablished,
    MissingAuthority,
    MissingMembers,
    InvalidMember,
    InvalidQuantity,
    OutstandingMembers,
    OutstandingAuthority,
    OutstandingOwnership,
    UnknownTotal,
    OpaqueImportConflict,
}

impl From<Refusal> for CreationRefusal {
    fn from(value: Refusal) -> Self {
        match value {
            Refusal::AlreadyEstablished => Self::AlreadyEstablished,
            Refusal::OutstandingMembers => Self::OutstandingMembers,
            Refusal::OutstandingAuthority => Self::OutstandingAuthority,
            Refusal::MissingAuthority | Refusal::UnknownPopulation => Self::MissingAuthority,
            Refusal::MissingMembers => Self::MissingMembers,
            Refusal::InvalidQuantity => Self::InvalidQuantity,
            Refusal::OutstandingOwnership => Self::OutstandingOwnership,
            _ => Self::NotCreationEnvironment,
        }
    }
}

/// Opaque evidence issued only by a checked transition that minted the
/// resulting abstract population identity. Certificate checking compares exact state roots;
/// it never tries to allocate the same identity a second time.
#[derive(Clone, Debug)]
pub(crate) struct CheckedPopulationAuthorityExchange {
    before: u64,
    after: u64,
    description: ResourceDescription,
    establish: bool,
}

/// Evidence for one member entering or leaving a registered population.
/// The proof checker must also check the corresponding resource exchange.
#[derive(Clone, Debug)]
pub(crate) struct CheckedPopulationMemberExchange {
    before: u64,
    after: u64,
    description: ResourceDescription,
    produce: bool,
}

impl CheckedPopulationMemberExchange {
    pub(in crate::kernel) fn matches(
        &self,
        before: &CreationEvents,
        after: &CreationEvents,
        description: &ResourceDescription,
        produce: bool,
    ) -> bool {
        self.before == before.0.identity
            && self.after == after.0.identity
            && &self.description == description
            && self.produce == produce
    }
}

impl CheckedPopulationAuthorityExchange {
    pub(in crate::kernel) fn matches(
        &self,
        before: &CreationEvents,
        after: &CreationEvents,
        description: &ResourceDescription,
        establish: bool,
    ) -> bool {
        self.before == before.0.identity
            && self.after == after.0.identity
            && &self.description == description
            && self.establish == establish
    }
}

/// Exact storage-block creation evidence. Copies of a proof path share a root;
/// each transition makes one new root, so state comparison never scans events.
#[derive(Clone)]
pub(in crate::kernel) struct CreationEvents(Arc<Root>);

impl std::fmt::Debug for CreationEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CreationEvents")
            .field("identity", &self.0.identity)
            .field("invocation", &self.0.invocation)
            .field("pending_count", &self.0.pending.len())
            .field("event_count", &self.0.creators.len())
            .field("anchor_count", &self.0.anchors.len())
            .field("tainted_blocks", &self.0.tainted.len())
            .finish()
    }
}

impl PartialEq for CreationEvents {
    fn eq(&self, other: &Self) -> bool {
        self.0.identity == other.0.identity
    }
}
impl Eq for CreationEvents {}
impl PartialOrd for CreationEvents {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CreationEvents {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.identity.cmp(&other.0.identity)
    }
}
impl Hash for CreationEvents {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.identity.hash(state);
    }
}

impl CreationEvents {
    fn memoized_c_event(&self, key: CEvent, create: impl FnOnce() -> Self) -> Self {
        if let Some(existing) = self.0.c_events.lock().expect("C event cache").get(&key) {
            return existing.clone();
        }
        let next = create();
        self.0
            .c_events
            .lock()
            .expect("C event cache")
            .entry(key)
            .or_insert(next)
            .clone()
    }

    /// Standalone helper entry may assume one already existing population
    /// named by an exact external-argument pointer. This records only the
    /// contract's input custody; it cannot create storage or assert a total.
    pub(in crate::kernel) fn import_opaque_contract_population(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
    ) -> Result<Self, CreationRefusal> {
        self.import_opaque_contract_population_inner(description, owned_members, None, None)
    }

    /// Import a folded control only after independently checking its exact
    /// owned cell, contained authority, and `cell == count(family)` body fact.
    /// The entry cell load is then a sound witness for this one population's
    /// arbitrary initial total. Direct authority imports never receive one.
    pub(in crate::kernel) fn import_checked_control_wrapper(
        &self,
        state: &CState,
        selected: &CResourceFact,
        definition: &CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        if state.population_effects.creation.as_ref() != Some(self) {
            return Err("control import requires the current creation ledger".into());
        }
        let (description, entry_count) =
            state.checked_authority_wrapper_import_components(selected, definition, assumptions)?;
        let member = CResource::Composite {
            name: description.family().to_owned(),
            arguments: description.arguments().to_vec().into(),
        };
        let owned = state
            .resources()
            .exact_resource_facts(&member)
            .into_iter()
            .filter_map(|fact| fact.owned_quantity_term().cloned())
            .collect::<Vec<_>>();
        let (owned_members, symbolic_members) = match owned.as_slice() {
            [] => (0, None),
            [quantity] if quantity.as_const() == Some(1) => (1, None),
            [quantity] => (0, Some(quantity.clone())),
            _ => return Err("control import needs one owned member quantity".into()),
        };
        self.import_opaque_contract_population_inner(
            &description,
            owned_members,
            Some(entry_count),
            symbolic_members,
        )
        .map_err(|refusal| format!("control import refused: {refusal:?}"))
    }

    fn import_opaque_contract_population_inner(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
        entry_count: Option<Bitvector32Term>,
        symbolic_members: Option<Bitvector32Term>,
    ) -> Result<Self, CreationRefusal> {
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if pointer.pointer().block != PointerBlock::ExternalArgument
            || !description.schema().is_countable()
            || !description.resource_arguments().is_empty()
            || owned_members > 1
        {
            return Err(CreationRefusal::InvalidMember);
        }
        if let Some(existing) = &self.0.opaque_import {
            if existing.description == *description
                && existing.owned_members == owned_members
                && existing.entry_count == entry_count
                && existing.entry_symbolic_members == symbolic_members
            {
                return Ok(self.clone());
            }
            return Err(CreationRefusal::OpaqueImportConflict);
        }
        if !self.0.creators.is_empty() || !self.0.anchors.is_empty() {
            return Err(CreationRefusal::NotCreationEnvironment);
        }
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: Some(OpaqueImport {
                description: description.clone(),
                entry_owned_members: owned_members,
                owned_members,
                entry_symbolic_members: symbolic_members,
                symbolic_delta: None,
                entry_count,
                retired_authority: false,
            }),
        })))
    }

    pub(in crate::kernel) fn owns_population_authority(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        if self
            .0
            .opaque_import
            .as_ref()
            .is_some_and(|import| import.description == *description && !import.retired_authority)
        {
            return true;
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.pointer().block, description) else {
            return false;
        };
        self.0
            .anchors
            .get(block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some_and(|population| {
                self.0
                    .authority
                    .holder_owns_authority(self.0.invocation, population)
            })
    }

    pub(in crate::kernel) fn owns_population_member(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        if self.owns_imported_population_member(description) {
            return true;
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.pointer().block, description) else {
            return false;
        };
        self.0
            .anchors
            .get(block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some_and(|population| {
                self.0
                    .authority
                    .holder_owns_member(self.0.invocation, population)
                    || self
                        .0
                        .symbolic_batches
                        .get(&population)
                        .is_some_and(|batch| batch.owner == self.0.invocation)
            })
    }

    pub(in crate::kernel) fn owns_imported_population_member(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        self.0.opaque_import.as_ref().is_some_and(|import| {
            import.description == *description
                && (import.owned_members == 1
                    || import
                        .symbolic_delta
                        .as_ref()
                        .map_or(import.entry_symbolic_members.is_some(), |(produce, _)| {
                            *produce
                        }))
        })
    }

    /// Exact signed batch delta from a checked control import. The quantity may
    /// be zero; the direction remains part of the checked transition.
    pub(in crate::kernel) fn imported_member_delta_since_entry(
        &self,
        description: &ResourceDescription,
    ) -> Option<(bool, Bitvector32Term)> {
        let import = self.0.opaque_import.as_ref()?;
        if import.description != *description || import.retired_authority {
            return None;
        }
        import.symbolic_delta.clone().or_else(|| {
            match (import.entry_owned_members, import.owned_members) {
                (0, 1) => Some((true, Bitvector32Term::Constant(1))),
                (1, 0) => Some((false, Bitvector32Term::Constant(1))),
                _ => None,
            }
        })
    }

    pub(in crate::kernel) fn spent_imported_member_since(&self, before: &Self) -> bool {
        match (&before.0.opaque_import, &self.0.opaque_import) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && start.owned_members == 1
                    && end.owned_members == 0
                    && before.0.invocation == self.0.invocation
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn born_imported_member_since(&self, before: &Self) -> bool {
        match (&before.0.opaque_import, &self.0.opaque_import) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && start.owned_members == 0
                    && end.owned_members == 1
                    && before.0.invocation == self.0.invocation
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn retired_imported_authority_since(&self, before: &Self) -> bool {
        match (&before.0.opaque_import, &self.0.opaque_import) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && !start.retired_authority
                    && end.retired_authority
                    && end.owned_members == 0
                    && before.0.invocation == self.0.invocation
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn recognizes_imported_population(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        self.0
            .opaque_import
            .as_ref()
            .is_some_and(|import| import.description == *description)
    }

    pub(in crate::kernel) fn recognizes_population_authority(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        self.0
            .opaque_import
            .as_ref()
            .is_some_and(|import| import.description == *description)
            || self.tracks_population(description)
    }

    pub(in crate::kernel) fn has_opaque_import(&self) -> bool {
        self.0.opaque_import.is_some()
    }

    /// The description includes the exact pointer; another family or offset
    /// cannot observe this imported count.
    pub(in crate::kernel) fn observe_symbolic(
        &self,
        description: &ResourceDescription,
    ) -> Option<SymbolicPopulationCount> {
        let import = self.0.opaque_import.as_ref()?;
        if import.description != *description || import.retired_authority {
            return None;
        }
        Some(SymbolicPopulationCount {
            entry_count: import.entry_count.clone()?,
            delta: import.owned_members as i8 - import.entry_owned_members as i8,
            entry_owned_members: import.entry_owned_members,
            entry_symbolic_members: import.entry_symbolic_members.clone(),
            symbolic_delta: import.symbolic_delta.clone(),
        })
    }

    fn exact_member_block<'a>(
        &self,
        block: &'a PointerBlock,
        description: &ResourceDescription,
    ) -> Result<&'a PointerBlock, CreationRefusal> {
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if !description.schema().is_countable()
            || !description.resource_arguments().is_empty()
            || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
            || &pointer.pointer().block != block
        {
            return Err(CreationRefusal::InvalidMember);
        }
        Ok(block)
    }

    /// Read the total only while this proof environment holds the authority.
    pub(in crate::kernel) fn observe(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<u32, CreationRefusal> {
        if *block == PointerBlock::ExternalArgument
            && self
                .0
                .opaque_import
                .as_ref()
                .is_some_and(|import| import.description.family() == family)
        {
            return Err(CreationRefusal::UnknownTotal);
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        self.0
            .authority
            .observe(self.0.invocation, population)
            .map_err(CreationRefusal::from)
    }

    /// Observe the exact concrete-anchor total, including one outstanding
    /// symbolic batch, only while this holder owns population authority.
    pub(in crate::kernel) fn observe_term(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Bitvector32Term, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let base = self
            .0
            .authority
            .observe(self.0.invocation, population)
            .map_err(CreationRefusal::from)?;
        let base = Bitvector32Term::Constant(base);
        Ok(match self.0.symbolic_batches.get(&population) {
            Some(batch) => Bitvector32Term::add(base, batch.quantity.clone()),
            None => base,
        })
    }

    pub(in crate::kernel) fn observed_symbolic_batch(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Option<(u32, Bitvector32Term)> {
        let anchor = *self.0.anchors.get(block)?;
        let population = self.0.authority.population_at(anchor, family)?;
        let base = self
            .0
            .authority
            .observe(self.0.invocation, population)
            .ok()?;
        let batch = self.0.symbolic_batches.get(&population)?;
        Some((base, batch.quantity.clone()))
    }

    /// Exchange a checked quantity of one resource family. Symbolic batches are
    /// admitted for opaque helper proofs only; a concrete anchor still uses the
    /// exact cardinality engine below.
    pub(in crate::kernel) fn checked_member_exchange_quantity(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        if quantity.as_const() == Some(1) {
            return self.checked_member_exchange(block, description, produce);
        }
        if !crate::kernel::quantity_condition_holds(
            assumptions,
            crate::kernel::ConditionTerm::signed_greater_equal(
                quantity.clone(),
                Bitvector32Term::Constant(0),
            ),
        ) {
            return Err(CreationRefusal::InvalidQuantity);
        }
        if self.0.opaque_import.is_none() {
            self.exact_member_block(block, description)?;
            let anchor = *self
                .0
                .anchors
                .get(block)
                .ok_or(CreationRefusal::MissingAuthority)?;
            let population = self
                .0
                .authority
                .population_at(anchor, description.family())
                .ok_or(CreationRefusal::MissingAuthority)?;
            if !self
                .0
                .authority
                .holder_owns_authority(self.0.invocation, population)
            {
                return Err(CreationRefusal::MissingAuthority);
            }
            let mut batches = self.0.symbolic_batches.clone();
            let mut holders = self.0.symbolic_holders.clone();
            if produce {
                if batches.contains_key(&population) {
                    return Err(CreationRefusal::OutstandingMembers);
                }
                let base = self
                    .0
                    .authority
                    .observe(self.0.invocation, population)
                    .map_err(CreationRefusal::from)?;
                let maximum = Bitvector32Term::Constant(i32::MAX as u32 - base);
                if !crate::kernel::quantity_condition_holds(
                    assumptions,
                    crate::kernel::ConditionTerm::signed_greater_equal(maximum, quantity.clone()),
                ) {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                batches.insert(
                    population,
                    SymbolicBatch {
                        owner: self.0.invocation,
                        quantity: quantity.clone(),
                    },
                );
                let held = holders.get(&self.0.invocation).copied().unwrap_or(0);
                holders.insert(
                    self.0.invocation,
                    held.checked_add(1)
                        .ok_or(CreationRefusal::InvalidQuantity)?,
                );
            } else {
                let batch = batches
                    .get(&population)
                    .ok_or(CreationRefusal::MissingMembers)?;
                if batch.owner != self.0.invocation
                    || !same_quantity(&batch.quantity, quantity, assumptions)
                {
                    return Err(CreationRefusal::MissingMembers);
                }
                batches.remove(&population);
                let held = holders.get(&self.0.invocation).copied().unwrap_or(0);
                if held <= 1 {
                    holders.remove(&self.0.invocation);
                } else {
                    holders.insert(self.0.invocation, held - 1);
                }
            }
            let mut tainted = self.0.tainted.clone();
            if produce {
                let families = tainted
                    .get(block)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(description.family().to_owned());
                tainted.insert(block.clone(), families);
            }
            let after = Self(Arc::new(Root {
                identity: fresh_identity(),
                entry_call: OnceLock::new(),
                proof_entry: OnceLock::new(),
                transfers: Mutex::new(BTreeMap::new()),
                returns: Mutex::new(BTreeMap::new()),
                c_events: Mutex::new(BTreeMap::new()),
                invocation: self.0.invocation,
                pending: self.0.pending.clone(),
                creators: self.0.creators.clone(),
                anchors: self.0.anchors.clone(),
                authority: self.0.authority.clone(),
                symbolic_batches: batches,
                symbolic_holders: holders,
                tainted,
                opaque_import: None,
            }));
            let evidence = CheckedPopulationMemberExchange {
                before: self.0.identity,
                after: after.0.identity,
                description: description.clone(),
                produce,
            };
            return Ok((after, evidence));
        }
        let import = self
            .0
            .opaque_import
            .as_ref()
            .filter(|import| import.description == *description && import.entry_count.is_some())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if import.retired_authority || import.symbolic_delta.is_some() {
            return Err(CreationRefusal::InvalidQuantity);
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if &pointer.pointer().block != block {
            return Err(CreationRefusal::InvalidMember);
        }
        if produce {
            if import.owned_members != 0 || import.entry_symbolic_members.is_some() {
                return Err(CreationRefusal::MissingMembers);
            }
        } else if import.entry_symbolic_members.as_ref() != Some(quantity) {
            return Err(CreationRefusal::MissingMembers);
        }
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: Some(OpaqueImport {
                symbolic_delta: Some((produce, quantity.clone())),
                ..import.clone()
            }),
        }));
        let evidence = CheckedPopulationMemberExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            produce,
        };
        Ok((after, evidence))
    }

    /// Change exactly one member. The caller supplies a checked resource type;
    /// this method independently rejects fields, references and non-base anchors.
    pub(in crate::kernel) fn checked_member_exchange(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        if let Some(import) = self
            .0
            .opaque_import
            .as_ref()
            .filter(|import| import.description == *description)
        {
            // An opaque helper has one checked member exchange. Mixing a
            // unit transition with an imported symbolic batch would lose one
            // of the deltas from its population count.
            if import.entry_symbolic_members.is_some() || import.symbolic_delta.is_some() {
                return Err(CreationRefusal::InvalidQuantity);
            }
            // This ledger is proof-local. A birth is transferred only at a
            // verified call whose concrete authority still has a live anchor.
            let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
                return Err(CreationRefusal::InvalidMember);
            };
            if &pointer.pointer().block != block {
                return Err(CreationRefusal::InvalidMember);
            }
            if import.owned_members != u32::from(!produce) {
                return Err(CreationRefusal::MissingMembers);
            }
            if import.retired_authority {
                return Err(CreationRefusal::MissingAuthority);
            }
            let after = Self(Arc::new(Root {
                identity: fresh_identity(),
                entry_call: OnceLock::new(),
                proof_entry: OnceLock::new(),
                transfers: Mutex::new(BTreeMap::new()),
                returns: Mutex::new(BTreeMap::new()),
                c_events: Mutex::new(BTreeMap::new()),
                invocation: self.0.invocation,
                pending: self.0.pending.clone(),
                creators: self.0.creators.clone(),
                anchors: self.0.anchors.clone(),
                authority: self.0.authority.clone(),
                symbolic_batches: self.0.symbolic_batches.clone(),
                symbolic_holders: self.0.symbolic_holders.clone(),
                tainted: self.0.tainted.clone(),
                opaque_import: Some(OpaqueImport {
                    description: description.clone(),
                    entry_owned_members: import.entry_owned_members,
                    owned_members: u32::from(produce),
                    entry_symbolic_members: import.entry_symbolic_members.clone(),
                    symbolic_delta: None,
                    entry_count: import.entry_count.clone(),
                    retired_authority: false,
                }),
            }));
            let evidence = CheckedPopulationMemberExchange {
                before: self.0.identity,
                after: after.0.identity,
                description: description.clone(),
                produce,
            };
            return Ok((after, evidence));
        }
        self.exact_member_block(block, description)?;
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, description.family())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if self.0.symbolic_batches.contains_key(&population) {
            return Err(CreationRefusal::InvalidQuantity);
        }
        let authority = if produce {
            self.0.authority.produce(self.0.invocation, population, 1)
        } else {
            self.0.authority.consume(self.0.invocation, population, 1)
        }
        .map_err(CreationRefusal::from)?;
        let mut tainted = self.0.tainted.clone();
        if produce {
            let families = tainted
                .get(block)
                .cloned()
                .unwrap_or_default()
                .with_value(description.family().to_owned());
            tainted.insert(block.clone(), families);
        }
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_import: self.0.opaque_import.clone(),
        }));
        let evidence = CheckedPopulationMemberExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            produce,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn new() -> Self {
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: Holder::fresh(),
            pending: PersistentMap::default(),
            creators: PersistentMap::default(),
            anchors: PersistentMap::default(),
            authority: AuthorityState::default(),
            symbolic_batches: PersistentMap::default(),
            symbolic_holders: PersistentMap::default(),
            tainted: PersistentMap::default(),
            opaque_import: None,
        }))
    }

    /// A call carries known storage origins but runs in a distinct creator
    /// environment. The caller's current creation rights do not follow it.
    /// Rechecking one entry must recover exactly the same child identity.
    /// Distinct C call occurrences need their own event key before calls are
    /// enabled in authority mode.
    pub(in crate::kernel) fn enter_call(&self) -> Self {
        self.0
            .entry_call
            .get_or_init(|| {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    proof_entry: OnceLock::new(),
                    transfers: Mutex::new(BTreeMap::new()),
                    returns: Mutex::new(BTreeMap::new()),
                    c_events: Mutex::new(BTreeMap::new()),
                    invocation: Holder::fresh(),
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority: self.0.authority.clone(),
                    symbolic_batches: self.0.symbolic_batches.clone(),
                    symbolic_holders: self.0.symbolic_holders.clone(),
                    tainted: self.0.tainted.clone(),
                    opaque_import: None,
                }))
            })
            .clone()
    }

    /// Rebind a standalone proof's declared input to its checked function
    /// entry. Unlike an ordinary nested call, this retains the one opaque
    /// assumption that the proof entry itself is required to establish.
    pub(in crate::kernel) fn enter_proof_entry(&self) -> Self {
        self.0
            .proof_entry
            .get_or_init(|| {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    proof_entry: OnceLock::new(),
                    transfers: Mutex::new(BTreeMap::new()),
                    returns: Mutex::new(BTreeMap::new()),
                    c_events: Mutex::new(BTreeMap::new()),
                    invocation: Holder::fresh(),
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority: self.0.authority.clone(),
                    symbolic_batches: self.0.symbolic_batches.clone(),
                    symbolic_holders: self.0.symbolic_holders.clone(),
                    tainted: self.0.tainted.clone(),
                    opaque_import: self.0.opaque_import.clone(),
                }))
            })
            .clone()
    }

    /// Move one exact owned contract fact between invocation holders. The
    /// visible resource planner must perform the matching owned exchange;
    /// this ledger operation changes neither the population total nor C memory.
    pub(in crate::kernel) fn transfer_call_fact(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        authority_fact: bool,
    ) -> Result<Self, CreationRefusal> {
        self.transfer_call_fact_quantity(
            from,
            to,
            description,
            authority_fact,
            &Bitvector32Term::Constant(1),
            &PureFactContext::new(),
        )
    }

    pub(in crate::kernel) fn transfer_call_fact_quantity(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        authority_fact: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<Self, CreationRefusal> {
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        let block = self.exact_member_block(&pointer.pointer().block, description)?;
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, description.family())
            .ok_or(CreationRefusal::MissingAuthority)?;
        let key = (
            from.0.invocation,
            to.0.invocation,
            population,
            authority_fact,
            quantity.clone(),
        );
        if let Some(cached) = self.0.transfers.lock().expect("transfer cache").get(&key) {
            return Ok(cached.clone());
        }
        let mut batches = self.0.symbolic_batches.clone();
        let mut holders = self.0.symbolic_holders.clone();
        let authority = if authority_fact {
            if quantity.as_const() != Some(1) {
                return Err(CreationRefusal::InvalidQuantity);
            }
            self.0
                .authority
                .transfer_authority(from.0.invocation, to.0.invocation, population)
                .map_err(CreationRefusal::from)?
        } else if let Some(batch) = batches.get(&population).cloned() {
            if batch.owner != from.0.invocation
                || !same_quantity(&batch.quantity, quantity, assumptions)
            {
                return Err(CreationRefusal::MissingMembers);
            }
            if from.0.invocation != to.0.invocation {
                batches.insert(
                    population,
                    SymbolicBatch {
                        owner: to.0.invocation,
                        quantity: batch.quantity,
                    },
                );
                let prior = holders.get(&from.0.invocation).copied().unwrap_or(0);
                if prior <= 1 {
                    holders.remove(&from.0.invocation);
                } else {
                    holders.insert(from.0.invocation, prior - 1);
                }
                let received = holders.get(&to.0.invocation).copied().unwrap_or(0);
                holders.insert(
                    to.0.invocation,
                    received
                        .checked_add(1)
                        .ok_or(CreationRefusal::InvalidQuantity)?,
                );
            }
            self.0.authority.clone()
        } else if let Some(exact) = quantity
            .as_const()
            .filter(|q| *q > 0 && *q <= i32::MAX as u32)
        {
            self.0
                .authority
                .transfer_members(from.0.invocation, to.0.invocation, population, exact)
                .map_err(CreationRefusal::from)?
        } else {
            return Err(CreationRefusal::MissingMembers);
        };
        let successor = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: batches,
            symbolic_holders: holders,
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        }));
        Ok(self
            .0
            .transfers
            .lock()
            .expect("transfer cache")
            .entry(key)
            .or_insert(successor)
            .clone())
    }

    /// Move the C storage cleanup obligation with a consumed or borrowed
    /// control whose checked body contains the allocation. The ordinary
    /// resource transfer separately moves that exact allocation fact.
    pub(in crate::kernel) fn transfer_call_anchor(
        &self,
        from: &Self,
        to: &Self,
        block: &PointerBlock,
    ) -> Result<Self, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let authority = self
            .0
            .authority
            .transfer_anchor(from.0.invocation, to.0.invocation, anchor)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        })))
    }

    pub(in crate::kernel) fn tracks_population(&self, description: &ResourceDescription) -> bool {
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        self.0
            .anchors
            .get(&pointer.pointer().block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some()
    }

    /// A helper can finish only after returning or consuming all abstract
    /// ownership it received. In particular it cannot strand a member while
    /// returning the authority, or retain a creator anchor from local storage.
    pub(in crate::kernel) fn finish_call(&self, caller: &Self) -> Result<Self, CreationRefusal> {
        if self.0.symbolic_holders.contains_key(&self.0.invocation) {
            return Err(CreationRefusal::OutstandingOwnership);
        }
        self.0
            .authority
            .finish_holder(self.0.invocation)
            .map_err(CreationRefusal::from)?;
        Ok(self.return_to(caller))
    }

    /// Return keeps creation events from the callee but restores the caller's
    /// environment. A callee-created object cannot be established by caller.
    pub(in crate::kernel) fn return_to(&self, caller: &Self) -> Self {
        if let Some(cached) = self
            .0
            .returns
            .lock()
            .expect("return cache")
            .get(&caller.0.identity)
        {
            return cached.clone();
        }
        let successor = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: caller.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: caller.0.opaque_import.clone(),
        }));
        self.0
            .returns
            .lock()
            .expect("return cache")
            .entry(caller.0.identity)
            .or_insert(successor)
            .clone()
    }

    /// The C `malloc`/`calloc` statement owns an unresolved result. Record
    /// its creator before another function can test the pointer and resolve
    /// the outcome. This is not yet a live-storage creation grant.
    pub(in crate::kernel) fn pending_creation(&self, block: PointerBlock) -> Self {
        self.memoized_c_event(CEvent::Pending(block.clone()), || {
            self.pending_creation_uncached(block)
        })
    }

    fn pending_creation_uncached(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(&block, PointerBlock::Symbolic(_)));
        assert!(
            !self.0.pending.contains_key(&block),
            "pending allocation reused"
        );
        let mut pending = self.0.pending.clone();
        pending.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending,
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        }))
    }

    /// Resolve an actual pending allocation. Failure discards its origin;
    /// success attaches the original creator to the trusted Heap block even
    /// when a helper made the deciding branch.
    pub(in crate::kernel) fn resolve_pending(
        &self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
    ) -> Self {
        self.memoized_c_event(
            CEvent::Resolve(pending_block.clone(), live_block.clone()),
            || self.resolve_pending_uncached(pending_block, live_block),
        )
    }

    fn resolve_pending_uncached(
        &self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
    ) -> Self {
        let Some(creator) = self.0.pending.get(pending_block).copied() else {
            return self.clone();
        };
        let mut pending = self.0.pending.clone();
        pending.remove(pending_block);
        let mut creators = self.0.creators.clone();
        let mut anchors = self.0.anchors.clone();
        let mut authority = self.0.authority.clone();
        let mut tainted = self.0.tainted.without_key(pending_block);
        if let Some(block) = live_block {
            debug_assert!(matches!(&block, PointerBlock::Heap(_)));
            assert!(
                !creators.contains_key(&block),
                "storage lifetime created twice"
            );
            if let Some(families) = self.0.tainted.get(pending_block) {
                tainted.insert(block.clone(), families.clone());
            }
            let (next, anchor) = authority.allocate_anchor(creator);
            authority = next;
            anchors.insert(block.clone(), anchor);
            creators.insert(block, creator);
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending,
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_import: self.0.opaque_import.clone(),
        }))
    }

    /// Called only at checked C storage creation, never at resource lowering,
    /// contract allocation import, or generic memory-block construction.
    pub(in crate::kernel) fn created(&self, block: PointerBlock) -> Self {
        self.memoized_c_event(CEvent::Created(block.clone()), || {
            self.created_uncached(block)
        })
    }

    fn created_uncached(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(block, PointerBlock::Heap(_)) || block.starts_with("local:"));
        let mut creators = self.0.creators.clone();
        assert!(
            !creators.contains_key(&block),
            "storage lifetime created twice"
        );
        let (authority, anchor) = self.0.authority.allocate_anchor(self.0.invocation);
        let mut anchors = self.0.anchors.clone();
        anchors.insert(block.clone(), anchor);
        creators.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        }))
    }

    pub(in crate::kernel) fn created_here(&self, block: &PointerBlock) -> bool {
        self.0.creators.get(block).copied() == Some(self.0.invocation)
    }

    pub(in crate::kernel) fn retirement_refusal(
        &self,
        block: &PointerBlock,
    ) -> Option<CreationRefusal> {
        let anchor = *self.0.anchors.get(block)?;
        self.0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .err()
            .map(CreationRefusal::from)
    }

    /// Once a member existed, absence from the local resource context is no
    /// evidence of an empty population: it may have been transferred away.
    /// This mark follows the storage lifetime across helper calls.
    pub(in crate::kernel) fn member_created(&self, block: &PointerBlock, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        self.memoized_c_event(
            CEvent::MemberCreated(block.clone(), family.to_owned()),
            || self.member_created_uncached(block, family),
        )
    }

    fn member_created_uncached(&self, block: &PointerBlock, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        let mut tainted = self.0.tainted.clone();
        let families = tainted
            .get(block)
            .cloned()
            .unwrap_or_default()
            .with_value(family.to_owned());
        tainted.insert(block.clone(), families);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_import: self.0.opaque_import.clone(),
        }))
    }

    /// A checked source fold may establish only at its own creation event,
    /// before any member of this family has existed in the storage lifetime.
    pub(in crate::kernel) fn establish(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        if !self.created_here(block) {
            return Err(CreationRefusal::NotCreationEnvironment);
        }
        if self
            .0
            .tainted
            .get(block)
            .is_some_and(|families| families.contains(&family.to_owned()))
        {
            return Err(CreationRefusal::MembersAlreadyExisted);
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let (authority, _) = self
            .0
            .authority
            .establish(self.0.invocation, anchor, family)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        })))
    }

    pub(in crate::kernel) fn checked_establish(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let after = self.establish(block, description.family())?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: true,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn checked_retire(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let after = self.retire_authority(block, description.family())?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: false,
        };
        Ok((after, evidence))
    }

    /// A standalone proof can retire the imported authority only after its
    /// last imported member is spent. The caller has separately proved the
    /// entry count was one through the checked control-cell invariant.
    pub(in crate::kernel) fn checked_retire_imported(
        &self,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let import = self
            .0
            .opaque_import
            .as_ref()
            .filter(|import| import.description == *description)
            .ok_or(CreationRefusal::MissingAuthority)?;
        if import.retired_authority || import.entry_owned_members != 1 || import.owned_members != 0
        {
            return Err(CreationRefusal::OutstandingMembers);
        }
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: Some(OpaqueImport {
                retired_authority: true,
                ..import.clone()
            }),
        }));
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: false,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn retire_authority(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        if self.0.symbolic_batches.contains_key(&population) {
            return Err(CreationRefusal::OutstandingMembers);
        }
        let authority = self
            .0
            .authority
            .retire(self.0.invocation, population)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_import: self.0.opaque_import.clone(),
        })))
    }

    /// End of an automatic or heap lifetime removes its provenance. Future
    /// reuse at the same address needs an independently checked creation.
    pub(in crate::kernel) fn retired(&self, block: &PointerBlock) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        if let Some(refusal) = self.retirement_refusal(block) {
            return Err(refusal);
        }
        Ok(self.memoized_c_event(CEvent::Retired(block.clone()), || {
            self.retired_uncached(block)
                .expect("retirement was checked before memoizing")
        }))
    }

    fn retired_uncached(&self, block: &PointerBlock) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let authority = self
            .0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .map_err(CreationRefusal::from)?;
        let mut creators = self.0.creators.clone();
        creators.remove(block);
        let mut anchors = self.0.anchors.clone();
        anchors.remove(block);
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.without_key(block),
            opaque_import: self.0.opaque_import.clone(),
        })))
    }
}

#[cfg(test)]
mod tests;
