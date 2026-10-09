//! Additive authority-migration spine. This models owned anchor lifetimes,
//! not C pointers or memory permissions. No legacy C proof can invoke it.
//!
//! Each immutable state is one proof alternative. Holders represent separate
//! owners within that alternative, so passing an anchor cannot erase an
//! authority held elsewhere. The C bridge must obtain an anchor from checked
//! storage-lifetime evidence; `allocate_anchor` grants no C memory ownership.
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::atomic::{AtomicU64, Ordering};

pub(in crate::kernel) mod c_creation;

fn fresh() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("population authority identity exhausted")
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Holder(u64);
impl Holder {
    pub(super) fn fresh() -> Self {
        Self(fresh())
    }
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Anchor(u64);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Population(u64);

#[derive(Clone, Debug, PartialEq)]
struct AnchorRecord {
    owner: Holder,
    // Creation permission stays with the creating proof environment. Moving
    // memory ownership does not move this permission to another function.
    creator: Holder,
    // Keep retired scopes until this lifetime ends: retirement must not
    // authorize a fresh zero-count assertion about the same population.
    established: PersistentSet<String>,
    registrations: u32,
}
#[derive(Clone, Debug, PartialEq)]
struct PopulationRecord {
    anchor: Anchor,
    family: String,
    owner: Holder,
    total: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Refusal {
    MissingAnchor,
    NotCreationEnvironment,
    MissingAuthority,
    MissingMembers,
    AlreadyEstablished,
    UnknownPopulation,
    OutstandingMembers,
    OutstandingAuthority,
    OutstandingOwnership,
    InvalidQuantity,
}

/// Exact unary populations for the first kernel slice: family(anchor).
/// Every lookup/update touches a bounded number of persistent map paths.
/// Wildcard scopes, C bindings, symbolic totals, views, and loans are not
/// admitted by this module; callers cannot simulate them with guessed IDs.
#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct AuthorityState {
    anchors: PersistentMap<Anchor, AnchorRecord>,
    registrations: PersistentMap<(Anchor, String), Population>,
    populations: PersistentMap<Population, PopulationRecord>,
    members: PersistentMap<(Holder, Population), u32>,
    obligations: PersistentMap<Holder, u64>,
}

impl AuthorityState {
    pub(super) fn is_empty(&self) -> bool {
        self.anchors.is_empty()
            && self.registrations.is_empty()
            && self.populations.is_empty()
            && self.members.is_empty()
            && self.obligations.is_empty()
    }

    fn shares_roots_with(&self, other: &Self) -> bool {
        self.anchors.shares_root_with(&other.anchors)
            && self.registrations.shares_root_with(&other.registrations)
            && self.populations.shares_root_with(&other.populations)
            && self.members.shares_root_with(&other.members)
            && self.obligations.shares_root_with(&other.obligations)
    }

    /// Whether the two states differ only in the paired anchors, each pair
    /// holding equal records on which no population is established. Such an
    /// anchor is named only by its own record, so renaming it changes no
    /// registration, population, member or obligation.
    pub(super) fn same_up_to_unestablished_anchors(
        &self,
        other: &Self,
        renamed: &[(Anchor, Anchor)],
    ) -> bool {
        let mut left_anchors = self.anchors.clone();
        let mut right_anchors = other.anchors.clone();
        for (left, right) in renamed {
            let (Some(left_record), Some(right_record)) =
                (self.anchors.get(left), other.anchors.get(right))
            else {
                return false;
            };
            if left_record != right_record
                || left_record.registrations != 0
                || !left_record.established.is_empty()
            {
                return false;
            }
            left_anchors.remove(left);
            right_anchors.remove(right);
        }
        left_anchors == right_anchors
            && self.registrations == other.registrations
            && self.populations == other.populations
            && self.members == other.members
            && self.obligations == other.obligations
    }

    fn change_obligations(&mut self, holder: Holder, remove: u64, add: u64) {
        let prior = self.obligations.get(&holder).copied().unwrap_or(0);
        let next = prior
            .checked_sub(remove)
            .and_then(|n| n.checked_add(add))
            .expect("checked authority ownership accounting");
        if next == 0 {
            self.obligations.remove(&holder);
        } else {
            self.obligations.insert(holder, next);
        }
    }
    fn anchor_owned(&self, holder: Holder, anchor: Anchor) -> Result<&AnchorRecord, Refusal> {
        self.anchors
            .get(&anchor)
            .filter(|r| r.owner == holder)
            .ok_or(Refusal::MissingAnchor)
    }
    fn authority_owned(
        &self,
        holder: Holder,
        population: Population,
    ) -> Result<&PopulationRecord, Refusal> {
        self.populations
            .get(&population)
            .ok_or(Refusal::UnknownPopulation)
            .and_then(|r| {
                if r.owner == holder {
                    Ok(r)
                } else {
                    Err(Refusal::MissingAuthority)
                }
            })
    }

    pub(super) fn holder_owns_authority(&self, holder: Holder, population: Population) -> bool {
        self.authority_owned(holder, population).is_ok()
    }

    pub(super) fn holder_owns_member(&self, holder: Holder, population: Population) -> bool {
        self.members
            .get(&(holder, population))
            .is_some_and(|count| *count > 0)
    }
    fn set_members(&mut self, holder: Holder, population: Population, quantity: u32) {
        if quantity == 0 {
            self.members.remove(&(holder, population));
        } else {
            self.members.insert((holder, population), quantity);
        }
    }
    fn positive(quantity: u32) -> Result<(), Refusal> {
        if quantity == 0 || quantity > i32::MAX as u32 {
            Err(Refusal::InvalidQuantity)
        } else {
            Ok(())
        }
    }

    /// Introduce a *fresh abstract* anchor lifetime. This cannot bind a chosen
    /// existing C address. A later checked C bridge must transport the same
    /// anchor through aliases/calls instead of calling this on every lookup.
    pub(super) fn allocate_anchor(&self, holder: Holder) -> (Self, Anchor) {
        let anchor = Anchor(fresh());
        let mut next = self.clone();
        next.anchors.insert(
            anchor,
            AnchorRecord {
                owner: holder,
                creator: holder,
                established: PersistentSet::default(),
                registrations: 0,
            },
        );
        next.change_obligations(holder, 0, 1);
        (next, anchor)
    }

    /// Establish once per scope in the creating environment, while it owns
    /// the anchor. Contract entry must use a distinct holder and may only
    /// receive already-established authority, never creation permission.
    pub(super) fn establish(
        &self,
        holder: Holder,
        anchor: Anchor,
        family: &str,
    ) -> Result<(Self, Population), Refusal> {
        let mut record = self.anchor_owned(holder, anchor)?.clone();
        let key = (anchor, family.to_owned());
        if record.established.contains(&key.1) {
            return Err(Refusal::AlreadyEstablished);
        }
        if record.creator != holder {
            return Err(Refusal::NotCreationEnvironment);
        }
        record.established = record.established.with_value(key.1.clone());
        record.registrations = record
            .registrations
            .checked_add(1)
            .ok_or(Refusal::InvalidQuantity)?;
        let population = Population(fresh());
        let mut next = self.clone();
        next.anchors.insert(anchor, record);
        next.registrations.insert(key, population);
        next.populations.insert(
            population,
            PopulationRecord {
                anchor,
                family: family.into(),
                owner: holder,
                total: 0,
            },
        );
        next.change_obligations(holder, 0, 1);
        Ok((next, population))
    }

    /// Resolve a resource type's live population identity. Naming it grants
    /// neither authority nor members; observations still check ownership.
    pub(super) fn population_at(&self, anchor: Anchor, family: &str) -> Option<Population> {
        self.registrations
            .get(&(anchor, family.to_owned()))
            .copied()
    }

    pub(super) fn observe(&self, holder: Holder, population: Population) -> Result<u32, Refusal> {
        Ok(self.authority_owned(holder, population)?.total)
    }

    /// Creates members at the authority holder. Ordinary transfer can then
    /// distribute them; no operation changes another holder's members.
    pub(super) fn produce(
        &self,
        holder: Holder,
        population: Population,
        quantity: u32,
    ) -> Result<Self, Refusal> {
        Self::positive(quantity)?;
        let mut record = self.authority_owned(holder, population)?.clone();
        record.total = record
            .total
            .checked_add(quantity)
            .filter(|n| *n <= i32::MAX as u32)
            .ok_or(Refusal::InvalidQuantity)?;
        let owned = self
            .members
            .get(&(holder, population))
            .copied()
            .unwrap_or(0);
        let mut next = self.clone();
        next.populations.insert(population, record);
        next.set_members(holder, population, owned + quantity);
        next.change_obligations(holder, 0, u64::from(quantity));
        Ok(next)
    }

    pub(super) fn consume(
        &self,
        holder: Holder,
        population: Population,
        quantity: u32,
    ) -> Result<Self, Refusal> {
        Self::positive(quantity)?;
        let mut record = self.authority_owned(holder, population)?.clone();
        let owned = self
            .members
            .get(&(holder, population))
            .copied()
            .unwrap_or(0);
        let remaining = owned.checked_sub(quantity).ok_or(Refusal::MissingMembers)?;
        record.total = record
            .total
            .checked_sub(quantity)
            .expect("members covered by total");
        let mut next = self.clone();
        next.populations.insert(population, record);
        next.set_members(holder, population, remaining);
        next.change_obligations(holder, u64::from(quantity), 0);
        Ok(next)
    }

    pub(super) fn transfer_members(
        &self,
        from: Holder,
        to: Holder,
        population: Population,
        quantity: u32,
    ) -> Result<Self, Refusal> {
        Self::positive(quantity)?;
        if !self.populations.contains_key(&population) {
            return Err(Refusal::UnknownPopulation);
        }
        let owned = self.members.get(&(from, population)).copied().unwrap_or(0);
        let remaining = owned.checked_sub(quantity).ok_or(Refusal::MissingMembers)?;
        if from == to {
            return Ok(self.clone());
        }
        let received = self
            .members
            .get(&(to, population))
            .copied()
            .unwrap_or(0)
            .checked_add(quantity)
            .ok_or(Refusal::InvalidQuantity)?;
        let mut next = self.clone();
        next.set_members(from, population, remaining);
        next.set_members(to, population, received);
        next.change_obligations(from, u64::from(quantity), 0);
        next.change_obligations(to, 0, u64::from(quantity));
        Ok(next)
    }

    pub(super) fn transfer_authority(
        &self,
        from: Holder,
        to: Holder,
        population: Population,
    ) -> Result<Self, Refusal> {
        let mut record = self.authority_owned(from, population)?.clone();
        if from == to {
            return Ok(self.clone());
        }
        record.owner = to;
        let mut next = self.clone();
        next.populations.insert(population, record);
        next.change_obligations(from, 1, 0);
        next.change_obligations(to, 0, 1);
        Ok(next)
    }

    pub(super) fn transfer_anchor(
        &self,
        from: Holder,
        to: Holder,
        anchor: Anchor,
    ) -> Result<Self, Refusal> {
        let mut record = self.anchor_owned(from, anchor)?.clone();
        if from == to {
            return Ok(self.clone());
        }
        record.owner = to;
        let mut next = self.clone();
        next.anchors.insert(anchor, record);
        next.change_obligations(from, 1, 0);
        next.change_obligations(to, 0, 1);
        Ok(next)
    }

    pub(super) fn retire(&self, holder: Holder, population: Population) -> Result<Self, Refusal> {
        let record = self.authority_owned(holder, population)?;
        if record.total != 0 {
            return Err(Refusal::OutstandingMembers);
        }
        let mut anchor = self
            .anchors
            .get(&record.anchor)
            .expect("registered live anchor")
            .clone();
        anchor.registrations -= 1;
        let mut next = self.clone();
        next.anchors.insert(record.anchor, anchor);
        next.registrations
            .remove(&(record.anchor, record.family.clone()));
        next.populations.remove(&population);
        next.change_obligations(holder, 1, 0);
        Ok(next)
    }

    pub(super) fn free_anchor(&self, holder: Holder, anchor: Anchor) -> Result<Self, Refusal> {
        if self.anchor_owned(holder, anchor)?.registrations != 0 {
            return Err(Refusal::OutstandingAuthority);
        }
        let mut next = self.clone();
        next.anchors.remove(&anchor);
        next.change_obligations(holder, 1, 0);
        Ok(next)
    }

    /// Scope exit cannot silently discard control, members, or an anchor.
    pub(super) fn finish_holder(&self, holder: Holder) -> Result<(), Refusal> {
        if self.obligations.contains_key(&holder) {
            Err(Refusal::OutstandingOwnership)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests;
