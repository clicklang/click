//! Proof names for exact mutex authority occurrences.
//!
//! A name is an alias, never a second resource. In particular, a copied name
//! does not keep an authority alive after its owned occurrence is consumed.

use super::{CResource, CResourceFact, CState, ResourceOccurrenceId, Variable};
use crate::persistent::PersistentMap;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

#[derive(Clone, Debug)]
struct NamedMutexAuthority {
    fact: CResourceFact,
    occurrence: ResourceOccurrenceId,
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct NamedMutexAuthorities {
    /// Includes the exact occurrences; state equality must distinguish a
    /// stale alias from one rebound to a live occurrence.
    identity: u64,
    /// Binder-to-fact identity, unchanged by an exact occurrence transfer.
    logical_bindings_identity: u64,
    aliases: PersistentMap<Variable, NamedMutexAuthority>,
    occupied: PersistentMap<ResourceOccurrenceId, Variable>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum NamedMutexAuthorityError {
    NotMutexAuthority,
    NotUniquelyOwned,
    AlreadyBound,
    AlreadyNamed,
    NotBound,
    MismatchedAuthority,
}

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_add(1, AtomicOrdering::Relaxed)
}

impl NamedMutexAuthorities {
    pub(in crate::kernel) fn new() -> Self {
        let identity = fresh_identity();
        Self {
            identity,
            logical_bindings_identity: identity,
            aliases: PersistentMap::default(),
            occupied: PersistentMap::default(),
        }
    }

    pub(in crate::kernel) fn same_logical_bindings(&self, other: &Self) -> bool {
        self.logical_bindings_identity == other.logical_bindings_identity
    }

    /// Select the exact owned occurrence now, so consuming and reinserting
    /// an equal fact cannot revive a stale alias.
    pub(in crate::kernel) fn bind(
        &self,
        binder: Variable,
        fact: &CResourceFact,
        state: &CState,
    ) -> Result<Self, NamedMutexAuthorityError> {
        if !matches!(
            fact,
            CResourceFact::Own(
                CResource::MutexLive(_) | CResource::MutexUse(_) | CResource::MutexGuard(_),
                _
            )
        ) || fact
            .owned_quantity_term()
            .is_none_or(|quantity| quantity.as_const() != Some(1))
        {
            return Err(NamedMutexAuthorityError::NotMutexAuthority);
        }
        if self.aliases.contains_key(&binder) {
            return Err(NamedMutexAuthorityError::AlreadyBound);
        }
        let (occurrence, _) = state
            .resources
            .unique_owned_occurrence_for_fact(fact)
            .ok_or(NamedMutexAuthorityError::NotUniquelyOwned)?;
        if self.occupied.contains_key(&occurrence) {
            return Err(NamedMutexAuthorityError::AlreadyNamed);
        }
        let identity = fresh_identity();
        Ok(Self {
            identity,
            logical_bindings_identity: identity,
            aliases: self.aliases.with_inserted(
                binder,
                NamedMutexAuthority {
                    fact: fact.clone(),
                    occurrence,
                },
            ),
            occupied: self.occupied.with_inserted(occurrence, binder),
        })
    }

    /// Resolution checks the occurrence on every use. The map by itself
    /// never proves ownership or licenses a mutex transition.
    pub(in crate::kernel) fn resolve<'a>(
        &'a self,
        binder: Variable,
        state: &CState,
    ) -> Option<&'a CResourceFact> {
        let alias = self.aliases.get(&binder)?;
        state
            .resources
            .owned_occurrence_matches(alias.occurrence, &alias.fact)
            .then_some(&alias.fact)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn forget(&self, binder: Variable) -> Self {
        let Some(previous) = self.aliases.get(&binder) else {
            return self.clone();
        };
        let identity = fresh_identity();
        Self {
            identity,
            logical_bindings_identity: identity,
            aliases: self.aliases.without_key(&binder),
            occupied: self.occupied.without_key(&previous.occurrence),
        }
    }

    /// Transport one checked name across a resource-context transfer that
    /// inserted a new occurrence for the very same mutex authority atom.
    /// The old occurrence need not survive, but its recorded fact must match
    /// exactly; a guard from a later acquisition cannot inherit this name.
    pub(in crate::kernel) fn rebind_existing_exact(
        &self,
        binder: Variable,
        expected: &CResourceFact,
        state: &CState,
    ) -> Result<Self, NamedMutexAuthorityError> {
        let previous = self
            .aliases
            .get(&binder)
            .ok_or(NamedMutexAuthorityError::NotBound)?;
        if &previous.fact != expected {
            return Err(NamedMutexAuthorityError::MismatchedAuthority);
        }
        let (occurrence, _) = state
            .resources
            .unique_owned_occurrence_for_fact(expected)
            .ok_or(NamedMutexAuthorityError::NotUniquelyOwned)?;
        if self
            .occupied
            .get(&occurrence)
            .is_some_and(|owner| *owner != binder)
        {
            return Err(NamedMutexAuthorityError::AlreadyNamed);
        }
        Ok(Self {
            identity: fresh_identity(),
            logical_bindings_identity: self.logical_bindings_identity,
            aliases: self.aliases.with_inserted(
                binder,
                NamedMutexAuthority {
                    fact: expected.clone(),
                    occurrence,
                },
            ),
            occupied: self
                .occupied
                .without_key(&previous.occurrence)
                .with_inserted(occurrence, binder),
        })
    }

    /// Follow only the exact occurrence exchanged by the checked loan adapter.
    /// A stale same-address alias is not selected by this indexed lookup.
    pub(in crate::kernel) fn apply_checked_mutex_updates(
        &self,
        updates: &[super::loans::mutex_calls::MutexAuthorityUpdate],
        state: &CState,
    ) -> Result<Self, NamedMutexAuthorityError> {
        let mut next = self.clone();
        for update in updates {
            let Some(binder) = next.occupied.get(&update.source_occurrence).copied() else {
                continue;
            };
            if update.source == update.derived {
                next = next.rebind_existing_exact(binder, &update.source, state)?;
            } else {
                next =
                    next.transport_checked_use(binder, &update.source, &update.derived, state)?;
            }
        }
        Ok(next)
    }

    /// A checked synchronous call may lend a live authority or reborrow a use
    /// share, giving its callee a different use atom under the same proof name.
    /// The caller supplies the checked loan transition; this map only verifies
    /// the selected source and new uniquely owned occurrence.
    pub(in crate::kernel) fn transport_checked_use(
        &self,
        binder: Variable,
        source: &CResourceFact,
        derived: &CResourceFact,
        state: &CState,
    ) -> Result<Self, NamedMutexAuthorityError> {
        let previous = self
            .aliases
            .get(&binder)
            .ok_or(NamedMutexAuthorityError::NotBound)?;
        if &previous.fact != source {
            return Err(NamedMutexAuthorityError::MismatchedAuthority);
        }
        let (source_mutex, source_initialization) = match source.resource() {
            CResource::MutexLive(identity) => (&identity.mutex, identity.epoch),
            CResource::MutexUse(identity) => (&identity.mutex, identity.initialization),
            _ => return Err(NamedMutexAuthorityError::NotMutexAuthority),
        };
        // A use share may also return to the lifecycle authority it was split
        // from, as when a join recovers a parent's retained share.
        let (target_mutex, target_initialization) = match derived.resource() {
            CResource::MutexUse(target) => (&target.mutex, target.initialization),
            CResource::MutexLive(target) if matches!(source.resource(), CResource::MutexUse(_)) => {
                (&target.mutex, target.epoch)
            }
            _ => return Err(NamedMutexAuthorityError::NotMutexAuthority),
        };
        if source_mutex != target_mutex
            || source_initialization.is_none()
            || source_initialization != target_initialization
        {
            return Err(NamedMutexAuthorityError::MismatchedAuthority);
        }
        let (occurrence, _) = state
            .resources
            .unique_owned_occurrence_for_fact(derived)
            .ok_or(NamedMutexAuthorityError::NotUniquelyOwned)?;
        if self
            .occupied
            .get(&occurrence)
            .is_some_and(|owner| *owner != binder)
        {
            return Err(NamedMutexAuthorityError::AlreadyNamed);
        }
        let identity = fresh_identity();
        Ok(Self {
            identity,
            logical_bindings_identity: identity,
            aliases: self.aliases.with_inserted(
                binder,
                NamedMutexAuthority {
                    fact: derived.clone(),
                    occurrence,
                },
            ),
            occupied: self
                .occupied
                .without_key(&previous.occurrence)
                .with_inserted(occurrence, binder),
        })
    }
}

impl PartialEq for NamedMutexAuthorities {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for NamedMutexAuthorities {}
impl PartialOrd for NamedMutexAuthorities {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for NamedMutexAuthorities {
    fn cmp(&self, other: &Self) -> Ordering {
        self.identity.cmp(&other.identity)
    }
}
impl Hash for NamedMutexAuthorities {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MutexIdentity, MutexUseIdentity, Pointer, ResourceContext};

    fn authority(epoch: u64) -> CResourceFact {
        CResourceFact::own(CResource::MutexLive(MutexIdentity {
            epoch: Some(epoch),
            mutex: Pointer::symbolic(Variable(400)),
        }))
    }

    fn use_authority(epoch: u64, mutex: Variable) -> CResourceFact {
        CResourceFact::own(CResource::MutexUse(MutexUseIdentity {
            protected: None,
            binding: None,
            initialization: Some(epoch),
            mutex: Pointer::symbolic(mutex),
        }))
    }

    #[test]
    fn checked_use_transport_requires_the_named_source_and_exact_derived_share() {
        let source = authority(1);
        let other = authority(2);
        let derived = use_authority(1, Variable(400));
        let mut state = CState::new();
        state.resources = ResourceContext::new().unchecked_with_fact(source.clone());
        let named = NamedMutexAuthorities::new()
            .bind(Variable(1), &source, &state)
            .unwrap();
        state.resources = ResourceContext::new().unchecked_with_fact(derived.clone());
        assert_eq!(
            named.transport_checked_use(Variable(1), &other, &derived, &state),
            Err(NamedMutexAuthorityError::MismatchedAuthority)
        );
        assert_eq!(
            named.transport_checked_use(
                Variable(1),
                &source,
                &use_authority(2, Variable(400)),
                &state,
            ),
            Err(NamedMutexAuthorityError::MismatchedAuthority)
        );
        assert_eq!(
            named.transport_checked_use(
                Variable(1),
                &source,
                &use_authority(1, Variable(401)),
                &state,
            ),
            Err(NamedMutexAuthorityError::MismatchedAuthority)
        );
        let moved = named
            .transport_checked_use(Variable(1), &source, &derived, &state)
            .unwrap();
        assert_eq!(moved.resolve(Variable(1), &state), Some(&derived));
        assert_ne!(moved, named);
        assert!(!moved.same_logical_bindings(&named));
        state.resources = ResourceContext::new();
        assert_eq!(moved.resolve(Variable(1), &state), None);
        assert_eq!(
            named.transport_checked_use(Variable(1), &source, &derived, &state),
            Err(NamedMutexAuthorityError::NotUniquelyOwned)
        );
    }

    #[test]
    fn aliases_require_exact_unique_live_mutex_authority() {
        let fact = authority(1);
        let mut state = CState::new();
        let empty = NamedMutexAuthorities::new();
        assert_eq!(
            empty.bind(Variable(1), &fact, &state),
            Err(NamedMutexAuthorityError::NotUniquelyOwned)
        );
        state.resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        let named = empty.bind(Variable(1), &fact, &state).unwrap();
        assert_eq!(named.resolve(Variable(1), &state), Some(&fact));
        assert_eq!(named.resolve(Variable(2), &state), None);
        assert_eq!(
            named.bind(Variable(2), &fact, &state),
            Err(NamedMutexAuthorityError::AlreadyNamed)
        );
        assert_eq!(
            named.bind(Variable(1), &fact, &state),
            Err(NamedMutexAuthorityError::AlreadyBound)
        );
        assert_eq!(
            named.bind(Variable(2), &authority(2), &state),
            Err(NamedMutexAuthorityError::NotUniquelyOwned)
        );
        let token = CResourceFact::own(CResource::Token {
            name: "other".into(),
            arguments: vec![].into(),
        });
        assert_eq!(
            named.bind(Variable(2), &token, &state),
            Err(NamedMutexAuthorityError::NotMutexAuthority)
        );
        state.resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        assert_eq!(named.resolve(Variable(1), &state), None);
        assert_eq!(named.forget(Variable(1)).resolve(Variable(1), &state), None);
        let rebound = named
            .rebind_existing_exact(Variable(1), &fact, &state)
            .unwrap();
        assert_eq!(rebound.resolve(Variable(1), &state), Some(&fact));
        assert_ne!(named, rebound);
        assert!(named.same_logical_bindings(&rebound));
        let other_guard = authority(2);
        state.resources = ResourceContext::new().unchecked_with_fact(other_guard.clone());
        assert_eq!(
            rebound.rebind_existing_exact(Variable(1), &other_guard, &state),
            Err(NamedMutexAuthorityError::MismatchedAuthority)
        );
        let different = NamedMutexAuthorities::new()
            .bind(Variable(1), &other_guard, &state)
            .unwrap();
        assert!(!rebound.same_logical_bindings(&different));
    }

    #[test]
    fn alias_lookup_does_not_scan_unrelated_resources() {
        let mut work = Vec::new();
        for size in [16, 64, 256] {
            let fact = authority(1);
            let mut state = CState::new();
            state.resources = ResourceContext::new().unchecked_with_fact(fact.clone());
            for index in 0..size {
                state.resources =
                    state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((result, deterministic), persistent) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        let aliases = NamedMutexAuthorities::new()
                            .bind(Variable(1), &fact, &state)
                            .unwrap();
                        aliases.resolve(Variable(1), &state).cloned()
                    })
                });
            assert_eq!(result, Some(fact));
            work.push((deterministic, persistent));
        }
        assert!(work[2].0 <= work[0].0 + 32, "alias lookup work: {work:?}");
        assert!(work[2].1 <= work[0].1 + 32, "alias index work: {work:?}");
    }
}
