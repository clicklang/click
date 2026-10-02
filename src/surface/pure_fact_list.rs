//! A proof path's ordered pure facts with the fact context they build kept
//! beside them.
//!
//! Planning executes a path one statement at a time, and every step reasons
//! under the context of the path's facts so far. Rebuilding that context from
//! the list at each step makes each step linear in the path and the path
//! quadratic. This list instead keeps the context of a prefix of its facts
//! and extends it by the facts appended since, so a step pays for the facts
//! it adds. A mutation that removes or reorders a fact inside the built
//! prefix drops the context, and the next query rebuilds it once.
//!
//! The context is the one a rebuild from the list would produce: it is
//! built by the same fold over the same facts in the same order.

use crate::kernel::proof::PropositionSource;
use crate::kernel::{Proposition, PureFactContext};
use std::sync::Mutex;

/// The context of a prefix of some ordered fact sequence, built on demand
/// and extended as the sequence grows. The owner guarantees that the facts
/// it passes are the sequence the prefix was built from, grown only at its
/// end, and drops the prefix otherwise ([`Self::invalidate_from`]).
///
/// A lock rather than a cell only so an owner stays shareable across
/// threads; no caller contends for it.
#[derive(Debug, Default)]
pub(crate) struct BuiltContext(Mutex<Option<(usize, PureFactContext)>>);

impl Clone for BuiltContext {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.lock().clone()))
    }
}

impl BuiltContext {
    /// The context of all of `facts`, extending the built prefix by the
    /// facts after it. Each fact a context assumes here is charged one unit
    /// of work.
    pub(crate) fn context_of(&self, facts: &[Proposition]) -> PureFactContext {
        self.context_of_selected(
            facts,
            |fact, selected| {
                selected.push(crate::kernel::clone_proposition_iteratively(fact));
            },
            true,
        )
    }

    /// The context of the parts `select` takes from each of `facts`, in
    /// order, extending the built prefix by the facts after it; each
    /// assumed part is charged unless `charged` is false. `select` must be
    /// the same for every call on this prefix.
    fn context_of_selected(
        &self,
        facts: &[Proposition],
        select: impl Fn(&Proposition, &mut Vec<Proposition>),
        charged: bool,
    ) -> PureFactContext {
        let mut built = self.lock();
        let (length, context) = built.get_or_insert_with(|| (0, PureFactContext::new()));
        debug_assert!(*length <= facts.len());
        if *length < facts.len() {
            let mut selected = Vec::new();
            for fact in &facts[*length..] {
                select(fact, &mut selected);
            }
            if charged {
                crate::kernel::reasoning::path_facts::count_context_rebuild_entries(selected.len());
                for fact in selected {
                    *context = std::mem::take(context).assume_proposition(fact);
                }
            } else {
                crate::kernel::reasoning::path_facts::count_uncharged_context_entries(
                    selected.len(),
                );
                for fact in selected {
                    *context = std::mem::take(context).assume_proposition_uncharged(fact);
                }
            }
            *length = facts.len();
        }
        context.clone()
    }

    /// Drops the built prefix when it reaches `index`, the first position
    /// whose fact changed.
    pub(crate) fn invalidate_from(&mut self, index: usize) {
        let built = self
            .0
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if built.as_ref().is_some_and(|(length, _)| *length > index) {
            *built = None;
        }
    }

    /// Keeps whichever of this prefix and `other`'s is longer. Both must
    /// have been built from prefixes of one sequence.
    pub(crate) fn adopt_longer(&mut self, other: &Self) {
        let other = other.lock().clone();
        let built = self
            .0
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if other
            .as_ref()
            .is_some_and(|(length, _)| built.as_ref().is_none_or(|(built, _)| length > built))
        {
            *built = other;
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Option<(usize, PureFactContext)>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct PureFactList {
    facts: Vec<Proposition>,
    built: BuiltContext,
    /// The context of the facts' direct-transport premises
    /// (`kernel::proof::fact_reasoning::direct_fact_transport_premises`).
    transport_built: BuiltContext,
}

impl PartialEq for PureFactList {
    fn eq(&self, other: &Self) -> bool {
        self.facts == other.facts
    }
}

impl Eq for PureFactList {}

impl From<Vec<Proposition>> for PureFactList {
    fn from(facts: Vec<Proposition>) -> Self {
        Self {
            facts,
            built: BuiltContext::default(),
            transport_built: BuiltContext::default(),
        }
    }
}

impl FromIterator<Proposition> for PureFactList {
    fn from_iter<I: IntoIterator<Item = Proposition>>(facts: I) -> Self {
        Self::from(facts.into_iter().collect::<Vec<_>>())
    }
}

impl std::ops::Deref for PureFactList {
    type Target = Vec<Proposition>;

    fn deref(&self) -> &Vec<Proposition> {
        &self.facts
    }
}

impl<'a> IntoIterator for &'a PureFactList {
    type Item = &'a Proposition;
    type IntoIter = std::slice::Iter<'a, Proposition>;

    fn into_iter(self) -> Self::IntoIter {
        self.facts.iter()
    }
}

impl PureFactList {
    /// Retain an already checked source's graph while materializing the
    /// ordered syntax needed by the surface driver. Re-admitting this prefix
    /// would disconnect resources published against the source context.
    pub(crate) fn from_source(source: &(impl PropositionSource + ?Sized)) -> Self {
        let facts = source
            .propositions()
            .map(crate::kernel::clone_proposition_iteratively)
            .collect::<Vec<_>>();
        let built = BuiltContext(Mutex::new(Some((facts.len(), source.pure_context()))));
        Self::with_built_context(facts, built)
    }

    /// `facts` with the context `built` holds for a prefix of them.
    pub(crate) fn with_built_context(facts: Vec<Proposition>, built: BuiltContext) -> Self {
        Self {
            facts,
            built,
            transport_built: BuiltContext::default(),
        }
    }

    /// The context of every fact in the list, extending the built prefix by
    /// the facts appended since.
    pub(crate) fn context(&self) -> PureFactContext {
        self.built.context_of(&self.facts)
    }

    pub(crate) fn built_context(&self) -> &BuiltContext {
        &self.built
    }

    /// The context of the facts' direct-transport premises, in order,
    /// extended like [`Self::context`].
    pub(crate) fn direct_transport_context(&self) -> PureFactContext {
        self.transport_built.context_of_selected(
            &self.facts,
            crate::kernel::proof::fact_reasoning::direct_fact_transport_premises,
            // A known violation: a simple step's statement-local facts hold
            // every observable resource fact of its state, so this context
            // is linear in the unrelated resources at each call step, and
            // charging it grows
            // `expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations`
            // by a unit per unrelated allocation.
            false,
        )
    }

    pub(crate) fn into_vec(self) -> Vec<Proposition> {
        self.facts
    }

    pub(crate) fn push(&mut self, fact: Proposition) {
        self.facts.push(fact);
    }

    pub(crate) fn extend(&mut self, facts: impl IntoIterator<Item = Proposition>) {
        self.facts.extend(facts);
    }

    /// Keeps the facts `keep` accepts, in order. The built context survives
    /// only when every removed fact lies after its prefix.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&Proposition) -> bool) {
        let mut first_removed = None;
        let mut index = 0;
        self.facts.retain(|fact| {
            let kept = keep(fact);
            if !kept && first_removed.is_none() {
                first_removed = Some(index);
            }
            index += 1;
            kept
        });
        if let Some(first_removed) = first_removed {
            self.invalidate_from(first_removed);
        }
    }

    /// Replaces a transported fact's source with its target at the source's
    /// position: downstream premise selection is order-sensitive, so
    /// rewriting must not reorder the working set. Kept out of line, like
    /// the by-value proposition handling of the shared transition
    /// dispatcher it serves; the expansion small-stack regression pins that
    /// boundary.
    #[inline(never)]
    pub(crate) fn replace_fact_in_place(&mut self, source: &Proposition, target: &Proposition) {
        if let Some(position) = self.facts.iter().position(|fact| fact == source) {
            if self.facts.contains(target) {
                self.facts.remove(position);
            } else {
                self.facts[position] = target.clone();
            }
            self.invalidate_from(position);
        } else if !self.facts.contains(target) {
            self.facts.push(target.clone());
        }
    }

    fn invalidate_from(&mut self, index: usize) {
        self.built.invalidate_from(index);
        self.transport_built.invalidate_from(index);
    }
}

impl PropositionSource for PureFactList {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.facts.iter()
    }

    fn pure_context(&self) -> PureFactContext {
        self.context()
    }
}
