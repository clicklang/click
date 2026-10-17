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
//!
//! The facts themselves are persistent. Each one is filed under a sequence
//! number that only grows, so the list's order is the order of those
//! numbers, a copy of the list shares every fact with its source, and a
//! fact appended, removed or replaced in place costs a logarithm. The
//! questions the execution steps ask of a whole list (is this exact fact,
//! or a conjunct of one, there; does a statement fact directly contradict
//! one; which facts can a store's transport move) are answered from
//! persistent indexes the list keeps beside its facts, so a step touches
//! the facts it names rather than every fact before it. A caller that needs
//! the facts as a slice still gets one (`Deref`), materialized once per
//! list version and counted as a copy (`count_flat_fact_copies`).

use crate::kernel::proof::ProofFacts;
use crate::kernel::proof::PropositionSource;
use crate::kernel::{Proposition, PureFactContext};
use std::sync::{Arc, Mutex, OnceLock};

/// The context of a prefix of some ordered fact sequence, built on demand
/// and extended as the sequence grows. The owner guarantees that the facts
/// it passes are the sequence the prefix was built from, grown only at its
/// end, and drops the prefix otherwise ([`Self::invalidate_from`]). The
/// prefix is named by the first sequence number after it.
///
/// A lock rather than a cell only so an owner stays shareable across
/// threads; no caller contends for it.
#[derive(Debug, Default)]
pub(crate) struct BuiltContext(Mutex<Option<(u64, PureFactContext)>>);

impl Clone for BuiltContext {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.lock().clone()))
    }
}

type FactEntries = imbl::OrdMap<u64, Arc<Proposition>>;

impl BuiltContext {
    fn built(through: u64, context: PureFactContext) -> Self {
        Self(Mutex::new(Some((through, context))))
    }

    /// The context of all of `facts`, extending the built prefix by the
    /// facts after it. Each fact a context assumes here is charged one unit
    /// of work.
    fn context_of(&self, facts: &FactEntries, next: u64) -> PureFactContext {
        self.context_of_selected(
            facts,
            next,
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
        facts: &FactEntries,
        next: u64,
        select: impl Fn(&Proposition, &mut Vec<Proposition>),
        charged: bool,
    ) -> PureFactContext {
        let mut built = self.lock();
        let (through, context) = built.get_or_insert_with(|| (0, PureFactContext::new()));
        debug_assert!(*through <= next);
        if *through < next {
            let mut selected = Vec::new();
            for (_, fact) in facts.range(*through..) {
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
            *through = next;
        }
        context.clone()
    }

    /// Drops the built prefix when it holds `sequence`, the first fact that
    /// changed.
    fn invalidate_from(&mut self, sequence: u64) {
        let built = self
            .0
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if built
            .as_ref()
            .is_some_and(|(through, _)| *through > sequence)
        {
            *built = None;
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Option<(u64, PureFactContext)>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

/// The exact-syntax indexes of a list's facts. `by_fact` files every fact
/// under its own sequence numbers; `conjuncts` counts every node of every
/// fact's conjunction tree, the fact itself included, so a fact that is, or
/// has as a conjunct, a given proposition is one lookup.
#[derive(Clone, Default)]
struct ExactFactIndex {
    by_fact: imbl::OrdMap<Arc<Proposition>, imbl::OrdSet<u64>>,
    conjuncts: imbl::OrdMap<Arc<Proposition>, usize>,
}

impl ExactFactIndex {
    fn insert(&mut self, sequence: u64, fact: &Arc<Proposition>) {
        count_fact_index_entries(1);
        self.by_fact
            .entry(fact.clone())
            .or_default()
            .insert(sequence);
        conjunction_nodes(fact, &mut |node| {
            *self.conjuncts.entry(Arc::new(node.clone())).or_insert(0) += 1;
        });
    }

    fn remove(&mut self, sequence: u64, fact: &Proposition) {
        count_fact_index_entries(1);
        if let Some(sequences) = self.by_fact.get_mut(fact) {
            sequences.remove(&sequence);
            if sequences.is_empty() {
                self.by_fact.remove(fact);
            }
        }
        conjunction_nodes(fact, &mut |node| {
            if let Some(count) = self.conjuncts.get_mut(node) {
                *count -= 1;
                if *count == 0 {
                    self.conjuncts.remove(node);
                }
            }
        });
    }
}

/// `fact` and, through conjunctions, every conjunct of it.
fn conjunction_nodes(fact: &Proposition, visit: &mut impl FnMut(&Proposition)) {
    visit(fact);
    if let Proposition::And(left, right) = fact {
        conjunction_nodes(left, visit);
        conjunction_nodes(right, visit);
    }
}

/// The facts an automatic store transport can move: those for which
/// `c_condition_fact_has_memory` holds or that name a load variable. A fact
/// naming only unregistered load variables is kept too, since a later
/// registration makes it one the transport reads; the transport applies its
/// exact test to each candidate. Evaluated lazily, for the facts filed since
/// the last query and those replaced in place, and kept as facts are
/// removed.
#[derive(Clone, Default)]
struct TransportCandidates {
    /// Sequence numbers below this have been evaluated, except `pending`.
    through: u64,
    pending: imbl::OrdSet<u64>,
    candidates: imbl::OrdSet<u64>,
}

impl TransportCandidates {
    fn refresh(&mut self, facts: &FactEntries, next: u64) {
        let mut evaluate = |sequence: u64, fact: &Proposition| {
            count_transport_candidate_tests(1);
            if crate::kernel::c_condition_fact_has_memory(fact)
                || crate::kernel::proposition_mentions_load_variable(fact)
            {
                self.candidates.insert(sequence);
            }
        };
        for sequence in std::mem::take(&mut self.pending) {
            if let Some(fact) = facts.get(&sequence) {
                evaluate(sequence, fact);
            }
        }
        if self.through < next {
            for (sequence, fact) in facts.range(self.through..) {
                evaluate(*sequence, fact);
            }
            self.through = next;
        }
    }

    fn remove(&mut self, sequence: u64) {
        self.candidates.remove(&sequence);
        self.pending.remove(&sequence);
    }

    fn replace(&mut self, sequence: u64) {
        self.candidates.remove(&sequence);
        if sequence < self.through {
            self.pending.insert(sequence);
        }
    }
}

/// The sequence number of a new list's first fact, leaving room below for
/// facts a list extension puts in front (`extended_to_proof_facts`).
const SEQUENCE_ORIGIN: u64 = 1 << 62;

#[derive(Clone)]
pub(crate) struct PureFactList {
    facts: FactEntries,
    /// The sequence number the next appended fact takes.
    next: u64,
    /// The facts as one vector, for callers that read them as a slice.
    flat: Arc<OnceLock<Vec<Proposition>>>,
    /// Built on the first exact query, then kept by every mutation.
    exact: Arc<OnceLock<ExactFactIndex>>,
    transport: Arc<Mutex<Option<TransportCandidates>>>,
    built: BuiltContext,
    /// The context of the facts' direct-transport premises
    /// (`kernel::proof::fact_reasoning::direct_fact_transport_premises`).
    transport_built: BuiltContext,
    /// The indexed proof facts this list was copied from, and the first
    /// sequence number after the prefix they hold, so a proof over the list
    /// extends them by the facts appended since instead of indexing every
    /// fact again.
    source: Option<(ProofFacts, u64)>,
}

impl Default for PureFactList {
    fn default() -> Self {
        Self {
            facts: FactEntries::default(),
            next: SEQUENCE_ORIGIN,
            flat: Arc::default(),
            exact: Arc::default(),
            transport: Arc::default(),
            built: BuiltContext::default(),
            transport_built: BuiltContext::default(),
            source: None,
        }
    }
}

impl std::fmt::Debug for PureFactList {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PureFactList")
            .field("facts", &self.iter().collect::<Vec<_>>())
            .field("built", &self.built)
            .field("transport_built", &self.transport_built)
            .finish_non_exhaustive()
    }
}

impl PartialEq for PureFactList {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl Eq for PureFactList {}

impl From<Vec<Proposition>> for PureFactList {
    fn from(facts: Vec<Proposition>) -> Self {
        let mut list = Self::default();
        list.extend(facts);
        list
    }
}

impl FromIterator<Proposition> for PureFactList {
    fn from_iter<I: IntoIterator<Item = Proposition>>(facts: I) -> Self {
        let mut list = Self::default();
        list.extend(facts);
        list
    }
}

impl std::ops::Deref for PureFactList {
    type Target = Vec<Proposition>;

    /// The facts as a vector, materialized once for this version of the
    /// list. Every entry copied is counted (`count_flat_fact_copies`): a
    /// step that reads its whole list this way pays for every earlier fact.
    fn deref(&self) -> &Vec<Proposition> {
        self.flat.get_or_init(|| {
            count_flat_fact_copies(self.facts.len());
            self.facts
                .values()
                .map(|fact| crate::kernel::clone_proposition_iteratively(fact))
                .collect()
        })
    }
}

/// The facts of a list in order.
pub(crate) type PureFactIter<'a> = std::iter::Map<
    imbl::ordmap::Values<'a, u64, Arc<Proposition>, imbl::shared_ptr::DefaultSharedPtr>,
    fn(&'a Arc<Proposition>) -> &'a Proposition,
>;

impl<'a> IntoIterator for &'a PureFactList {
    type Item = &'a Proposition;
    type IntoIter = PureFactIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl PureFactList {
    /// Retain an already checked source's graph while materializing the
    /// ordered syntax needed by the surface driver. Re-admitting this prefix
    /// would disconnect resources published against the source context.
    pub(crate) fn from_source(source: &(impl PropositionSource + ?Sized)) -> Self {
        let mut list = Self::default();
        list.extend(
            source
                .propositions()
                .map(crate::kernel::clone_proposition_iteratively),
        );
        list.built = BuiltContext::built(list.next, source.pure_context());
        list
    }

    /// The facts of a proof, in its order, with every context and index the
    /// proof already keeps: its context, its direct-transport context when it
    /// keeps one, and the proof facts themselves. The proof's contexts were
    /// built over the same facts in the order they were added, which is not
    /// necessarily this order; a context is the facts it assumes, not the
    /// order it met them in, so the list keeps them rather than rebuilding.
    pub(crate) fn from_proof_facts(source: &ProofFacts) -> Self {
        let mut list = Self::from_source(source);
        list.adopt_proof_facts(source);
        list
    }

    /// What [`Self::from_proof_facts`] builds from `source`, built from
    /// `base`, an unchanged list `from_proof_facts` (or this) built from
    /// earlier proof facts of the same proof, by placing the facts `source`
    /// has gained since where `ProofFacts::propositions` yields them: a new
    /// statement batch's facts in front (moving a fact `base` already holds
    /// there), facts appended to the proof after. `base`'s facts and
    /// indexes are shared, not copied again. `None` when `source` does not
    /// extend `base`'s proof facts.
    pub(crate) fn extended_to_proof_facts(base: &Self, source: &ProofFacts) -> Option<Self> {
        let (base_source, through) = base.source.as_ref()?;
        if *through != base.next {
            return None;
        }
        let (front, appended) = source.propositions_since(base_source)?;
        let mut list = base.clone();
        // `propositions` yields each distinct fact once, at its first
        // occurrence: the newest batches, then the older facts, then the
        // appended ones.
        let mut seen = std::collections::BTreeSet::new();
        let mut moved = Vec::new();
        let mut leading = Vec::new();
        for fact in front {
            if seen.contains(&fact) {
                continue;
            }
            if let Some(sequences) = list.exact_index().by_fact.get(&fact) {
                moved.extend(sequences.iter().copied());
            }
            seen.insert(fact.clone());
            leading.push(fact);
        }
        list.remove_sequences(&moved);
        list.prepend(leading);
        for fact in appended {
            if !seen.contains(fact.as_ref()) && !list.contains(&fact) {
                list.push(crate::kernel::clone_proposition_iteratively(&fact));
            }
        }
        list.built = BuiltContext::built(list.next, source.pure_context());
        list.transport_built = BuiltContext::default();
        list.adopt_proof_facts(source);
        #[cfg(debug_assertions)]
        if fact_list_check_enabled() {
            crate::instrumentation::uncharged_debug_check(|| {
                assert!(
                    list.iter().eq(source.propositions()),
                    "an extended loop fact list lost the order its proof facts present"
                );
            });
        }
        Some(list)
    }

    /// Puts `facts`, in order, before every fact of the list.
    fn prepend(&mut self, facts: Vec<Proposition>) {
        if facts.is_empty() {
            return;
        }
        let first = self
            .facts
            .get_min()
            .map_or(self.next, |(sequence, _)| *sequence);
        let start = first - facts.len() as u64;
        let (mut exact, mut transport) = self.begin_mutation();
        for (offset, fact) in facts.into_iter().enumerate() {
            let sequence = start + offset as u64;
            let fact = Arc::new(fact);
            if let Some(index) = exact.as_mut() {
                index.insert(sequence, &fact);
            }
            if let Some(transport) = transport.as_mut() {
                transport.pending.insert(sequence);
            }
            self.facts.insert(sequence, fact);
        }
        self.end_mutation(exact, transport);
        self.invalidate_from(start);
    }

    fn adopt_proof_facts(&mut self, source: &ProofFacts) {
        if let Some(transport) = source.direct_transport_assumptions() {
            self.transport_built = BuiltContext::built(self.next, transport.clone());
        }
        self.source = Some((source.clone(), self.next));
    }

    /// Indexed proof facts holding exactly this list's facts, in its order:
    /// the proof facts it was copied from extended by the facts appended
    /// since, or every fact indexed afresh when it was not copied from any
    /// or a fact inside the copied prefix has since changed.
    pub(crate) fn proof_facts(&self) -> ProofFacts {
        match &self.source {
            Some((source, through)) => self
                .facts
                .range(*through..)
                .fold(source.clone(), |facts, (_, fact)| {
                    facts.with_kernel_checked_fact(fact.as_ref().clone())
                }),
            None => ProofFacts::from_ordered(&self.to_vec()),
        }
    }

    /// Retain the already checked context of this exact ordered fact list.
    pub(crate) fn with_checked_context(facts: Vec<Proposition>, context: PureFactContext) -> Self {
        let mut list = Self::from(facts);
        list.built = BuiltContext::built(list.next, context);
        list
    }

    /// The context of every fact in the list, extending the built prefix by
    /// the facts appended since.
    pub(crate) fn context(&self) -> PureFactContext {
        self.built.context_of(&self.facts, self.next)
    }

    /// The context of the facts' direct-transport premises, in order,
    /// extended like [`Self::context`].
    pub(crate) fn direct_transport_context(&self) -> PureFactContext {
        self.transport_built.context_of_selected(
            &self.facts,
            self.next,
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

    pub(crate) fn len(&self) -> usize {
        self.facts.len()
    }

    /// The facts in order, read in place.
    pub(crate) fn iter(&self) -> PureFactIter<'_> {
        self.facts
            .values()
            .map(Arc::as_ref as fn(&Arc<Proposition>) -> &Proposition)
    }

    /// The facts as an owned vector.
    pub(crate) fn to_vec(&self) -> Vec<Proposition> {
        count_flat_fact_copies(self.facts.len());
        self.facts
            .values()
            .map(|fact| crate::kernel::clone_proposition_iteratively(fact))
            .collect()
    }

    pub(crate) fn into_vec(self) -> Vec<Proposition> {
        self.to_vec()
    }

    /// The facts after the first `length`, in order.
    pub(crate) fn facts_after(&self, length: usize) -> Vec<Proposition> {
        self.iter().skip(length).cloned().collect()
    }

    /// Whether `fact` is one of the facts.
    pub(crate) fn contains(&self, fact: &Proposition) -> bool {
        self.exact_index().by_fact.contains_key(fact)
    }

    /// Whether `required` is one of the facts or, through conjunctions, a
    /// conjunct of one: what `exactly_available_fact` finds in a slice of
    /// these facts, by one lookup.
    pub(crate) fn has_exact_conjunct(&self, required: &Proposition) -> bool {
        self.exact_index().conjuncts.contains_key(required)
    }

    /// Whether a fact of the list directly contradicts `fact`, as
    /// `exact_facts_directly_conflict(available, fact)` decides for some
    /// fact `available` of the list. That decision splits both sides at
    /// conjunctions and pairs leaves `a` (of the listed fact) and `l` (of
    /// `fact`) exactly when `a` is `ConditionIs(c, !v)` for `l` written
    /// `ConditionIs(c, v)`, `a` is `Not(l)`, or `l` is `Not(a)` for an `a`
    /// that is itself neither a negation nor a conjunction; this looks each
    /// such `a` up among the listed facts' conjuncts.
    pub(crate) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        let index = self.exact_index();
        let mut conflict = false;
        conjunction_nodes(fact, &mut |leaf| {
            if conflict || matches!(leaf, Proposition::And(_, _)) {
                return;
            }
            let negated = Proposition::Not(Box::new(leaf.clone()));
            let opposite = match leaf {
                Proposition::ConditionIs(condition, value) => {
                    Some(Proposition::ConditionIs(condition.clone(), !value))
                }
                Proposition::Not(body)
                    if !matches!(body.as_ref(), Proposition::Not(_) | Proposition::And(_, _)) =>
                {
                    Some(body.as_ref().clone())
                }
                _ => None,
            };
            conflict = index.conjuncts.contains_key(&negated)
                || opposite.is_some_and(|opposite| index.conjuncts.contains_key(&opposite));
        });
        conflict
    }

    /// The facts an automatic store transport may move, in order: every
    /// fact for which `c_condition_fact_has_memory` holds or that
    /// `proposition_mentions_registered_load_variable` may accept. The
    /// caller applies its exact test to each.
    pub(crate) fn transport_candidates(&self) -> Vec<Proposition> {
        let mut transport = self
            .transport
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let candidates = transport.get_or_insert_with(TransportCandidates::default);
        candidates.refresh(&self.facts, self.next);
        candidates
            .candidates
            .iter()
            .filter_map(|sequence| self.facts.get(sequence))
            .map(|fact| crate::kernel::clone_proposition_iteratively(fact))
            .collect()
    }

    /// Builds the exact index and evaluates transport candidacy for every
    /// fact now, so copies made from this list before they change share
    /// both instead of each building its own.
    pub(crate) fn prepare_indexes(&self) {
        self.exact_index();
        let mut transport = self
            .transport
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        transport
            .get_or_insert_with(TransportCandidates::default)
            .refresh(&self.facts, self.next);
    }

    fn exact_index(&self) -> &ExactFactIndex {
        self.exact.get_or_init(|| {
            let mut index = ExactFactIndex::default();
            for (sequence, fact) in &self.facts {
                index.insert(*sequence, fact);
            }
            index
        })
    }

    /// The indexes a mutation updates: each one built so far, unshared.
    fn begin_mutation(&mut self) -> (Option<ExactFactIndex>, Option<TransportCandidates>) {
        self.flat = Arc::new(OnceLock::new());
        let exact = std::mem::take(&mut self.exact);
        let exact = Arc::try_unwrap(exact)
            .map(|cell| cell.into_inner())
            .unwrap_or_else(|shared| shared.get().cloned());
        let transport = std::mem::take(&mut self.transport);
        let transport = match Arc::try_unwrap(transport) {
            Ok(transport) => transport
                .into_inner()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            Err(shared) => shared
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .clone(),
        };
        (exact, transport)
    }

    fn end_mutation(
        &mut self,
        exact: Option<ExactFactIndex>,
        transport: Option<TransportCandidates>,
    ) {
        let cell = OnceLock::new();
        if let Some(exact) = exact {
            let _ = cell.set(exact);
        }
        self.exact = Arc::new(cell);
        self.transport = Arc::new(Mutex::new(transport));
    }

    pub(crate) fn push(&mut self, fact: Proposition) {
        self.extend(std::iter::once(fact));
    }

    pub(crate) fn extend(&mut self, facts: impl IntoIterator<Item = Proposition>) {
        let mut facts = facts.into_iter().peekable();
        if facts.peek().is_none() {
            return;
        }
        let (mut exact, transport) = self.begin_mutation();
        for fact in facts {
            let fact = Arc::new(fact);
            if let Some(index) = exact.as_mut() {
                index.insert(self.next, &fact);
            }
            self.facts.insert(self.next, fact);
            self.next += 1;
        }
        self.end_mutation(exact, transport);
    }

    /// Keeps the facts `keep` accepts, in order. The built context survives
    /// only when every removed fact lies after its prefix.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&Proposition) -> bool) {
        let removed = self
            .facts
            .iter()
            .filter(|(_, fact)| !keep(fact))
            .map(|(sequence, _)| *sequence)
            .collect::<Vec<_>>();
        self.remove_sequences(&removed);
    }

    /// Removes every copy of `fact`, found through the index: what
    /// `retain(|available| available != fact)` keeps.
    pub(crate) fn remove_all(&mut self, fact: &Proposition) {
        let removed = self
            .exact_index()
            .by_fact
            .get(fact)
            .map(|sequences| sequences.iter().copied().collect::<Vec<_>>())
            .unwrap_or_default();
        self.remove_sequences(&removed);
    }

    fn remove_sequences(&mut self, removed: &[u64]) {
        let Some(first_removed) = removed.iter().copied().min() else {
            return;
        };
        let (mut exact, mut transport) = self.begin_mutation();
        for sequence in removed {
            if let Some(fact) = self.facts.remove(sequence) {
                if let Some(index) = exact.as_mut() {
                    index.remove(*sequence, &fact);
                }
                if let Some(transport) = transport.as_mut() {
                    transport.remove(*sequence);
                }
            }
        }
        self.end_mutation(exact, transport);
        self.invalidate_from(first_removed);
    }

    /// Replaces a transported fact's source with its target at the source's
    /// position: downstream premise selection is order-sensitive, so
    /// rewriting must not reorder the working set. Kept out of line, like
    /// the by-value proposition handling of the shared transition
    /// dispatcher it serves; the expansion small-stack regression pins that
    /// boundary.
    #[inline(never)]
    pub(crate) fn replace_fact_in_place(&mut self, source: &Proposition, target: &Proposition) {
        let position = self
            .exact_index()
            .by_fact
            .get(source)
            .and_then(|sequences| sequences.get_min().copied());
        if let Some(sequence) = position {
            if self.contains(target) {
                self.remove_sequences(&[sequence]);
            } else {
                let (mut exact, mut transport) = self.begin_mutation();
                let target = Arc::new(target.clone());
                if let Some(previous) = self.facts.insert(sequence, target.clone())
                    && let Some(index) = exact.as_mut()
                {
                    index.remove(sequence, &previous);
                    index.insert(sequence, &target);
                }
                if let Some(transport) = transport.as_mut() {
                    transport.replace(sequence);
                }
                self.end_mutation(exact, transport);
                self.invalidate_from(sequence);
            }
        } else if !self.contains(target) {
            self.push(target.clone());
        }
    }

    fn invalidate_from(&mut self, sequence: u64) {
        self.built.invalidate_from(sequence);
        self.transport_built.invalidate_from(sequence);
        if self
            .source
            .as_ref()
            .is_some_and(|(_, through)| *through > sequence)
        {
            self.source = None;
        }
    }
}

impl PropositionSource for PureFactList {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.iter()
    }

    fn pure_context(&self) -> PureFactContext {
        self.context()
    }

    fn indexed_proof_facts(&self) -> ProofFacts {
        self.proof_facts()
    }
}

/// Debug builds only: `CLICK_DEBUG_CHECK_FACT_LISTS=1` checks every list
/// extension against the copy it replaces, for corpus validation.
#[cfg(debug_assertions)]
fn fact_list_check_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("CLICK_DEBUG_CHECK_FACT_LISTS").is_some_and(|value| value == "1")
    })
}

#[cfg(test)]
thread_local! {
    static FLAT_FACT_COPIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static FACT_INDEX_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TRANSPORT_CANDIDATE_TESTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Counts, in test builds, the facts copied out of a list into a flat
/// vector: a caller that reads the whole list as a slice.
fn count_flat_fact_copies(_entries: usize) {
    #[cfg(test)]
    FLAT_FACT_COPIES.with(|count| count.set(count.get() + _entries));
}

/// Counts, in test builds, the facts filed in or withdrawn from a list's
/// exact index.
fn count_fact_index_entries(_entries: usize) {
    #[cfg(test)]
    FACT_INDEX_ENTRIES.with(|count| count.set(count.get() + _entries));
}

/// Counts, in test builds, the facts tested for transport candidacy.
fn count_transport_candidate_tests(_entries: usize) {
    #[cfg(test)]
    TRANSPORT_CANDIDATE_TESTS.with(|count| count.set(count.get() + _entries));
}

/// The list entries copied flat, indexed, and tested for transport on this
/// thread so far.
#[cfg(test)]
pub(crate) fn fact_list_entry_counts() -> [usize; 3] {
    [
        FLAT_FACT_COPIES.with(std::cell::Cell::get),
        FACT_INDEX_ENTRIES.with(std::cell::Cell::get),
        TRANSPORT_CANDIDATE_TESTS.with(std::cell::Cell::get),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, ConditionTerm, Variable};

    fn condition(variable: u64) -> ConditionTerm {
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(variable))),
            Box::new(Bitvector32Term::Constant(0)),
        )
    }

    fn predicate(name: &str) -> Proposition {
        Proposition::Predicate {
            name: name.to_string(),
            arguments: Vec::new(),
        }
    }

    /// Leaves and small compounds of every shape the direct-conflict rule
    /// distinguishes: conditions of both values, negations of conditions,
    /// of negations and of conjunctions, other facts and their negations,
    /// and conjunctions of those.
    fn shapes() -> Vec<Proposition> {
        let not = |fact: Proposition| Proposition::Not(Box::new(fact));
        let and = |left: Proposition, right: Proposition| {
            Proposition::And(Box::new(left), Box::new(right))
        };
        let mut leaves = Vec::new();
        for variable in [1, 2] {
            for value in [true, false] {
                let fact = Proposition::ConditionIs(condition(variable), value);
                leaves.push(fact.clone());
                leaves.push(not(fact.clone()));
                leaves.push(not(not(fact)));
            }
        }
        leaves.push(predicate("p"));
        leaves.push(not(predicate("p")));
        leaves.push(not(not(predicate("p"))));
        leaves.push(predicate("q"));
        let mut shapes = leaves.clone();
        for (index, left) in leaves.iter().enumerate() {
            for right in leaves.iter().skip(index).step_by(3) {
                shapes.push(and(left.clone(), right.clone()));
                shapes.push(not(and(left.clone(), right.clone())));
            }
        }
        shapes
    }

    #[test]
    fn indexed_conflicts_agree_with_the_pairwise_rule() {
        let shapes = shapes();
        for listed in shapes.chunks(5) {
            let list = PureFactList::from(listed.to_vec());
            for fact in &shapes {
                let expected = listed.iter().any(|available| {
                    crate::kernel::proof::fact_reasoning::exact_facts_directly_conflict(
                        available, fact,
                    )
                });
                assert_eq!(
                    list.directly_conflicts_with(fact),
                    expected,
                    "{fact:?} against {listed:?}"
                );
            }
        }
    }

    #[test]
    fn indexed_membership_follows_every_mutation() {
        let shapes = shapes();
        let mut list = PureFactList::from(shapes[..12].to_vec());
        let mut flat = shapes[..12].to_vec();
        let check = |list: &PureFactList, flat: &[Proposition]| {
            assert!(list.iter().eq(flat.iter()), "order");
            for fact in &shapes {
                assert_eq!(list.contains(fact), flat.contains(fact), "{fact:?}");
                let conjunct = flat.iter().any(|available| {
                    let mut found = false;
                    conjunction_nodes(available, &mut |node| found |= node == fact);
                    found
                });
                assert_eq!(list.has_exact_conjunct(fact), conjunct, "{fact:?}");
            }
        };
        check(&list, &flat);
        let copy = list.clone();
        list.replace_fact_in_place(&shapes[3], &shapes[20]);
        let position = flat.iter().position(|fact| fact == &shapes[3]).unwrap();
        flat[position] = shapes[20].clone();
        check(&list, &flat);
        list.replace_fact_in_place(&shapes[4], &shapes[20]);
        flat.retain(|fact| fact != &shapes[4]);
        check(&list, &flat);
        list.remove_all(&shapes[5]);
        flat.retain(|fact| fact != &shapes[5]);
        check(&list, &flat);
        list.extend(shapes[30..34].iter().cloned());
        flat.extend(shapes[30..34].iter().cloned());
        check(&list, &flat);
        list.retain(|fact| !matches!(fact, Proposition::Predicate { .. }));
        flat.retain(|fact| !matches!(fact, Proposition::Predicate { .. }));
        check(&list, &flat);
        assert_eq!(list.to_vec(), flat);
        // The copy taken before the mutations keeps its facts and indexes.
        check(&copy, &shapes[..12]);
    }

    #[test]
    fn transport_candidates_follow_replacements() {
        let list = PureFactList::from(vec![predicate("p"), predicate("q")]);
        assert!(list.transport_candidates().is_empty());
        let mut list = list;
        list.push(predicate("r"));
        assert!(list.transport_candidates().is_empty());
        list.replace_fact_in_place(&predicate("q"), &predicate("s"));
        assert!(list.transport_candidates().is_empty());
        assert_eq!(
            list.iter().cloned().collect::<Vec<_>>(),
            vec![predicate("p"), predicate("s"), predicate("r")]
        );
    }
}
