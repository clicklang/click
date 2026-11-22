//! Ordered views of the kernel's pure fact store. This type owns no fact
//! collection, syntax index, reasoning context, or prefix synchronization.
use crate::kernel::proof::{PropositionSource, PureFactStore};
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{Proposition, PureFactContext};

#[derive(Clone, Default)]
pub(crate) struct PureFactList {
    facts: PureFactStore,
    statement_view: bool,
}

impl std::fmt::Debug for PureFactList {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
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
        Self::from_source(&facts)
    }
}
impl FromIterator<Proposition> for PureFactList {
    fn from_iter<I: IntoIterator<Item = Proposition>>(facts: I) -> Self {
        let mut list = Self::default();
        list.extend(facts);
        list
    }
}
pub(crate) type PureFactIter<'a> = Box<dyn Iterator<Item = &'a Proposition> + 'a>;
impl<'a> IntoIterator for &'a PureFactList {
    type Item = &'a Proposition;
    type IntoIter = PureFactIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl PureFactList {
    pub(crate) fn from_source(source: &(impl PropositionSource + ?Sized)) -> Self {
        Self {
            facts: source.ordered_fact_store(),
            statement_view: false,
        }
    }
    pub(crate) fn from_store(source: &PureFactStore) -> Self {
        Self::from_source(source)
    }
    pub(crate) fn store(&self) -> &PureFactStore {
        &self.facts
    }
    pub(crate) fn for_statement(facts: Vec<Proposition>, base: &PureFactStore) -> Self {
        Self {
            facts: base.statement_view(facts),
            statement_view: true,
        }
    }
    pub(crate) fn into_store(self) -> PureFactStore {
        self.facts
    }
    /// A checked statement already holds a fork of the incoming graph,
    /// including the outcome's facts. Other callers may supply a separate
    /// context for prerequisite checking.
    pub(crate) fn is_statement_view(&self) -> bool {
        self.statement_view
    }
    // Keep occurrence order when source provenance addresses producer positions.
    // `from_store` intentionally offers a unique-fact presentation instead.
    pub(crate) fn from_produced_store(store: PureFactStore) -> Self {
        Self {
            facts: store,
            statement_view: false,
        }
    }
    pub(crate) fn context(&self) -> PureFactContext {
        self.facts.assumptions().clone()
    }
    pub(crate) fn len(&self) -> usize {
        self.facts.len()
    }
    pub(crate) fn get(&self, index: usize) -> Option<&Proposition> {
        self.facts.occurrence(index)
    }
    pub(crate) fn iter(&self) -> PureFactIter<'_> {
        Box::new(self.facts.occurrences())
    }
    pub(crate) fn to_vec(&self) -> Vec<Proposition> {
        count_flat_fact_copies(self.len());
        self.iter()
            .map(crate::kernel::clone_proposition_iteratively)
            .collect()
    }
    pub(crate) fn into_vec(self) -> Vec<Proposition> {
        self.to_vec()
    }
    pub(crate) fn contains(&self, fact: &Proposition) -> bool {
        self.facts.contains_presented(fact)
    }
    pub(crate) fn has_exact_conjunct(&self, fact: &Proposition) -> bool {
        self.facts.has_stated_conjunct(fact)
    }
    pub(crate) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        let mut pending = vec![fact];
        while let Some(leaf) = pending.pop() {
            if let Proposition::And(left, right) = leaf {
                pending.extend([right.as_ref(), left.as_ref()]);
                continue;
            }
            let negated = Proposition::Not(Box::new(leaf.clone()));
            let opposite = match leaf {
                Proposition::ConditionIs(condition, value) => {
                    Some(Proposition::condition_is(condition.clone(), !value))
                }
                Proposition::Not(body)
                    if !matches!(body.as_ref(), Proposition::Not(_) | Proposition::And(_, _)) =>
                {
                    Some(body.as_ref().clone())
                }
                _ => None,
            };
            if self.has_exact_conjunct(&negated)
                || opposite.is_some_and(|fact| self.has_exact_conjunct(&fact))
            {
                return true;
            }
        }
        false
    }
    pub(crate) fn push(&mut self, fact: Proposition) {
        self.extend(std::iter::once(fact));
    }
    pub(crate) fn extend(&mut self, facts: impl IntoIterator<Item = Proposition>) {
        for fact in facts {
            self.facts = self.facts.with_list_fact(fact);
        }
    }
    pub(crate) fn retain(&mut self, keep: impl FnMut(&Proposition) -> bool) {
        self.facts = self.facts.retaining(keep);
    }
    /// Common facts from distinct outcomes extend the graph at the fork.
    pub(crate) fn retain_from(&mut self, base: &Self, mut keep: impl FnMut(&Proposition) -> bool) {
        if self.statement_view {
            let selected = self
                .iter()
                .filter(|fact| keep(fact))
                .cloned()
                .collect::<Vec<_>>();
            if selected.len() != self.len() {
                self.facts = base.facts.statement_view(selected);
            }
        } else {
            self.retain(keep);
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
    fn exact_available(&self, required: &Proposition) -> bool {
        self.has_exact_conjunct(required)
    }
    fn fact_store(&self) -> PureFactStore {
        self.store().clone()
    }
    fn ordered_fact_store(&self) -> PureFactStore {
        self.facts.clone()
    }
}
#[cfg(test)]
thread_local! { static FLAT_FACT_COPIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
fn count_flat_fact_copies(_entries: usize) {
    #[cfg(test)]
    FLAT_FACT_COPIES.with(|count| count.set(count.get() + _entries));
}
#[cfg(test)]
pub(crate) fn fact_list_entry_counts() -> [usize; 2] {
    [FLAT_FACT_COPIES.with(std::cell::Cell::get), 0]
}
#[cfg(test)]
fn conjunction_nodes(fact: &Proposition, visit: &mut impl FnMut(&Proposition)) {
    let mut pending = vec![fact];
    while let Some(node) = pending.pop() {
        visit(node);
        if let Proposition::And(left, right) = node {
            pending.extend([right.as_ref(), left.as_ref()]);
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ConditionTerm, MachineTerm, Variable};

    fn condition(variable: u64) -> ConditionTerm {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(variable))),
            right: Box::new(MachineTerm::constant(0)),
        }
    }

    #[test]
    fn shared_statement_facts_preserve_scope_order_and_context() {
        let original = Proposition::condition_is(condition(400), true);
        let left = Proposition::condition_is(condition(401), true);
        let right = Proposition::condition_is(condition(402), true);
        let pair = Proposition::And(Box::new(left.clone()), Box::new(right.clone()));
        let root = PureFactStore::from_ordered(std::slice::from_ref(&original));
        let branch = root.with_kernel_checked_fact(pair.clone());
        let view = PureFactList::from_produced_store(branch.clone());
        assert!(view.facts.shares_exact_index_with(&branch));
        assert!(view.fact_store().shares_exact_index_with(&branch));
        assert!(
            view.context()
                .shares_fact_storage_with(branch.assumptions())
        );
        assert!(view.contains(&pair));
        assert!(!view.contains(&left));
        assert!(view.has_exact_conjunct(&left));
        assert!(view.has_exact_conjunct(&pair));
        assert!(!PureFactList::from_store(&root).has_exact_conjunct(&left));
        assert_eq!(
            view.iter().cloned().collect::<Vec<_>>(),
            vec![original.clone(), pair.clone()]
        );
        let published = root.with_statement_facts(vec![left.clone(), pair.clone()]);
        assert_eq!(
            published.propositions().cloned().collect::<Vec<_>>(),
            vec![left, pair, original]
        );
    }

    #[test]
    fn statement_store_retains_producer_context_and_extends_without_surface_indexes() {
        let original = Proposition::condition_is(condition(410), true);
        let added = Proposition::condition_is(condition(411), true);
        let base = PureFactStore::from_ordered(std::slice::from_ref(&original));
        let context = base.assumptions();
        let mut view = PureFactList::for_statement(vec![original.clone()], &base);
        assert!(view.context().shares_fact_storage_with(context));
        view.push(added.clone());
        assert!(view.facts.contains_presented(&added));
        assert_eq!(
            view.iter().cloned().collect::<Vec<_>>(),
            vec![original, added.clone()]
        );
        assert!(view.context().contains_assumed_exact(&added));
        assert!(!context.contains_assumed_exact(&added));
    }

    #[test]
    fn indexed_initial_facts_retain_their_cached_context() {
        let original = Proposition::condition_is(condition(10), true);
        let added = Proposition::condition_is(condition(11), true);
        let mut list = PureFactList::from(vec![original.clone()]);
        let cached = list.context();
        let indexed = list.fact_store();
        assert!(indexed.assumptions().shares_fact_storage_with(&cached));
        list.push(added.clone());
        let extended = list.context();
        let indexed_extended = list.fact_store();
        assert!(
            indexed_extended
                .assumptions()
                .shares_fact_storage_with(&extended)
        );
        assert!(indexed_extended.contains(&added));
        assert!(indexed.contains(&original));
        assert!(!indexed.contains(&added));
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
                let fact = Proposition::condition_is(condition(variable), value);
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
    fn indexed_conflicts_agree_with_the_pairwise_rule_for_published_facts() {
        let shapes = shapes();
        for listed in shapes.chunks(5) {
            let list = PureFactList::from(listed.to_vec());
            for fact in &shapes {
                // Propagation publishes ordinary facts beyond the input list.
                // The pairwise rule ranges over that complete presentation.
                let expected = list.iter().any(|available| {
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
    fn propagated_double_negation_has_an_exact_conflict_without_explosion() {
        let positive = Proposition::condition_is(condition(1), true);
        let negative = Proposition::condition_is(condition(1), false);
        let source = Proposition::Not(Box::new(Proposition::Not(Box::new(negative.clone()))));
        let list = PureFactList::from(vec![source]);
        assert!(list.contains(&negative));
        assert!(list.directly_conflicts_with(&positive));
        assert!(!list.directly_conflicts_with(&Proposition::condition_is(condition(2), true)));
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
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../scaling_tests/surface/pure_fact_list/store_sharing_tests.rs");
}
