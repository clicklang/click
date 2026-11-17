//! Ordered views and strict syntax selection over the store's shared facts.
use super::*;

/// Intern conjunction structure by child IDs. Atomic keys retain their exact
/// written syntax; constructing or querying a conjunction visits its syntax
/// once instead of cloning every nested subtree into a structural map key.
#[derive(Clone, Default)]
struct WrittenSyntax {
    atoms: PersistentMap<Arc<Proposition>, u64>,
    pairs: PersistentMap<(u64, u64), u64>,
    next: u64,
}

impl WrittenSyntax {
    fn admit(&mut self, fact: &Arc<Proposition>) {
        if !matches!(fact.as_ref(), Proposition::And(..)) {
            if self.atoms.get(fact.as_ref()).is_none() {
                let id = self.next;
                self.next += 1;
                self.atoms = self.atoms.with_inserted(fact.clone(), id);
            }
            return;
        }
        enum Task<'a> {
            Read(&'a Proposition),
            Pair,
        }
        let mut tasks = vec![Task::Read(fact)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Read(Proposition::And(left, right)) => {
                    tasks.extend([Task::Pair, Task::Read(right), Task::Read(left)]);
                }
                Task::Read(atom) => {
                    let id = match self.atoms.get(atom) {
                        Some(id) => *id,
                        None => {
                            let id = self.next;
                            self.next += 1;
                            self.atoms = self.atoms.with_inserted(
                                Arc::new(crate::kernel::clone_proposition_iteratively(atom)),
                                id,
                            );
                            id
                        }
                    };
                    values.push(id);
                }
                Task::Pair => {
                    let right = values.pop().expect("right conjunction operand");
                    let left = values.pop().expect("left conjunction operand");
                    let key = (left, right);
                    let id = match self.pairs.get(&key) {
                        Some(id) => *id,
                        None => {
                            let id = self.next;
                            self.next += 1;
                            self.pairs = self.pairs.with_inserted(key, id);
                            id
                        }
                    };
                    values.push(id);
                }
            }
        }
    }

    fn contains(&self, fact: &Proposition) -> bool {
        enum Task<'a> {
            Read(&'a Proposition),
            Pair,
        }
        let mut tasks = vec![Task::Read(fact)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Read(Proposition::And(left, right)) => {
                    tasks.extend([Task::Pair, Task::Read(right), Task::Read(left)])
                }
                Task::Read(atom) => match self.atoms.get(atom) {
                    Some(id) => values.push(*id),
                    None => return false,
                },
                Task::Pair => {
                    let right = values.pop().expect("right conjunction operand");
                    let left = values.pop().expect("left conjunction operand");
                    match self.pairs.get(&(left, right)) {
                        Some(id) => values.push(*id),
                        None => return false,
                    }
                }
            }
        }
        true
    }
}

/// These maps are order indexes: all values reference the same proposition
/// objects as the semantic indexes. `first` supplies set presentation, while
/// `entries` additionally retains repeated explicitly supplied occurrences.
#[derive(Clone, Default)]
pub(super) struct FactPresentation {
    entries: PersistentMap<i128, Arc<Proposition>>,
    first: PersistentMap<i128, Arc<Proposition>>,
    locations: imbl::OrdMap<Arc<Proposition>, i128>,
    duplicates: imbl::OrdMap<Arc<Proposition>, imbl::OrdSet<i128>>,
    syntax: WrittenSyntax,
    next: i128,
}

impl FactPresentation {
    pub(super) fn get(&self, index: usize) -> Option<&Proposition> {
        self.entries.get_index(index).map(|(_, fact)| fact.as_ref())
    }
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(super) fn iter(&self) -> impl DoubleEndedIterator<Item = &Proposition> + ExactSizeIterator {
        self.entries.values().map(Arc::as_ref)
    }
    pub(super) fn shared_unique_iter(&self) -> impl Iterator<Item = Arc<Proposition>> + '_ {
        self.first.values().cloned()
    }
    pub(super) fn unique_iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Proposition> + ExactSizeIterator {
        self.first.values().map(Arc::as_ref)
    }
    pub(super) fn contains(&self, fact: &Proposition) -> bool {
        self.locations.contains_key(fact)
    }
    pub(super) fn has_conjunct(&self, fact: &Proposition) -> bool {
        self.syntax.contains(fact)
    }
    pub(super) fn unique(&self) -> Self {
        Self {
            entries: self.first.clone(),
            duplicates: imbl::OrdMap::default(),
            ..self.clone()
        }
    }
    pub(super) fn append(&mut self, fact: Arc<Proposition>) {
        let sequence = self.next;
        self.next += 1;
        if self.locations.contains_key(fact.as_ref()) {
            self.duplicates
                .entry(fact.clone())
                .or_default()
                .insert(sequence);
        } else {
            self.syntax.admit(&fact);
            self.locations.insert(fact.clone(), sequence);
            self.first = self.first.with_inserted(sequence, fact.clone());
        }
        self.entries = self.entries.with_inserted(sequence, fact);
    }
    /// A batch is presented once per proposition, newest batch first. Only
    /// the named batch's locations change; unrelated facts stay shared.
    pub(super) fn prioritize(&mut self, facts: impl IntoIterator<Item = Arc<Proposition>>) {
        let mut seen = BTreeSet::new();
        let mut prefix = Vec::new();
        for fact in facts {
            if !seen.insert(fact.clone()) {
                continue;
            }
            if let Some(sequence) = self.locations.remove(fact.as_ref()) {
                self.entries = self.entries.without_key(&sequence);
                self.first = self.first.without_key(&sequence);
                if let Some(duplicates) = self.duplicates.remove(fact.as_ref()) {
                    for sequence in duplicates {
                        self.entries = self.entries.without_key(&sequence);
                    }
                }
            } else {
                self.syntax.admit(&fact);
            }
            prefix.push(fact);
        }
        let first = self
            .entries
            .iter()
            .next()
            .map_or(self.next, |(sequence, _)| *sequence);
        let start = first - prefix.len() as i128;
        for (offset, fact) in prefix.into_iter().enumerate() {
            let sequence = start + offset as i128;
            self.locations.insert(fact.clone(), sequence);
            self.first = self.first.with_inserted(sequence, fact.clone());
            self.entries = self.entries.with_inserted(sequence, fact);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn atom(name: &str) -> Arc<Proposition> {
        Arc::new(Proposition::Predicate {
            name: name.to_string(),
            arguments: Vec::new(),
        })
    }
    #[test]
    fn occurrence_and_unique_views_share_values_and_keep_order() {
        let (a, b, c) = (atom("a"), atom("b"), atom("c"));
        let mut root = FactPresentation::default();
        root.append(a.clone());
        root.append(a.clone());
        root.append(b.clone());
        assert_eq!(
            root.iter().collect::<Vec<_>>(),
            vec![a.as_ref(), a.as_ref(), b.as_ref()]
        );
        assert_eq!(
            root.unique_iter().collect::<Vec<_>>(),
            vec![a.as_ref(), b.as_ref()]
        );
        let mut child = root.unique();
        child.prioritize([b.clone(), c.clone(), b.clone()]);
        assert_eq!(
            child.iter().collect::<Vec<_>>(),
            vec![b.as_ref(), c.as_ref(), a.as_ref()]
        );
        child.append(a.clone());
        assert_eq!(
            child.iter().collect::<Vec<_>>(),
            vec![b.as_ref(), c.as_ref(), a.as_ref(), a.as_ref()]
        );
        for (index, fact) in child.iter().enumerate() {
            assert_eq!(child.get(index), Some(fact));
        }
        assert!(child.get(child.len()).is_none());
        assert_eq!(root.len(), 3);
    }
    #[test]
    fn strict_conjunction_membership_requires_the_written_shape() {
        let (a, b, c) = (atom("a"), atom("b"), atom("c"));
        let pair = Arc::new(Proposition::And(
            Box::new(a.as_ref().clone()),
            Box::new(b.as_ref().clone()),
        ));
        let mut facts = FactPresentation::default();
        facts.append(a.clone());
        facts.append(b.clone());
        assert!(!facts.has_conjunct(&pair));
        facts.append(Arc::new(Proposition::And(
            Box::new(pair.as_ref().clone()),
            Box::new(c.as_ref().clone()),
        )));
        assert!(facts.has_conjunct(&pair));
        assert!(facts.has_conjunct(&a));
        assert!(!facts.has_conjunct(&Proposition::And(
            Box::new(b.as_ref().clone()),
            Box::new(a.as_ref().clone())
        )));
        assert!(!facts.has_conjunct(&Proposition::And(
            Box::new(a.as_ref().clone()),
            Box::new(Proposition::And(
                Box::new(b.as_ref().clone()),
                Box::new(c.as_ref().clone())
            ))
        )));
    }
    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/facts/presentation/tests.rs");
    }
}
