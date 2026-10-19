use super::*;
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::Mutex;

type Pair = (u64, u64);

#[cfg(test)]
thread_local! { static SOURCE_VISITS: Cell<usize> = const { Cell::new(0) }; }

fn source_visit() {
    #[cfg(test)]
    SOURCE_VISITS.with(|visits| visits.set(visits.get() + 1));
}

/// Disposable, persistent index over exact stated separation authority. Each
/// context fork owns its cache lock; graph hypotheses never cross branches.
#[derive(Default)]
pub(in crate::kernel) struct SeparatedAddressIndex(Mutex<Option<Box<Index>>>);

#[derive(Clone, Debug, Default)]
struct Index {
    graph: Option<EqualityGraph>,
    sources: PersistentMap<Proposition, (Pointer, Pointer)>,
    pairs: PersistentMap<Pair, PersistentSet<Proposition>>,
    incident: PersistentMap<u64, PersistentSet<Pair>>,
}

impl Clone for SeparatedAddressIndex {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.0.lock().expect("separation index").clone()))
    }
}

impl std::fmt::Debug for SeparatedAddressIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SeparatedAddressIndex")
            .finish_non_exhaustive()
    }
}

fn pair(left: u64, right: u64) -> Pair {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

impl Index {
    fn attach(&mut self, key: Pair, fact: Proposition) {
        source_visit();
        self.pairs = self.pairs.with_inserted(
            key,
            self.pairs
                .get(&key)
                .cloned()
                .unwrap_or_default()
                .with_value(fact),
        );
        for endpoint in [key.0, key.1] {
            self.incident = self.incident.with_inserted(
                endpoint,
                self.incident
                    .get(&endpoint)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(key),
            );
        }
    }

    fn detach_pair(&mut self, key: Pair) {
        self.pairs = self.pairs.without_key(&key);
        for endpoint in [key.0, key.1] {
            if let Some(incident) = self.incident.get(&endpoint) {
                let remaining = incident.without_value(&key);
                self.incident = if remaining.is_empty() {
                    self.incident.without_key(&endpoint)
                } else {
                    self.incident.with_inserted(endpoint, remaining)
                };
            }
        }
    }

    fn synchronize(&mut self, graph: &EqualityGraph) {
        let Some(previous) = &self.graph else {
            self.graph = Some(graph.clone());
            return;
        };
        if let Some(merges) = graph.address_merges_since(previous) {
            for merge in merges {
                crate::instrumentation::record_deterministic_work(1);
                let incident = self.incident.get(&merge.moved).cloned().unwrap_or_default();
                for old in incident.iter() {
                    let facts = self.pairs.get(old).cloned().unwrap_or_default();
                    self.detach_pair(*old);
                    let replace = |id| if id == merge.moved { merge.kept } else { id };
                    let new = pair(replace(old.0), replace(old.1));
                    for fact in facts.iter() {
                        crate::instrumentation::record_deterministic_work(1);
                        self.attach(new, fact.clone());
                    }
                }
            }
        } else {
            // Withdrawal reconstructs the checked graph from its remaining
            // exact support. Class IDs from that lineage cannot be reused.
            self.pairs = Default::default();
            self.incident = Default::default();
            let sources = self.sources.clone();
            let registered = sources
                .iter()
                .filter_map(|(fact, (left, right))| {
                    crate::instrumentation::record_deterministic_work(1);
                    Some((
                        fact.clone(),
                        graph.address_class(left)?,
                        graph.address_class(right)?,
                    ))
                })
                .collect::<Vec<_>>();
            // Registration may join classes through producer definitions.
            // Attach only after every selected source has been registered.
            for (fact, left, right) in registered {
                self.attach(
                    pair(
                        graph.address_class_root(left),
                        graph.address_class_root(right),
                    ),
                    fact,
                );
            }
        }
        self.graph = Some(graph.clone());
    }
}

impl SeparatedAddressIndex {
    pub(in crate::kernel) fn adjust(
        &self,
        fact: &Proposition,
        left: Pointer,
        right: Pointer,
        insert: bool,
        graph: &EqualityGraph,
    ) {
        let mut cache = self.0.lock().expect("separation index");
        let index = cache.get_or_insert_with(Box::default);
        let (Some(left_class), Some(right_class)) =
            (graph.address_class(&left), graph.address_class(&right))
        else {
            return;
        };
        index.synchronize(graph);
        let key = pair(
            graph.address_class_root(left_class),
            graph.address_class_root(right_class),
        );
        if insert {
            index.sources = index.sources.with_inserted(fact.clone(), (left, right));
            index.attach(key, fact.clone());
        } else {
            index.sources = index.sources.without_key(fact);
            if let Some(facts) = index.pairs.get(&key) {
                let remaining = facts.without_value(fact);
                if remaining.is_empty() {
                    index.detach_pair(key);
                } else {
                    index.pairs = index.pairs.with_inserted(key, remaining);
                }
            }
        }
    }

    pub(in crate::kernel) fn candidates(
        &self,
        left: &Pointer,
        right: &Pointer,
        graph: &EqualityGraph,
    ) -> Vec<Proposition> {
        let mut cache = self.0.lock().expect("separation index");
        let Some(index) = cache.as_deref_mut() else {
            return Vec::new();
        };
        if index.sources.is_empty() {
            return Vec::new();
        }
        let (Some(left), Some(right)) = (graph.address_class(left), graph.address_class(right))
        else {
            return Vec::new();
        };
        index.synchronize(graph);
        let key = pair(
            graph.address_class_root(left),
            graph.address_class_root(right),
        );
        index
            .pairs
            .get(&key)
            .into_iter()
            .flat_map(|facts| {
                facts.iter().map(|fact| {
                    source_visit();
                    fact.clone()
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/separation_classes.rs");
}
