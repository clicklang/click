//! Shared range queries retain only the inputs they actually read. Graph
//! updates invalidate those queries and their parents; unrelated facts keep
//! the cached prefix. Persistent maps isolate cloned proof branches.
use super::*;
use crate::persistent::PersistentSet;
use std::sync::{Arc, Mutex};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel::difference_graph) enum Kind {
    Resolve,
    ModularResolve,
    Interval,
}
pub(in crate::kernel::difference_graph) type QueryKey = (Kind, Domain, u64);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel::difference_graph) enum Read {
    Operand(Domain, Key),
    Node(NodeId),
    Truncation,
    Query(QueryKey),
}
#[derive(Clone, Copy)]
pub(super) enum Answer {
    Resolve(Option<Affine>),
    Interval((i128, i128)),
}
#[derive(Clone)]
struct Entry {
    _root: crate::kernel::KernelTerm,
    answer: Answer,
    reads: Arc<[Read]>,
}
#[derive(Clone, Default)]
pub(super) struct Cache {
    entries: PersistentMap<QueryKey, Entry>,
    readers: PersistentMap<Read, PersistentSet<QueryKey>>,
}
#[derive(Default)]
pub(in crate::kernel::difference_graph) struct SharedQueryCache(Mutex<Cache>);
impl Clone for SharedQueryCache {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.0.lock().expect("range cache").clone()))
    }
}
impl SharedQueryCache {
    pub(super) fn lock(&self) -> std::sync::MutexGuard<'_, Cache> {
        self.0.lock().expect("range cache")
    }
    pub(in crate::kernel::difference_graph) fn invalidate(&self, input: Read) {
        let mut cache = self.lock();
        if !cache.readers.contains_key(&input) {
            return;
        }
        let mut pending = vec![input];
        while let Some(input) = pending.pop() {
            charge();
            let users = cache.readers.get(&input).cloned().unwrap_or_default();
            cache.readers.remove(&input);
            for user in users.iter() {
                charge();
                if let Some(entry) = cache.entries.get(user).cloned() {
                    cache.entries.remove(user);
                    for read in entry.reads.iter() {
                        let users = cache
                            .readers
                            .get(read)
                            .cloned()
                            .unwrap_or_default()
                            .without_value(user);
                        if users.is_empty() {
                            cache.readers.remove(read);
                        } else {
                            cache.readers.insert(read.clone(), users);
                        }
                    }
                    pending.push(Read::Query(*user));
                }
            }
        }
    }
}
impl Cache {
    pub(super) fn get(&self, key: &QueryKey) -> Option<Answer> {
        charge();
        self.entries.get(key).map(|entry| entry.answer)
    }
    pub(super) fn insert(
        &mut self,
        key: QueryKey,
        root: &crate::kernel::KernelTerm,
        answer: Answer,
        mut reads: Vec<Read>,
    ) {
        reads.sort();
        reads.dedup();
        for read in &reads {
            charge();
            let users = self
                .readers
                .get(read)
                .cloned()
                .unwrap_or_default()
                .with_value(key);
            self.readers.insert(read.clone(), users);
        }
        self.entries.insert(
            key,
            Entry {
                _root: root.clone(),
                answer,
                reads: reads.into(),
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use crate::kernel::{KernelTermImport, VerificationSession};

    fn variable(n: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(crate::kernel::Variable(998100 + n))
    }
    fn range(graph: &mut DifferenceGraph, value: &Bitvector32Term, lo: u32, hi: u32) {
        graph.assume_condition(
            &ConditionTerm::signed_less_equal(lo.into(), value.clone()),
            true,
        );
        graph.assume_condition(
            &ConditionTerm::signed_less_equal(value.clone(), hi.into()),
            true,
        );
    }
    fn interval(graph: &DifferenceGraph, term: &Bitvector32Term) -> (i128, i128) {
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, term)
            .unwrap();
        let actual = Query::new(graph).interval(Domain::Int32, V::Shared(&root));
        assert_eq!(actual, graph.term_interval(Domain::Int32, term));
        actual
    }
    #[test]
    fn cached_missing_nodes_and_tightened_bounds_follow_only_the_changed_branch() {
        let _session = VerificationSession::enter();
        let x = variable(0);
        let sum = Bitvector32Term::add(x.clone(), 1u32.into());
        let empty = DifferenceGraph::new();
        assert_eq!(interval(&empty, &sum), Domain::Int32.range());
        let mut parent = empty.clone();
        range(&mut parent, &x, 0, 10);
        assert_eq!(interval(&parent, &sum), (1, 11));
        assert_eq!(interval(&empty, &sum), Domain::Int32.range());
        let mut child = parent.clone();
        range(&mut child, &x, 0, 4);
        assert_eq!(interval(&child, &sum), (1, 5));
        assert_eq!(interval(&parent, &sum), (1, 11));
        child.assume_condition(&ConditionTerm::equal(x, 2u32.into()), true);
        assert_eq!(interval(&child, &sum), (3, 3));
    }
    #[test]
    fn cached_subtraction_tracks_new_and_tightened_edges() {
        let _session = VerificationSession::enter();
        let (x, y) = (variable(1), variable(2));
        let difference = Bitvector32Term::subtract(x.clone(), y.clone());
        let mut parent = DifferenceGraph::new();
        range(&mut parent, &x, 0, 100);
        range(&mut parent, &y, 0, 100);
        assert_eq!(interval(&parent, &difference), (-100, 100));
        let mut child = parent.clone();
        child.assume_condition(
            &ConditionTerm::signed_less_equal(x.clone(), y.clone()),
            true,
        );
        assert_eq!(interval(&child, &difference), (-100, 0));
        child.assume_condition(&ConditionTerm::signed_less_than(x, y), true);
        assert_eq!(interval(&child, &difference), (-100, -1));
        assert_eq!(interval(&parent, &difference), (-100, 100));
    }
    #[test]
    fn cached_structural_range_notices_an_explicit_compound_node() {
        let _session = VerificationSession::enter();
        let (x, y) = (variable(3), variable(4));
        let product = Bitvector32Term::multiply(x.clone(), y.clone());
        let mut graph = DifferenceGraph::new();
        range(&mut graph, &x, 0, 10);
        range(&mut graph, &y, 0, 10);
        assert_eq!(interval(&graph, &product), (0, 100));
        graph.assume_condition(
            &ConditionTerm::signed_less_equal(product.clone(), 7u32.into()),
            true,
        );
        assert_eq!(interval(&graph, &product), (0, 7));
    }
    #[test]
    fn cached_ranges_follow_truncated_neighbor_updates() {
        let _session = VerificationSession::enter();
        let source = variable(10);
        let leaves: Vec<_> = (0..EDGE_LIMIT + 4)
            .map(|i| variable(20 + i as u64))
            .collect();
        let mut parent = DifferenceGraph::new();
        range(&mut parent, &source, 0, 100);
        for leaf in &leaves {
            range(&mut parent, leaf, 0, 100);
            parent.assume_condition(
                &ConditionTerm::signed_less_equal(leaf.clone(), source.clone()),
                true,
            );
        }
        let term = Bitvector32Term::add(leaves.last().unwrap().clone(), 1u32.into());
        assert_eq!(interval(&parent, &term), (1, 101));
        let mut child = parent.clone();
        range(&mut child, &source, 0, 3);
        assert!(!child.truncated.is_empty());
        assert_eq!(interval(&child, &term), (1, 4));
        range(&mut child, &source, 0, 1);
        assert_eq!(interval(&child, &term), (1, 2));
        assert_eq!(interval(&parent, &term), (1, 101));
    }
    #[test]
    fn cached_wide_word_ranges_follow_the_other_signedness() {
        let _session = VerificationSession::enter();
        let x = variable(60);
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::UInt64, &x)
            .unwrap();
        let read = |graph: &DifferenceGraph| {
            let result = Query::new(graph).interval(Domain::UInt64, V::Shared(&root));
            assert_eq!(result, graph.term_interval(Domain::UInt64, &x));
            result
        };
        let mut parent = DifferenceGraph::new();
        assert_eq!(read(&parent), Domain::UInt64.range());
        parent.assume_condition(
            &ConditionTerm::int64_signed_less_equal(Bitvector32Term::int64_constant(0), x.clone()),
            true,
        );
        parent.assume_condition(
            &ConditionTerm::int64_signed_less_equal(x.clone(), Bitvector32Term::int64_constant(10)),
            true,
        );
        assert_eq!(read(&parent), (0, 10));
        let mut child = parent.clone();
        child.assume_condition(
            &ConditionTerm::int64_signed_less_equal(x.clone(), Bitvector32Term::int64_constant(4)),
            true,
        );
        assert_eq!(read(&child), (0, 4));
        assert_eq!(read(&parent), (0, 10));
    }
}
