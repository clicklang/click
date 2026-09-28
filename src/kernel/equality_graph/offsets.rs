//! Explicit offset equality and addition congruence inside the trusted graph.
//! Addition signatures use operand classes; parent-use indexes propagate late
//! merges. No arithmetic solving, cancellation, or injectivity runs here.
//! Shallow keys preserve widths, signedness, and machine-term snapshot identity.

use super::{MachineAtom, PointerOffsetTerm, Variable};
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Constant(i64),
    Variable(Variable),
    Add(u64, u64),
    Int32Scaled(MachineAtom, i64),
    Int64Scaled(MachineAtom, i64, bool),
}

#[derive(Clone, Default)]
pub(super) struct OffsetClasses {
    nodes: PersistentMap<Node, u64>,
    // Weight counts class members plus registered parent uses. Moving the
    // lighter side bounds both root depth and reindexing, including a class
    // with many addition parents repeatedly joined to fresh singleton terms.
    parents: PersistentMap<u64, u64>,
    weights: PersistentMap<u64, usize>,
    additions: PersistentMap<u64, (u64, u64)>,
    uses: PersistentMap<u64, PersistentSet<u64>>,
    signatures: PersistentMap<(u64, u64), u64>,
    addition_signatures: PersistentMap<u64, (u64, u64)>,
}

impl OffsetClasses {
    fn intern(&mut self, term: &PointerOffsetTerm) -> u64 {
        enum Work<'a> {
            Term(&'a PointerOffsetTerm),
            Add,
        }
        let mut pending = vec![Work::Term(term)];
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let node = match work {
                Work::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    Node::Add(left, right)
                }
                Work::Term(term) => match term {
                    PointerOffsetTerm::Constant(value) => Node::Constant(*value),
                    PointerOffsetTerm::Variable(variable) => Node::Variable(*variable),
                    PointerOffsetTerm::Add(left, right) => {
                        pending.push(Work::Add);
                        pending.push(Work::Term(right));
                        pending.push(Work::Term(left));
                        continue;
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width } => Node::Int32Scaled(
                        MachineAtom::new(
                            crate::kernel::MachineIntegerType::Int32,
                            crate::kernel::canonical_term(value),
                        ),
                        *byte_width,
                    ),
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => Node::Int64Scaled(
                        MachineAtom::new(
                            if *unsigned {
                                crate::kernel::MachineIntegerType::UInt64
                            } else {
                                crate::kernel::MachineIntegerType::Int64
                            },
                            crate::kernel::canonical_term(value),
                        ),
                        *byte_width,
                        *unsigned,
                    ),
                },
            };
            let id = match self.nodes.get(&node) {
                Some(id) => *id,
                None => {
                    let id = self.nodes.len() as u64;
                    let operands = match &node {
                        Node::Add(left, right) => Some((*left, *right)),
                        _ => None,
                    };
                    self.nodes.insert(node, id);
                    if let Some(operands) = operands {
                        self.register_addition(id, operands);
                    }
                    id
                }
            };
            values.push(id);
        }
        values.pop().expect("offset term")
    }

    fn root(&self, mut id: u64) -> u64 {
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match self.parents.get(&id) {
                Some(parent) => id = *parent,
                None => return id,
            }
        }
    }

    pub(super) fn are_equal(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left = self.intern(left);
        let right = self.intern(right);
        self.root(left) == self.root(right)
    }

    pub(super) fn add_equality(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left = self.intern(left);
        let right = self.intern(right);
        self.close(vec![(left, right)])
    }

    fn weight(&self, id: u64) -> usize {
        self.weights.get(&id).copied().unwrap_or(1)
    }

    fn register_addition(&mut self, id: u64, operands: (u64, u64)) {
        self.additions.insert(id, operands);
        for operand in [operands.0, operands.1] {
            let root = self.root(operand);
            let uses = self.uses.get(&root).cloned().unwrap_or_default();
            if !uses.contains(&id) {
                self.uses.insert(root, uses.with_value(id));
                self.weights.insert(root, self.weight(root) + 1);
            }
        }
        let mut pending = Vec::new();
        self.reindex_addition(id, &mut pending);
        self.close(pending);
    }

    fn reindex_addition(&mut self, id: u64, pending: &mut Vec<(u64, u64)>) {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(old) = self.addition_signatures.get(&id).copied()
            && self.signatures.get(&old) == Some(&id)
        {
            self.signatures.remove(&old);
        }
        let (left, right) = *self.additions.get(&id).expect("registered addition");
        let signature = (self.root(left), self.root(right));
        if let Some(other) = self.signatures.get(&signature) {
            if *other != id {
                pending.push((id, *other));
            }
        } else {
            self.signatures.insert(signature, id);
        }
        self.addition_signatures.insert(id, signature);
    }

    fn close(&mut self, mut pending: Vec<(u64, u64)>) -> bool {
        let mut changed = false;
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let mut kept = self.root(left);
            let mut moved = self.root(right);
            if kept == moved {
                continue;
            }
            if self.weight(kept) < self.weight(moved) {
                std::mem::swap(&mut kept, &mut moved);
            }
            let weight = self.weight(kept) + self.weight(moved);
            self.parents.insert(moved, kept);
            self.weights.remove(&moved);
            self.weights.insert(kept, weight);
            let moved_uses = self.uses.get(&moved).cloned().unwrap_or_default();
            let mut kept_uses = self.uses.get(&kept).cloned().unwrap_or_default();
            for id in moved_uses.iter() {
                crate::instrumentation::record_deterministic_work(1);
                kept_uses = kept_uses.with_value(*id);
                self.reindex_addition(*id, &mut pending);
            }
            self.uses.remove(&moved);
            if !kept_uses.is_empty() {
                self.uses.insert(kept, kept_uses);
            }
            changed = true;
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::super::EqualityGraph;
    use super::*;
    use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, Proposition, PureFactContext};

    fn var(id: u64) -> PointerOffsetTerm {
        PointerOffsetTerm::Variable(Variable(id))
    }
    fn equality(left: &PointerOffsetTerm, right: &PointerOffsetTerm) -> ConditionTerm {
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone())
    }

    fn add(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
        // Preserve nested applications rather than folding constants here.
        PointerOffsetTerm::Add(Box::new(left), Box::new(right))
    }

    #[test]
    fn addition_congruence_handles_both_operands_and_insertion_orders() {
        for equality_first in [false, true] {
            let mut graph = EqualityGraph::default();
            let (a, b, c, d) = (var(100), var(101), var(102), var(103));
            let (left, right) = (var(104), var(105));
            if equality_first {
                graph.add_offset_equality(&a, &b);
                graph.add_offset_equality(&c, &d);
            }
            graph.add_offset_equality(&add(a.clone(), c.clone()), &left);
            graph.add_offset_equality(&add(b.clone(), d.clone()), &right);
            if !equality_first {
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&a, &b);
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&c, &d);
            }
            // Query the aliases, not the addition trees: closure must already
            // have propagated the operand equalities into their parents.
            assert!(graph.are_offsets_equal(&left, &right));
        }
    }

    #[test]
    fn addition_congruence_propagates_nested_late_merges_and_is_branch_local() {
        let nested = |mut term| {
            for i in 0..64 {
                term = add(term, var(200 + i));
            }
            term
        };
        let (a, b, left, right) = (var(110), var(111), var(112), var(113));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&nested(a.clone()), &left);
        parent.add_offset_equality(&nested(b.clone()), &right);
        let sibling = parent.clone();
        let mut branch = parent.clone();
        branch.add_offset_equality(&a, &b);
        assert!(branch.are_offsets_equal(&left, &right));
        assert!(!parent.are_offsets_equal(&left, &right));
        assert!(!sibling.are_offsets_equal(&left, &right));
    }

    #[test]
    fn addition_congruence_does_not_cancel_or_equate_distinct_displacements() {
        let (a, b, c) = (var(120), var(121), var(122));
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&add(a.clone(), c.clone()), &add(b.clone(), c.clone()));
        assert!(!graph.are_offsets_equal(&a, &b));
        graph.add_offset_equality(&a, &b);
        assert!(!graph.are_offsets_equal(
            &add(a, PointerOffsetTerm::Constant(1)),
            &add(b, PointerOffsetTerm::Constant(2)),
        ));
    }

    #[test]
    fn addition_congruence_closes_cycles_without_generating_terms() {
        let a = var(130);
        let b = add(a.clone(), var(131));
        let c = add(b.clone(), var(131));
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_offsets_equal(&a, &c));
        graph.add_offset_equality(&a, &b);
        assert!(graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn addition_congruence_matches_a_small_exhaustive_closure() {
        // Independent oracle: repeatedly scan every pair of applications,
        // relabeling a flat partition. Production must instead use indexes.
        let mut terms = vec![var(300), var(301), var(302)];
        let mut applications = Vec::new();
        for left in 0..3 {
            for right in 0..3 {
                applications.push((terms.len(), left, right));
                terms.push(add(terms[left].clone(), terms[right].clone()));
            }
        }
        for left in 3..12 {
            applications.push((terms.len(), left, 0));
            terms.push(add(terms[left].clone(), terms[0].clone()));
        }
        fn join(classes: &mut [usize], left: usize, right: usize) -> bool {
            let (left, right) = (classes[left], classes[right]);
            if left == right {
                return false;
            }
            for class in classes {
                if *class == right {
                    *class = left;
                }
            }
            true
        }
        for seed in 1..=4u64 {
            let mut graph = EqualityGraph::default();
            for term in &terms {
                assert!(graph.are_offsets_equal(term, term));
            }
            let mut classes = (0..terms.len()).collect::<Vec<_>>();
            let mut random = seed;
            for _ in 0..8 {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let left = (random >> 32) as usize % terms.len();
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let right = (random >> 32) as usize % terms.len();
                graph.add_offset_equality(&terms[left], &terms[right]);
                join(&mut classes, left, right);
                loop {
                    let mut changed = false;
                    for &(a, al, ar) in &applications {
                        for &(b, bl, br) in &applications {
                            if classes[al] == classes[bl] && classes[ar] == classes[br] {
                                changed |= join(&mut classes, a, b);
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                for (a, left) in terms.iter().enumerate() {
                    for (b, right) in terms.iter().enumerate() {
                        assert_eq!(
                            graph.are_offsets_equal(left, right),
                            classes[a] == classes[b],
                            "seed={seed}, a={a}, b={b}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn addition_congruence_late_merge_work_scales_with_affected_parents() {
        for size in [16u64, 64, 256, 1024] {
            let mut graph = EqualityGraph::default();
            for i in 0..size {
                graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
                graph.add_offset_equality(&add(var(1), var(10 + i)), &var(20_000 + i));
            }
            let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    graph.add_offset_equality(&var(0), &var(1));
                    for i in 0..size {
                        assert!(graph.are_offsets_equal(&var(10_000 + i), &var(20_000 + i)));
                    }
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 80 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 512 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
        }
    }

    #[test]
    fn addition_congruence_forks_do_not_reindex_unrelated_parents() {
        for size in [16u64, 64, 256, 1024] {
            let mut graph = EqualityGraph::default();
            for i in 0..size {
                graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
            }
            let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for i in 0..size {
                        let mut branch = graph.clone();
                        // Argument order must not move the class with many
                        // parents under this newly registered singleton.
                        branch.add_offset_equality(&var(20_000 + i), &var(0));
                        assert!(
                            branch.are_offsets_equal(&add(var(20_000 + i), var(10)), &var(10_000))
                        );
                    }
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 100 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 512 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
            assert!(!graph.are_offsets_equal(&var(20_000), &var(0)));
        }
    }

    #[test]
    fn offset_equality_is_transitive_symmetric_and_branch_local() {
        let (a, b, c) = (var(1), var(2), var(3));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&a, &b);
        let mut branch = parent.clone();
        branch.add_offset_equality(&b, &c);
        assert!(branch.are_offsets_equal(&c, &a));
        assert!(branch.are_offsets_equal(&a, &a));
        assert!(!parent.are_offsets_equal(&a, &c));
        let plus_one =
            |x| PointerOffsetTerm::Add(Box::new(x), Box::new(PointerOffsetTerm::Constant(1)));
        assert!(branch.are_offsets_equal(&plus_one(a), &plus_one(c)));
    }

    #[test]
    fn offset_equality_preserves_width_signedness_and_snapshot_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let scaled = |value, width, unsigned| PointerOffsetTerm::Int64Scaled {
            value: Box::new(value),
            byte_width: width,
            unsigned,
        };
        let value = Bitvector32Term::Variable(Variable(10));
        let signed = scaled(value.clone(), 4, false);
        let target = var(11);
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&signed, &target);
        assert!(!graph.are_offsets_equal(&scaled(value.clone(), 8, false), &target));
        assert!(!graph.are_offsets_equal(&scaled(value, 4, true), &target));
        let before =
            crate::kernel::intern_c_memory(crate::kernel::CMemory::new().with_block("offset", 8));
        let address = Pointer::symbolic(Variable(12));
        let after = crate::kernel::intern_c_memory(before.memory().clone().store(
            address.clone(),
            crate::kernel::CValue::Int32(Bitvector32Term::Constant(9)),
        ));
        let load = |memory: &crate::kernel::SharedCMemory| {
            Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory, &address, 8, memory,
            ))
        };
        let old = scaled(load(&before), 4, false);
        let new = scaled(load(&after), 4, false);
        graph.add_offset_equality(&old, &target);
        assert!(!graph.are_offsets_equal(&new, &target));
        assert!(!graph.are_offsets_equal(&add(new, var(13)), &add(target, var(13))));
    }

    #[test]
    fn offset_context_withdrawal_and_restriction_preserve_only_retained_equalities() {
        let (a, b, c) = (var(20), var(21), var(22));
        let ab = equality(&a, &b);
        let bc = equality(&b, &c);
        let p = Pointer::symbolic(Variable(23));
        let q = Pointer::symbolic(Variable(24));
        let pq = ConditionTerm::pointer_equal(p.clone(), q.clone());
        let context = PureFactContext::new()
            .assume_condition(ab.clone(), true)
            .assume_condition(bc.clone(), true)
            .assume_condition(pq.clone(), true);
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
        let translated_a = add(a.clone(), var(25));
        let translated_c = add(c.clone(), var(25));
        assert!(
            context
                .equality_graph
                .are_offsets_equal(&translated_a, &translated_c)
        );
        let weakened = context.without_exact_fact(&Proposition::ConditionIs(bc.clone(), true));
        assert!(!weakened.equality_graph.are_offsets_equal(&a, &c));
        assert!(
            !weakened
                .equality_graph
                .are_offsets_equal(&translated_a, &translated_c)
        );
        assert!(weakened.equality_graph.are_offsets_equal(&a, &b));
        assert!(weakened.equality_graph.are_equal(&p, &q));
        let no_pointer = context.without_exact_fact(&Proposition::ConditionIs(pq, true));
        assert!(!no_pointer.equality_graph.are_equal(&p, &q));
        assert!(no_pointer.equality_graph.are_offsets_equal(&a, &c));
        let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
        assert!(!restricted.equality_graph.are_offsets_equal(&a, &c));
        assert!(restricted.equality_graph.are_offsets_equal(&a, &b));
        let reversed = context.clone().assume_condition(bc, false);
        assert!(!reversed.equality_graph.are_offsets_equal(&a, &c));
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn offset_withdrawal_keeps_a_separately_stated_reverse_equality() {
        let (a, b, c) = (var(30), var(31), var(32));
        let ab = equality(&a, &b);
        let ba = equality(&b, &a);
        let context = PureFactContext::new()
            .assume_condition(ab.clone(), true)
            .assume_condition(ba.clone(), true)
            .assume_condition(equality(&b, &c), true);
        let once = context.without_exact_fact(&Proposition::ConditionIs(ab, true));
        assert!(once.equality_graph.are_offsets_equal(&a, &c));
        let twice = once.without_exact_fact(&Proposition::ConditionIs(ba, true));
        assert!(!twice.equality_graph.are_offsets_equal(&a, &c));
        assert!(twice.equality_graph.are_offsets_equal(&b, &c));
    }

    #[test]
    fn offset_graph_construction_and_fork_queries_scale_with_indexed_work() {
        let offset = |id| PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(id))),
            byte_width: 4,
        };
        for size in [16u64, 64, 256, 1024] {
            let ((graph, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut graph = EqualityGraph::default();
                    for i in 0..size {
                        graph.add_offset_equality(&offset(i), &offset(i + 1));
                        assert!(graph.are_offsets_equal(&offset(0), &offset(i + 1)));
                    }
                    graph
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 40 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 160 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
            let (_, fork_work) = crate::persistent::measure_persistent_work(|| {
                let mut branch = graph.clone();
                branch.add_offset_equality(&offset(size), &offset(size + 1));
                assert!(branch.are_offsets_equal(&offset(0), &offset(size + 1)));
                assert!(!graph.are_offsets_equal(&offset(0), &offset(size + 1)));
            });
            assert!(
                fork_work < 160 * logarithm,
                "size={size}, fork work={fork_work}"
            );
        }
    }
}
