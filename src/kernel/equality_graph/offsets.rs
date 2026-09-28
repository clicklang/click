//! Explicit equality of whole pointer-offset terms, inside the trusted graph.
//! No arithmetic propagation or congruence is performed here. Shallow intern
//! keys preserve widths, signedness, and machine-term snapshot identity.

use super::{MachineAtom, PointerOffsetTerm, Variable};
use crate::persistent::PersistentMap;

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
    // Union by size bounds root walks logarithmically without path compression
    // or a full-class copy when a persistent branch is extended.
    parents: PersistentMap<u64, u64>,
    sizes: PersistentMap<u64, usize>,
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
                    self.nodes.insert(node, id);
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
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return false;
        }
        let mut left_size = self.sizes.get(&left).copied().unwrap_or(1);
        let mut right_size = self.sizes.get(&right).copied().unwrap_or(1);
        if left_size < right_size {
            std::mem::swap(&mut left, &mut right);
            std::mem::swap(&mut left_size, &mut right_size);
        }
        self.parents.insert(right, left);
        self.sizes.remove(&right);
        self.sizes.insert(left, left_size + right_size);
        true
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
        assert!(!branch.are_offsets_equal(&plus_one(a), &plus_one(c)));
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
        let weakened = context.without_exact_fact(&Proposition::ConditionIs(bc.clone(), true));
        assert!(!weakened.equality_graph.are_offsets_equal(&a, &c));
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
