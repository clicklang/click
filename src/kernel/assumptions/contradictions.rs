//! Contradictions among a fact context's condition facts, indexed as each
//! fact is assumed.
//!
//! Every rule is a keyed lookup, so the context files each fact under the
//! keys its rules read when it assumes the fact, and `is_inconsistent` reads
//! whether any key is in conflict. No query walks the facts. The rules:
//!
//! - opposite polarities of one canonical condition, a full pointer
//!   equality's address equality among them, and a constant condition
//!   assumed with the other value;
//! - a strict order edge inside one equality class, or a reverse edge
//!   between two classes when either is strict;
//! - a variable whose constant bounds leave no admissible value.
//!
//! An equality class is a union-find over order-endpoint keys
//! (`order_endpoint_key`), joined by the scalar evidence edges of the
//! context's equalities (`scalar_evidence_pair`). Order edges are filed
//! under their endpoints' class roots; a merge moves the smaller class's
//! edges to the larger root, so each edge moves at most logarithmically
//! often. Both kinds of key are context-free, so a fact files the same way
//! in every context that holds it.
//!
//! A context only gains facts; a branch forks a persistent clone of its
//! parent's index.
//!
//! See `docs/internals/verification-efficiency.md`.

use super::checked_scalar_facts::ScalarOperandKey as Key;
use super::contradiction_endpoints::EndpointKeys;
use super::proposition_reasoning::canonical_contradiction_condition;
#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::MachineIntegerType;
use crate::kernel::MachineOperandView as V;
#[cfg(test)]
use crate::kernel::MachineTerm;
use crate::kernel::equality_graph::scalar_evidence_pair;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{ConditionTerm, Variable};
use crate::persistent::{PersistentMap, PersistentSet};

/// The widest bounded interval whose values are checked one by one against
/// the excluded values.
const EXHAUSTIBLE_RANGE: i64 = 256;

/// A key whose entries can conflict.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Cell {
    Polarity(ConditionTerm),
    /// The order edges between two class roots, smaller root first.
    Order(Key, Key),
    Range(Variable),
}

/// How many facts state an order edge, by strictness.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Edge {
    loose: u32,
    strict: u32,
}

impl Edge {
    fn any(self) -> bool {
        self.loose + self.strict > 0
    }

    fn add(self, other: Edge) -> Edge {
        Edge {
            loose: self.loose + other.loose,
            strict: self.strict + other.strict,
        }
    }
}

/// One variable's constant bounds and excluded values, each counted by the
/// facts that state it.
#[derive(Clone, Debug, Default)]
struct Range {
    lower: PersistentSet<i64>,
    upper: PersistentSet<i64>,
    excluded: PersistentSet<i64>,
}

impl Range {
    fn exhausted(&self) -> bool {
        let (Some(lower), Some(upper)) = (self.lower.iter().next_back(), self.upper.iter().next())
        else {
            return false;
        };
        if lower > upper {
            return true;
        }
        // Fewer excluded values than the interval holds leave one admitted.
        upper - lower <= EXHAUSTIBLE_RANGE
            && self.excluded.len() as i64 > upper - lower
            && (*lower..=*upper).all(|value| {
                crate::instrumentation::record_deterministic_work(1);
                self.excluded.contains(&value)
            })
    }

    fn is_empty(&self) -> bool {
        self.lower.is_empty() && self.upper.is_empty() && self.excluded.is_empty()
    }
}

/// The contradiction index of one set of condition facts.
#[derive(Clone, Debug, Default)]
pub(crate) struct Contradictions {
    endpoints: EndpointKeys,
    /// Which of `[false, true]` is assumed under each canonical condition.
    polarity: PersistentMap<ConditionTerm, [bool; 2]>,
    /// Union-find parents of non-root endpoint keys.
    parent: PersistentMap<Key, Key>,
    /// Member counts of class roots with more than one member.
    size: PersistentMap<Key, usize>,
    /// `from -> to -> edge`: `from <= to`, or `<` when strict, by class root.
    out_edges: PersistentMap<Key, PersistentMap<Key, Edge>>,
    /// The same edges keyed by `to`.
    in_edges: PersistentMap<Key, PersistentMap<Key, Edge>>,
    ranges: PersistentMap<Variable, Range>,
    /// The cells currently in conflict.
    conflicts: PersistentSet<Cell>,
}

impl Contradictions {
    /// Whether the indexed facts contradict each other.
    pub(crate) fn is_contradictory(&self) -> bool {
        !self.conflicts.is_empty()
    }

    fn adjust(&mut self, condition: &ConditionTerm, value: bool) {
        crate::instrumentation::record_deterministic_work(1);
        self.adjust_polarity(canonical_contradiction_condition(condition), value);
        if value && let ConditionTerm::PointerValueEqual(left, right) = condition {
            // Full pointer equality entails address equality, while its
            // negation makes no claim about addresses.
            let address =
                ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone());
            self.adjust_polarity(canonical_contradiction_condition(&address), true);
        }
        let observation =
            crate::kernel::machine_integer::comparison::native_comparison_view(condition, value);
        let cancel = observation.is_some();
        let mut comparison = observation.or_else(|| comparison_view(condition, value));
        while let Some(view) = comparison {
            // The old native copy admitted both the written equation and each
            // cancellation. Keep those endpoint classes without filing facts.
            comparison = cancel.then(|| view.cancelled_equality()).flatten();
            if view.format.format().bits() != 32
                || !matches!(view.relation, Relation::Equal | Relation::NotEqual)
            {
                continue;
            }
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view());
            let equal = view.relation == Relation::Equal;
            if equal {
                let left = self.register(left);
                let right = self.register(right);
                self.union(&left, &right);
            }
            let pair = left
                .variable()
                .zip(right.word32_constant())
                .or_else(|| right.variable().zip(left.word32_constant()));
            if let Some((variable, bits)) = pair {
                let constant = i64::from(bits as i32);
                self.adjust_range(*variable, |range| {
                    if equal {
                        range.lower = range.lower.with_value(constant);
                        range.upper = range.upper.with_value(constant);
                    } else {
                        range.excluded = range.excluded.with_value(constant);
                    }
                });
            }
        }
        if condition.true_pointer_offset_sides().is_some()
            && let Some((left, right)) = scalar_evidence_pair(condition, value)
        {
            self.union(
                &Key::new(left.operand_view()),
                &Key::new(right.operand_view()),
            );
        }
        if let Some(view) = super::retained_order_bounds::order_view(condition, value)
            && view.format == MachineIntegerType::Int32
        {
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view());
            let strict = view.relation == Relation::Less;
            let (left_key, right_key) = (self.register(left), self.register(right));
            let from = self.find(&left_key);
            let to = self.find(&right_key);
            let edge = if strict {
                Edge {
                    loose: 0,
                    strict: 1,
                }
            } else {
                Edge {
                    loose: 1,
                    strict: 0,
                }
            };
            self.adjust_edge(&from, &to, edge, true);
            self.refresh_order(&from, &to);
            if let (Some(variable), Some(bound)) = (
                left.variable().copied(),
                right.word32_constant().map(|bits| i64::from(bits as i32)),
            ) {
                let upper = if strict { bound - 1 } else { bound };
                self.adjust_range(variable, |range| {
                    range.upper = range.upper.with_value(upper);
                });
            }
            if let (Some(bound), Some(variable)) = (
                left.word32_constant().map(|bits| i64::from(bits as i32)),
                right.variable().copied(),
            ) {
                let lower = if strict { bound + 1 } else { bound };
                self.adjust_range(variable, |range| {
                    range.lower = range.lower.with_value(lower);
                });
            }
        }
    }

    fn set_conflict(&mut self, cell: Cell, conflict: bool) {
        self.conflicts = if conflict {
            self.conflicts.with_value(cell)
        } else {
            self.conflicts.without_value(&cell)
        };
    }

    fn adjust_polarity(&mut self, key: ConditionTerm, value: bool) {
        let mut held = self.polarity.get(&key).copied().unwrap_or([false, false]);
        held[usize::from(value)] = true;
        let conflict = (held[0] && held[1])
            || matches!(&key, ConditionTerm::Constant(actual) if held[usize::from(!*actual)]);
        self.polarity = self.polarity.with_inserted(key.clone(), held);
        self.set_conflict(Cell::Polarity(key), conflict);
    }

    fn adjust_range(&mut self, variable: Variable, change: impl FnOnce(&mut Range)) {
        let mut range = self.ranges.get(&variable).cloned().unwrap_or_default();
        change(&mut range);
        let exhausted = range.exhausted();
        self.ranges = if range.is_empty() {
            self.ranges.without_key(&variable)
        } else {
            self.ranges.with_inserted(variable, range)
        };
        self.set_conflict(Cell::Range(variable), exhausted);
    }

    /// An endpoint and its key name one value, so they share a class.
    fn register(&mut self, endpoint: V<'_>) -> Key {
        let (graph_key, key) = match endpoint {
            V::Legacy(term) => {
                let graph = super::equality_graph_term_key(term);
                if let Some(root) = crate::kernel::KernelTermImport::default()
                    .machine_arithmetic(MachineIntegerType::Int32, &graph)
                {
                    (
                        Key::new(V::Shared(&root)),
                        self.endpoints.key(V::Shared(&root)),
                    )
                } else {
                    (
                        Key::Written(graph),
                        Key::Written(super::proposition_reasoning::order_endpoint_key(term)),
                    )
                }
            }
            V::Shared(_) => (Key::new(endpoint), self.endpoints.key(endpoint)),
        };
        if graph_key != key {
            self.union(&graph_key, &key);
        }
        key
    }

    fn find(&self, term: &Key) -> Key {
        let mut current = term;
        while let Some(parent) = self.parent.get(current) {
            crate::instrumentation::record_deterministic_work(1);
            current = parent;
        }
        current.clone()
    }

    fn class_size(&self, root: &Key) -> usize {
        self.size.get(root).copied().unwrap_or(1)
    }

    fn union(&mut self, left: &Key, right: &Key) {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return;
        }
        let (root, merged) = if self.class_size(&left) >= self.class_size(&right) {
            (left, right)
        } else {
            (right, left)
        };
        let size = self.class_size(&root) + self.class_size(&merged);
        self.parent = self.parent.with_inserted(merged.clone(), root.clone());
        self.size = self
            .size
            .without_key(&merged)
            .with_inserted(root.clone(), size);
        self.move_edges(&merged, &root);
    }

    /// Refiles every edge at `merged` under `root`, which absorbed it.
    fn move_edges(&mut self, merged: &Key, root: &Key) {
        let outgoing = self.out_edges.get(merged).cloned().unwrap_or_default();
        let incoming = self.in_edges.get(merged).cloned().unwrap_or_default();
        let mut touched = Vec::new();
        for (to, edge) in outgoing.iter() {
            crate::instrumentation::record_deterministic_work(1);
            self.adjust_edge(merged, to, *edge, false);
            self.set_conflict(order_cell(merged, to), false);
            let to = if to == merged { root } else { to };
            self.adjust_edge(root, to, *edge, true);
            touched.push((root.clone(), to.clone()));
        }
        for (from, edge) in incoming.iter() {
            if from == merged {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            self.adjust_edge(from, merged, *edge, false);
            self.set_conflict(order_cell(from, merged), false);
            self.adjust_edge(from, root, *edge, true);
            touched.push((from.clone(), root.clone()));
        }
        for (from, to) in touched {
            self.refresh_order(&from, &to);
        }
    }

    fn edge(&self, from: &Key, to: &Key) -> Edge {
        self.out_edges
            .get(from)
            .and_then(|edges| edges.get(to))
            .copied()
            .unwrap_or_default()
    }

    fn adjust_edge(&mut self, from: &Key, to: &Key, edge: Edge, insert: bool) {
        let current = self.edge(from, to);
        let next = if insert {
            current.add(edge)
        } else {
            Edge {
                loose: current.loose.saturating_sub(edge.loose),
                strict: current.strict.saturating_sub(edge.strict),
            }
        };
        self.out_edges = with_edge(&self.out_edges, from, to, next);
        self.in_edges = with_edge(&self.in_edges, to, from, next);
    }

    /// Recomputes whether the edges between two roots conflict.
    fn refresh_order(&mut self, left: &Key, right: &Key) {
        let forward = self.edge(left, right);
        let conflict = if left == right {
            forward.strict > 0
        } else {
            let backward = self.edge(right, left);
            forward.any() && backward.any() && (forward.strict > 0 || backward.strict > 0)
        };
        self.set_conflict(order_cell(left, right), conflict);
    }
}

fn order_cell(left: &Key, right: &Key) -> Cell {
    if left <= right {
        Cell::Order(left.clone(), right.clone())
    } else {
        Cell::Order(right.clone(), left.clone())
    }
}

fn with_edge(
    edges: &PersistentMap<Key, PersistentMap<Key, Edge>>,
    from: &Key,
    to: &Key,
    edge: Edge,
) -> PersistentMap<Key, PersistentMap<Key, Edge>> {
    let targets = edges.get(from).cloned().unwrap_or_default();
    let targets = if edge.any() {
        targets.with_inserted(to.clone(), edge)
    } else {
        targets.without_key(to)
    };
    if targets.is_empty() {
        edges.without_key(from)
    } else {
        edges.with_inserted(from.clone(), targets)
    }
}

/// A fact context's index: extended as the context assumes condition facts,
/// cleared when the context is rebuilt, and rebuilt from the context's facts
/// by the next query that finds it cleared. Clones share it, as proof branches share the context.
#[derive(Clone)]
pub(crate) struct ContextContradictions(std::sync::Arc<std::sync::OnceLock<Contradictions>>);

impl Default for ContextContradictions {
    fn default() -> Self {
        Self(std::sync::Arc::new(std::sync::OnceLock::from(
            Contradictions::default(),
        )))
    }
}

impl std::fmt::Debug for ContextContradictions {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("ContextContradictions")
    }
}

impl ContextContradictions {
    /// Follows the context assuming `condition` with `value`; a cleared
    /// index stays cleared until its rebuild.
    pub(crate) fn adjust(&mut self, condition: &ConditionTerm, value: bool) {
        if let Some(index) = self.0.get() {
            let mut index = index.clone();
            index.adjust(condition, value);
            self.0 = std::sync::Arc::new(std::sync::OnceLock::from(index));
        }
    }

    /// Restarts from no facts, for a context about to re-assume all of its
    /// facts.
    pub(crate) fn reset(&mut self) {
        *self = Self::default();
    }

    /// The index of the context's `facts`, rebuilt from them when cleared.
    pub(crate) fn index<'a>(
        &self,
        facts: impl FnOnce() -> Vec<(&'a ConditionTerm, bool)>,
    ) -> &Contradictions {
        self.0.get_or_init(|| {
            let mut index = Contradictions::default();
            for (condition, value) in facts() {
                index.adjust(condition, value);
            }
            index
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::PureFactContext;

    fn var(index: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(986_100 + index))
    }

    /// A deterministic stream of facts over a few variables, constants, sums
    /// and loads: order facts, equalities and disequalities.
    struct Facts(u64);
    impl Facts {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0 >> 33
        }
        fn term(&mut self) -> MachineTerm {
            match self.next() % 6 {
                0 | 1 => var(self.next() % 4),
                2 => MachineTerm::constant((self.next() % 7) as u32),
                3 => MachineTerm::constant(u32::MAX - (self.next() % 2) as u32),
                4 => MachineTerm::add(var(self.next() % 4), MachineTerm::constant(1)),
                _ => var(self.next() % 4),
            }
        }
        fn fact(&mut self) -> (ConditionTerm, bool) {
            let (left, right) = (Box::new(self.term()), Box::new(self.term()));
            let value = !self.next().is_multiple_of(3);
            let condition = match self.next() % 12 {
                0..=2 => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                },
                3..=5 => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left,
                    right,
                },
                6 | 7 => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left,
                    right,
                },
                8 => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left,
                    right,
                },
                9 | 10 => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _ => ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(MachineTerm::Variable(Variable(
                        crate::kernel::eval::LOAD_VARIABLE_RANGE.start + self.next() % 2,
                    ))),
                    right,
                },
            };
            (condition, value)
        }
    }

    /// The index a context carries after growing, forking and dropping
    /// facts agrees with the reference scan of the same facts, and with an
    /// index rebuilt from them.
    #[test]
    fn the_incremental_index_agrees_with_the_reference_scan() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut contradictory = 0usize;
        for seed in 0..40u64 {
            let mut facts = Facts(seed + 1);
            let mut contexts = vec![PureFactContext::new()];
            for _ in 0..40 {
                // Grow the latest context, fork an earlier one, or drop one
                // of the latest's facts first, as proof branches and joins do.
                let latest = contexts.last().expect("a context").clone();
                let base = match facts.next() % 5 {
                    0 => contexts[(facts.next() as usize) % contexts.len()].clone(),
                    1 if !latest.condition_facts.is_empty() => {
                        let dropped = (facts.next() as usize) % latest.condition_facts.len();
                        let kept = latest
                            .condition_facts
                            .iter()
                            .enumerate()
                            .filter(|(index, _)| *index != dropped)
                            .map(|(_, (condition, value))| (condition.clone(), *value))
                            .collect::<Vec<_>>();
                        latest.restricted_to_facts(&kept, &[])
                    }
                    _ => latest,
                };
                let (condition, value) = facts.fact();
                let context = base.assume_condition(condition, value);
                let facts_of = || {
                    context
                        .condition_facts
                        .iter()
                        .map(|(condition, value)| (condition, *value))
                        .collect::<Vec<_>>()
                };
                let answer = context.contradictions.index(facts_of).is_contradictory();
                let rebuilt =
                    ContextContradictions(std::sync::Arc::new(std::sync::OnceLock::new()))
                        .index(facts_of)
                        .is_contradictory();
                let reference = context.reference_inconsistency_scan();
                assert_eq!(
                    answer, rebuilt,
                    "seed {seed}: {:?}",
                    context.condition_facts
                );
                assert_eq!(
                    answer, reference,
                    "seed {seed}: {:?}",
                    context.condition_facts
                );
                contradictory += usize::from(answer);
                contexts.push(context);
            }
        }
        assert!(
            contradictory > 100,
            "only {contradictory} contradictory contexts"
        );
    }

    fn less(left: MachineTerm, right: MachineTerm) -> (ConditionTerm, bool) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    }

    fn equal(left: MachineTerm, right: MachineTerm) -> (ConditionTerm, bool) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    }

    /// Each sequence closes a cycle only through an equality class, and
    /// in either order: the edges filed before the equality move with the
    /// class it merges.
    #[test]
    fn cycles_through_equality_classes_are_found_in_any_order() {
        let _session = crate::kernel::VerificationSession::enter();
        let cases = [
            // A reverse edge between classes: x == y, x < z, z < y.
            vec![
                equal(var(0), var(1)),
                less(var(0), var(2)),
                less(var(2), var(1)),
            ],
            // A strict edge inside one class: x == w, w == y, x < y.
            vec![
                equal(var(0), var(3)),
                equal(var(3), var(1)),
                less(var(0), var(1)),
            ],
        ];
        for facts in cases {
            for rotation in 0..facts.len() {
                let mut ordered = facts.clone();
                ordered.rotate_left(rotation);
                let (last, prefix) = ordered.split_last().expect("a closing fact");
                let mut context = PureFactContext::new();
                for (condition, value) in prefix {
                    context = context.assume_condition(condition.clone(), *value);
                    assert!(!context.is_inconsistent(), "{ordered:?}");
                }
                let closed = context.assume_condition(last.0.clone(), last.1);
                assert!(closed.is_inconsistent(), "{ordered:?}");
            }
        }
    }

    /// Asking whether a context is inconsistent reads the index, and one
    /// added fact files under a bounded number of keys, however many facts
    /// the context holds.
    #[test]
    fn one_added_fact_and_the_query_cost_the_same_beside_any_number_of_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let work_at = |size: u64| {
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(var(index)),
                        right: Box::new(var(index + 1)),
                    },
                    true,
                );
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(var(10_000 + index)),
                        right: Box::new(var(10_001 + index)),
                    },
                    true,
                );
            }
            assert!(!context.is_inconsistent());
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let next = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(var(size + 1)),
                        right: Box::new(MachineTerm::constant(7)),
                    },
                    true,
                );
                assert!(!next.is_inconsistent());
            });
            work
        };
        let small = work_at(16);
        let large = work_at(1024);
        assert!(
            large <= small + 64,
            "one added fact cost {large} work units beside 2048 facts against {small} beside 32"
        );
    }
}
