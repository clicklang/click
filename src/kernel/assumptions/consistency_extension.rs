//! Consistency of a fact context checked from a consistent one it extends.
//!
//! Contradiction is monotone: removing facts never creates a conflict, and
//! adding facts creates one only through an added fact. So a context that is
//! a consistent context with some facts removed and some added is
//! inconsistent only through a conflict an added fact takes part in.
//! `PureFactContext::is_inconsistent` rescans every fact, so a proof whose
//! contexts change by a few facts per step paid for all of them at every
//! step. A full scan that finds no conflict leaves a [`ConsistencySnapshot`]
//! of the indexes it built; a later context that differs from it by removed
//! facts and by added order facts of the plain shape below is decided by
//! checking just the added facts against the snapshot's indexes.
//!
//! The snapshot keeps the entries of removed facts. They can only make a
//! check find more conflicts than the context has, never fewer: a stale
//! entry may make the extension decline, and the full scan then decides,
//! but it cannot hide a conflict.
//!
//! The check answers only "consistent". Whenever an added fact is not plain,
//! the snapshot was built under other inputs, or an added fact would conflict
//! or merge two existing classes, it declines and the full scan decides, so
//! every "inconsistent" verdict still comes from the full scan.
//!
//! An added fact is plain when it is a signed order fact
//! (`condition_as_order_fact`) whose endpoints are built from non-load
//! variables and constants under `+`, `-` and `*` and are not
//! theory-sensitive, so their index keys do not depend on the context. The
//! snapshot itself must hold no theory-sensitive endpoint, no load-valued
//! endpoint, and no pointer-offset alias guard: then the full scan's deep
//! pairwise rules and alias rule have nothing to compare, before and after
//! the extension, and every remaining rule is a keyed lookup that the
//! extension repeats for each added fact:
//!
//! - opposite polarities of one canonical condition;
//! - an exact strict self-edge, reverse edge, or strict edge across an exact
//!   equality;
//! - a strict edge inside one equality class, or a reverse edge between two
//!   classes when either is strict;
//! - a variable whose constant bounds leave no admissible value.
//!
//! See `docs/internals/verification-efficiency.md`.

use super::proposition_reasoning::{
    canonical_contradiction_condition, normalized_order_endpoint_index_key,
    order_endpoint_is_theory_sensitive,
};
use super::*;
use crate::kernel::reasoning::order_reasoning::{
    IntegerRangeFacts, bitvector_variable, condition_as_order_fact, integer_range_exhausted,
    signed_bitvector_constant,
};
use crate::persistent::{PersistentMap, PersistentSet};

/// The most differing facts an extension checks before deferring to the
/// full scan, which then records a fresh snapshot.
const EXTENSION_FACT_LIMIT: usize = 64;
/// Snapshots retained per thread, most recent first.
const SNAPSHOT_LIMIT: usize = 4;

thread_local! {
    static SNAPSHOTS: RefCell<Vec<ConsistencySnapshot>> = const { RefCell::new(Vec::new()) };
}

pub(crate) fn clear_consistency_snapshots() {
    SNAPSHOTS.with(|snapshots| snapshots.borrow_mut().clear());
}

/// The indexes of one full consistency scan that found no conflict, keyed by
/// the inputs it read.
#[derive(Clone)]
pub(super) struct ConsistencySnapshot {
    pub(super) generation: u64,
    pub(super) bridging: bool,
    pub(super) condition_facts: PersistentMap<ConditionTerm, bool>,
    pub(super) scalar_evidence: ScalarEvidenceInputs,
    /// Each condition's canonical form and the polarity the context holds.
    pub(super) polarities: PersistentMap<ConditionTerm, bool>,
    /// Exact order edges and whether any is strict.
    pub(super) exact_order: PersistentMap<(Bitvector32Term, Bitvector32Term), bool>,
    /// Exact equalities, as ordered pairs.
    pub(super) exact_equal: PersistentSet<(Bitvector32Term, Bitvector32Term)>,
    /// The equality class of every registered endpoint, and of every index
    /// key a registration walked.
    pub(super) term_class: PersistentMap<Bitvector32Term, usize>,
    pub(super) key_class: PersistentMap<Bitvector32Term, usize>,
    pub(super) next_class: usize,
    /// Class-level order edges and whether any is strict.
    pub(super) class_order: PersistentMap<(usize, usize), bool>,
    /// Constant bounds and excluded values per variable.
    pub(super) ranges: PersistentMap<Variable, IntegerRangeFacts>,
}

pub(super) type ScalarEvidenceInputs = PersistentMap<
    Bitvector32Term,
    PersistentMap<Bitvector32Term, PersistentMap<ConditionTerm, Proposition>>,
>;

/// Whether an endpoint is built only from non-load variables and constants
/// under `+`, `-` and `*`: its index keys are then context-free, as the
/// extension requires. Any other term defers to the full scan.
pub(super) fn plain_endpoint(term: &Bitvector32Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match term {
            Bitvector32Term::Variable(variable) if !crate::kernel::is_load_variable(variable) => {}
            Bitvector32Term::Constant(_) => {}
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            _ => return false,
        }
    }
    true
}

/// Record a snapshot as the most recent.
pub(super) fn record_snapshot(snapshot: ConsistencySnapshot) {
    SNAPSHOTS.with(|snapshots| {
        let mut snapshots = snapshots.borrow_mut();
        snapshots.insert(0, snapshot);
        snapshots.truncate(SNAPSHOT_LIMIT);
    });
}

/// `Some(false)` when `context` extends a recorded consistent snapshot by
/// plain order facts none of which conflicts; `None` otherwise. Records the
/// extended snapshot so the next extension starts from it.
pub(super) fn consistent_by_extension(
    context: &PureFactContext,
    generation: u64,
    bridging: bool,
) -> Option<bool> {
    if !context.algebraic_constructor_conflicts.is_empty() {
        return None;
    }
    let candidates = SNAPSHOTS.with(|snapshots| snapshots.borrow().clone());
    for snapshot in candidates {
        if snapshot.generation != generation || snapshot.bridging != bridging {
            continue;
        }
        let Some(added) = added_facts(&snapshot.condition_facts, &context.condition_facts) else {
            continue;
        };
        if snapshot.scalar_evidence != context.equality_graph.admitted.scalar_evidence_inputs {
            continue;
        }
        let extended = extend(snapshot, context, &added)?;
        record_snapshot(extended);
        return Some(false);
    }
    None
}

/// The facts `extended` holds and `base` does not, a changed polarity
/// counting as added, or `None` when the two differ in more than the limit.
/// Facts `base` holds and `extended` lacks are skipped: removing a fact
/// cannot create a conflict.
fn added_facts(
    base: &PersistentMap<ConditionTerm, bool>,
    extended: &PersistentMap<ConditionTerm, bool>,
) -> Option<Vec<(ConditionTerm, bool)>> {
    let mut added = Vec::new();
    for (differences, (condition, _, after)) in base.diff(extended).enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        if differences >= EXTENSION_FACT_LIMIT {
            return None;
        }
        if let Some(value) = after {
            added.push((condition.clone(), *value));
        }
    }
    Some(added)
}

/// The snapshot with each added fact checked and indexed, or `None` when a
/// fact is not plain, conflicts, or would merge two existing classes.
fn extend(
    mut snapshot: ConsistencySnapshot,
    context: &PureFactContext,
    added: &[(ConditionTerm, bool)],
) -> Option<ConsistencySnapshot> {
    let equality_index = &context.equality_graph;
    for (condition, value) in added {
        crate::instrumentation::record_deterministic_work(1);
        let (left, right, strict) = condition_as_order_fact(condition, *value)?;
        if condition.true_pointer_offset_sides().is_some() {
            return None;
        }
        for endpoint in [&left, &right] {
            if !plain_endpoint(endpoint)
                || order_endpoint_is_theory_sensitive(endpoint, equality_index)
            {
                return None;
            }
        }

        let key = canonical_contradiction_condition(condition);
        if snapshot
            .polarities
            .get(&key)
            .is_some_and(|prior| prior != value)
        {
            return None;
        }
        snapshot.polarities.insert(key, *value);

        let ordered = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        if (left == right && strict)
            || snapshot
                .exact_order
                .get(&(right.clone(), left.clone()))
                .is_some_and(|reverse_strict| strict || *reverse_strict)
            || (strict && snapshot.exact_equal.contains(&ordered))
        {
            return None;
        }
        let pair = (left.clone(), right.clone());
        let exact_strict = snapshot.exact_order.get(&pair).copied().unwrap_or(false) || strict;
        snapshot.exact_order.insert(pair, exact_strict);

        let left_class = register_endpoint(&mut snapshot, context, &left)?;
        let right_class = register_endpoint(&mut snapshot, context, &right)?;
        if (strict && left_class == right_class)
            || snapshot
                .class_order
                .get(&(right_class, left_class))
                .is_some_and(|reverse_strict| strict || *reverse_strict)
        {
            return None;
        }
        let class_pair = (left_class, right_class);
        let class_strict = snapshot
            .class_order
            .get(&class_pair)
            .copied()
            .unwrap_or(false)
            || strict;
        snapshot.class_order.insert(class_pair, class_strict);

        for variable in add_to_ranges(&mut snapshot.ranges, &left, &right, strict) {
            if snapshot
                .ranges
                .get(&variable)
                .is_some_and(integer_range_exhausted)
            {
                return None;
            }
        }
    }
    snapshot.condition_facts = context.condition_facts.clone();
    Some(snapshot)
}

/// An endpoint's class, registering it as the full scan does: its equality
/// graph key and its order index key share one class. `None` when the two
/// keys already lie in different classes, which the full scan would merge.
fn register_endpoint(
    snapshot: &mut ConsistencySnapshot,
    context: &PureFactContext,
    term: &Bitvector32Term,
) -> Option<usize> {
    if let Some(class) = snapshot.term_class.get(term) {
        return Some(*class);
    }
    let graph_key = equality_graph_term_key(term);
    let index_key = normalized_order_endpoint_index_key(context, term);
    let class = match (
        snapshot.key_class.get(&graph_key).copied(),
        snapshot.key_class.get(&index_key).copied(),
    ) {
        (Some(graph), Some(index)) if graph != index => return None,
        (Some(class), _) | (_, Some(class)) => class,
        (None, None) => {
            let class = snapshot.next_class;
            snapshot.next_class += 1;
            class
        }
    };
    for key in [graph_key, index_key] {
        if snapshot.key_class.contains_key(&key) {
            continue;
        }
        let members = context.equality_graph.scalar_evidence_class(&key);
        for member in std::iter::once(key).chain(members) {
            crate::instrumentation::record_deterministic_work(1);
            match snapshot.key_class.get(&member) {
                Some(existing) if *existing != class => return None,
                Some(_) => {}
                None => snapshot.key_class.insert(member, class),
            }
        }
    }
    snapshot.term_class.insert(term.clone(), class);
    Some(class)
}

/// Fold one order fact into the per-variable bounds, as
/// `integer_range_facts` does, and name the variables it bounded.
pub(super) fn add_to_ranges(
    ranges: &mut PersistentMap<Variable, IntegerRangeFacts>,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    strict: bool,
) -> Vec<Variable> {
    let mut bounded = Vec::new();
    if let (Some(variable), Some(bound)) =
        (bitvector_variable(left), signed_bitvector_constant(right))
    {
        let upper = if strict { bound - 1 } else { bound };
        let mut range = ranges.get(&variable).cloned().unwrap_or_default();
        range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
        ranges.insert(variable, range);
        bounded.push(variable);
    }
    if let (Some(bound), Some(variable)) =
        (signed_bitvector_constant(left), bitvector_variable(right))
    {
        let lower = if strict { bound + 1 } else { bound };
        let mut range = ranges.get(&variable).cloned().unwrap_or_default();
        range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
        ranges.insert(variable, range);
        bounded.push(variable);
    }
    bounded
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(986_100 + index))
    }

    /// A deterministic stream of facts: mostly plain order facts over a few
    /// variables, constants and sums, which the extension decides, and some
    /// equalities, disequalities and loads, which defer to the full scan.
    struct Facts(u64);
    impl Facts {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0 >> 33
        }
        fn term(&mut self) -> Bitvector32Term {
            match self.next() % 6 {
                0 | 1 => var(self.next() % 4),
                2 => Bitvector32Term::Constant((self.next() % 7) as u32),
                3 => Bitvector32Term::Constant(u32::MAX - (self.next() % 2) as u32),
                4 => Bitvector32Term::add(var(self.next() % 4), Bitvector32Term::Constant(1)),
                _ => var(self.next() % 4),
            }
        }
        fn fact(&mut self) -> (ConditionTerm, bool) {
            let (left, right) = (Box::new(self.term()), Box::new(self.term()));
            let value = !self.next().is_multiple_of(3);
            let condition = match self.next() % 12 {
                0..=2 => ConditionTerm::Bitvector32SignedLessThan(left, right),
                3..=5 => ConditionTerm::Bitvector32SignedLessEqual(left, right),
                6 | 7 => ConditionTerm::Bitvector32SignedGreaterThan(left, right),
                8 => ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
                9 | 10 => ConditionTerm::Bitvector32Equal(left, right),
                _ => ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(Bitvector32Term::Variable(Variable(
                        crate::kernel::eval::LOAD_VARIABLE_RANGE.start + self.next() % 2,
                    ))),
                    right,
                ),
            };
            (condition, value)
        }
    }

    #[test]
    fn extension_agrees_with_the_full_scan_on_growing_and_forking_contexts() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut extended = 0usize;
        for seed in 0..40u64 {
            clear_consistency_snapshots();
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
                PureFactContext::reset_context_inconsistency_full_scans();
                let answer = context.is_inconsistent();
                extended += usize::from(PureFactContext::context_inconsistency_full_scans() == 0);
                // `is_inconsistent` reads the equality graph's constant
                // conflicts before either route, so the reference does too.
                let reference = context.equality_graph.has_scalar_constant_conflict()
                    || context.is_inconsistent_unmemoized();
                assert_eq!(
                    answer, reference,
                    "seed {seed}: {:?}",
                    context.condition_facts
                );
                contexts.push(context);
            }
        }
        assert!(
            extended > 200,
            "the extension decided only {extended} contexts"
        );
    }

    fn less(left: Bitvector32Term, right: Bitvector32Term) -> (ConditionTerm, bool) {
        (
            ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn equal(left: Bitvector32Term, right: Bitvector32Term) -> (ConditionTerm, bool) {
        (
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    }

    /// The last fact of each sequence closes a cycle only through an
    /// equality class, which the exact rules cannot see: the extension must
    /// not call it consistent.
    #[test]
    fn extension_sees_cycles_through_equality_classes() {
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
            clear_consistency_snapshots();
            let (last, prefix) = facts.split_last().expect("a closing fact");
            let mut context = PureFactContext::new();
            for (condition, value) in prefix {
                context = context.assume_condition(condition.clone(), *value);
                assert!(!context.is_inconsistent());
            }
            let closed = context.assume_condition(last.0.clone(), last.1);
            assert!(closed.is_inconsistent_unmemoized());
            assert!(closed.is_inconsistent(), "{:?}", closed.condition_facts);
        }
    }

    /// One plain order fact per step costs the extension a constant amount
    /// of work, however many facts the context already holds.
    #[test]
    fn extending_by_one_order_fact_does_not_rescan_the_context() {
        let _session = crate::kernel::VerificationSession::enter();
        let work_at = |size: u64| {
            clear_consistency_snapshots();
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    ConditionTerm::Bitvector32SignedLessEqual(
                        Box::new(var(index)),
                        Box::new(var(index + 1)),
                    ),
                    true,
                );
            }
            assert!(!context.is_inconsistent());
            let next = context.assume_condition(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(var(size + 1)),
                    Box::new(Bitvector32Term::Constant(7)),
                ),
                true,
            );
            PureFactContext::reset_context_inconsistency_full_scans();
            let (answer, work) =
                crate::instrumentation::measure_deterministic_work(|| next.is_inconsistent());
            assert!(!answer);
            assert_eq!(PureFactContext::context_inconsistency_full_scans(), 0);
            work
        };
        let small = work_at(16);
        let large = work_at(1024);
        assert!(
            large <= small + 32,
            "one added fact cost {large} work units beside 1024 facts against {small} beside 16"
        );
    }
}
