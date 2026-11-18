//! Incremental unit propagation over exact proposition syntax.
//!
//! Admission compiles only its own Boolean clause. Each occurrence is watched
//! under the exact fact that falsifies it. A truth is processed once, and each
//! watcher is consumed once per persistent lineage, even if its clause has
//! already fired. Thus maintenance is amortized over admitted syntax and
//! produced facts; queries never traverse clauses or dependency buckets.

use super::{ConditionTerm, Proposition, PureFactContext};
use crate::kernel::proof::PersistentSequence;
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::Arc;

#[derive(Clone, Default)]
struct Consequences(PersistentSequence<Arc<Proposition>>);
impl std::fmt::Debug for Consequences {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Consequences").field(&self.0.len()).finish()
    }
}

#[derive(Debug, Default)]
pub(in crate::kernel) struct Index {
    known: PersistentSet<Literal>,
    consequences: Consequences,
    watches: PersistentMap<Literal, PersistentSet<u64>>,
    clauses: PersistentMap<u64, PersistentSet<Literal>>,
    next_clause: u64,
    pending: imbl::Vector<Arc<Proposition>>,
    draining: bool,
}

// A context fork shares the outstanding work too. A clone is independently
// drainable even when an admission helper forks in the middle of propagation;
// the parent's local drain guard must not escape into that child.
impl Clone for Index {
    fn clone(&self) -> Self {
        Self {
            known: self.known.clone(),
            consequences: self.consequences.clone(),
            watches: self.watches.clone(),
            clauses: self.clauses.clone(),
            next_clause: self.next_clause,
            pending: self.pending.clone(),
            draining: false,
        }
    }
}

/// A watched identity retains the source literal beside its root-based key.
/// Only keys normalize exact native observations; emitted consequences keep
/// their original spelling and derivation.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum LiteralKey {
    Comparison(super::observation_comparisons::Key, bool),
    Exact(Proposition),
}

#[derive(Clone, Debug)]
struct Literal {
    proposition: Proposition,
    identity: LiteralKey,
}
impl Literal {
    fn key(&self) -> &LiteralKey {
        &self.identity
    }
}
impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}
impl Eq for Literal {}
impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(other.key())
    }
}

// Exact observations may include a value-preserving machine conversion.
// Read only these cached root relations (at most three conversions), retaining
// shared operands. This does not simplify arithmetic or consult facts.
fn observation_reading(condition: &ConditionTerm) -> Option<ConditionTerm> {
    use crate::kernel::SharedIntegerTerm;
    let (left, right, rebuild): (
        &SharedIntegerTerm,
        &SharedIntegerTerm,
        fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm,
    ) = match condition {
        ConditionTerm::IntegerEqual(a, b) => (a, b, ConditionTerm::IntegerEqual),
        ConditionTerm::IntegerNotEqual(a, b) => (a, b, ConditionTerm::IntegerNotEqual),
        ConditionTerm::IntegerLessThan(a, b) => (a, b, ConditionTerm::IntegerLessThan),
        ConditionTerm::IntegerLessEqual(a, b) => (a, b, ConditionTerm::IntegerLessEqual),
        ConditionTerm::IntegerGreaterThan(a, b) => (a, b, ConditionTerm::IntegerGreaterThan),
        ConditionTerm::IntegerGreaterEqual(a, b) => (a, b, ConditionTerm::IntegerGreaterEqual),
        _ => return None,
    };
    let a = left.value_read();
    let b = right.value_read();
    if std::ptr::eq(a, left.as_ref()) && std::ptr::eq(b, right.as_ref()) {
        return None;
    }
    Some(rebuild(a.clone().into(), b.clone().into()))
}

fn literal(proposition: &Proposition, mut positive: bool) -> Literal {
    let mut body = proposition;
    while let Proposition::Not(inner) = body {
        positive = !positive;
        body = inner;
    }
    let proposition = match body {
        Proposition::ConditionIs(condition, truth) => {
            Proposition::condition_is(condition.clone(), *truth == positive)
        }
        _ if positive => body.clone(),
        _ => Proposition::Not(Box::new(body.clone())),
    };
    let identity = match &proposition {
        Proposition::ConditionIs(condition, truth) => {
            use crate::kernel::machine_integer::{Relation, comparison};
            let reading = observation_reading(condition.native_compat());
            let condition = reading.as_ref().unwrap_or(condition.native_compat());
            let view = if matches!(condition, ConditionTerm::Compare { .. }) {
                comparison::comparison_view(condition, true)
            } else {
                comparison::structural_native_comparison_view(condition, true)
            };
            if let Some(mut view) = view {
                let truth = if view.relation == Relation::NotEqual {
                    view.relation = Relation::Equal;
                    !*truth
                } else {
                    *truth
                };
                LiteralKey::Comparison(super::observation_comparisons::key(&view), truth)
            } else {
                LiteralKey::Exact(
                    reading
                        .map(|condition| Proposition::condition_is(condition, *truth))
                        .unwrap_or_else(|| proposition.clone()),
                )
            }
        }
        _ => LiteralKey::Exact(proposition.clone()),
    };
    Literal {
        proposition,
        identity,
    }
}

fn constant(proposition: &Proposition) -> Option<bool> {
    match proposition {
        Proposition::ConditionIs(condition, truth) => {
            crate::kernel::proof::fact_reasoning::trivial_condition_value(condition.native_compat())
                .map(|value| value == *truth)
        }
        _ => None,
    }
}

fn falsehood() -> Proposition {
    Proposition::condition_is(ConditionTerm::Constant(false), true)
}

impl Index {
    fn admit(&mut self, proposition: &Proposition) -> Vec<Proposition> {
        let fact = literal(proposition, true);
        if self.known.contains(&fact) {
            return Vec::new();
        }
        self.known = self.known.with_value(fact.clone());
        let mut derived = Vec::new();
        if self.known.contains(&literal(&fact.proposition, false)) {
            derived.push(falsehood());
        }
        if fact.proposition != *proposition {
            derived.push(fact.proposition.clone());
        }
        // This bucket is consumed, not rescanned on subsequent admissions.
        if let Some(watches) = self.watches.get(&fact).cloned() {
            self.watches.remove(&fact);
            let excluded = literal(&fact.proposition, false);
            for id in watches.iter() {
                crate::instrumentation::record_deterministic_work(1);
                let Some(remaining) = self.clauses.get(id) else {
                    continue;
                };
                let remaining = remaining.without_value(&excluded);
                self.finish_clause(*id, remaining, &mut derived);
            }
        }
        // Negated disjunctions and implications have conjunctive consequences.
        // Do not descend through quantifiers or opaque atoms.
        match &fact.proposition {
            Proposition::And(left, right) => {
                derived.extend([left.as_ref().clone(), right.as_ref().clone()]);
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Or(left, right) => {
                    derived.extend([
                        literal(left, false).proposition,
                        literal(right, false).proposition,
                    ]);
                }
                Proposition::Implies(left, right) => {
                    derived.extend([left.as_ref().clone(), literal(right, false).proposition]);
                }
                Proposition::And(_, _) => self.register_clause(&fact.proposition, &mut derived),
                _ => {}
            },
            Proposition::Or(_, _) | Proposition::Implies(_, _) => {
                self.register_clause(&fact.proposition, &mut derived);
            }
            _ => {}
        }
        derived
    }

    fn register_clause(&mut self, source: &Proposition, derived: &mut Vec<Proposition>) {
        // Keep the exact children as well as the flat clause. For example,
        // A => (B => C) with A must publish the whole B => C, not merely
        // remember a clause that waits for B. Flattening additionally handles
        // conjunction guards and longer disjunctions in linear input work.
        let raw = match source {
            Proposition::Or(a, b) => vec![(a.as_ref(), true), (b.as_ref(), true)],
            Proposition::Implies(a, b) => vec![(a.as_ref(), false), (b.as_ref(), true)],
            Proposition::Not(body) => match body.as_ref() {
                Proposition::And(a, b) => vec![(a.as_ref(), false), (b.as_ref(), false)],
                _ => unreachable!("only a negated conjunction is a clause"),
            },
            _ => unreachable!("only Boolean clauses are registered"),
        };
        let raw = self.remaining_literals(raw, false);
        let flat = self.remaining_literals(vec![(source, true)], true);
        if let Some(remaining) = &raw {
            self.watch_clause(remaining.clone(), derived);
        }
        if flat != raw
            && let Some(remaining) = flat
        {
            self.watch_clause(remaining, derived);
        }
    }

    fn remaining_literals(
        &self,
        mut pending: Vec<(&Proposition, bool)>,
        flatten: bool,
    ) -> Option<PersistentSet<Literal>> {
        let mut remaining = PersistentSet::default();
        while let Some((proposition, positive)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match (proposition, positive) {
                (Proposition::Not(body), positive) if flatten => pending.push((body, !positive)),
                (Proposition::Or(left, right), true) if flatten => {
                    pending.extend([(left.as_ref(), true), (right.as_ref(), true)]);
                }
                (Proposition::And(left, right), false) if flatten => {
                    pending.extend([(left.as_ref(), false), (right.as_ref(), false)]);
                }
                (Proposition::Implies(left, right), true) if flatten => {
                    pending.extend([(left.as_ref(), false), (right.as_ref(), true)]);
                }
                _ => {
                    let entry = literal(proposition, positive);
                    if constant(&entry.proposition) == Some(true) || self.known.contains(&entry) {
                        return None;
                    }
                    if constant(&entry.proposition) != Some(false)
                        && !self.known.contains(&literal(&entry.proposition, false))
                    {
                        remaining = remaining.with_value(entry);
                    }
                }
            }
        }
        Some(remaining)
    }

    fn watch_clause(&mut self, remaining: PersistentSet<Literal>, derived: &mut Vec<Proposition>) {
        let id = self.next_clause;
        self.next_clause += 1;
        if remaining.len() > 1 {
            for entry in remaining.iter() {
                let trigger = literal(&entry.proposition, false);
                let watches = self.watches.get(&trigger).cloned().unwrap_or_default();
                self.watches.insert(trigger, watches.with_value(id));
            }
        }
        self.finish_clause(id, remaining, derived);
    }

    fn finish_clause(
        &mut self,
        id: u64,
        remaining: PersistentSet<Literal>,
        derived: &mut Vec<Proposition>,
    ) {
        match remaining.len() {
            0 => {
                self.clauses.remove(&id);
                derived.push(falsehood());
            }
            1 => {
                self.clauses.remove(&id);
                derived.push(
                    remaining
                        .last()
                        .expect("one remaining literal")
                        .proposition
                        .clone(),
                );
            }
            _ => self.clauses.insert(id, remaining),
        }
    }
}

impl PureFactContext {
    /// The already constructed Boolean output since an ancestor checkpoint.
    /// Traverses only the appended suffix, never the older fact context.
    pub(crate) fn propagation_consequences_since(&self, ancestor: &Self) -> Vec<Arc<Proposition>> {
        self.exact_propagation
            .consequences
            .0
            .suffix_since(&ancestor.exact_propagation.consequences.0)
            .expect("fact admission extends its propagation lineage")
    }

    /// Construct consequences from the newly admitted fact and previously
    /// admitted clauses. Re-entering normal admission maintains all existing
    /// fact/equality/consulted-premise projections, without rechecking the inference.
    pub(super) fn admit_exact_propagation(&mut self, proposition: Proposition) {
        self.admit_shared_exact_propagation(Arc::new(proposition));
    }

    pub(super) fn admit_shared_exact_propagation(&mut self, proposition: Arc<Proposition>) {
        self.exact_propagation.pending.push_back(proposition);
        if self.exact_propagation.draining {
            return;
        }
        self.exact_propagation.draining = true;
        while let Some(fact) = self.exact_propagation.pending.pop_front() {
            for consequence in self.exact_propagation.admit(&fact) {
                let consequence = Arc::new(consequence);
                if !self.contains_assumed_exact(&consequence) {
                    self.exact_propagation
                        .consequences
                        .0
                        .push(consequence.clone());
                }
                let context = std::mem::take(self);
                *self = context.assume_shared_proposition(consequence);
            }
        }
        self.exact_propagation.draining = false;
    }
}

#[cfg(test)]
mod tests;
