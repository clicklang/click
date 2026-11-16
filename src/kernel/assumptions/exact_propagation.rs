//! Incremental unit propagation over exact proposition syntax.
//!
//! Admission compiles only its own Boolean clause. Each occurrence is watched
//! under the exact fact that falsifies it. A truth is processed once, and each
//! watcher is consumed once per persistent lineage, even if its clause has
//! already fired. Thus maintenance is amortized over admitted syntax and
//! produced facts; queries never traverse clauses or dependency buckets.

use super::{ConditionTerm, Proposition, PureFactContext};
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Debug, Default)]
pub(in crate::kernel) struct Index {
    known: PersistentSet<Proposition>,
    watches: PersistentMap<Proposition, PersistentSet<u64>>,
    clauses: PersistentMap<u64, PersistentSet<Proposition>>,
    next_clause: u64,
    pending: imbl::Vector<Proposition>,
    draining: bool,
}

// A context fork shares the outstanding work too. A clone is independently
// drainable even when an admission helper forks in the middle of propagation;
// the parent's local drain guard must not escape into that child.
impl Clone for Index {
    fn clone(&self) -> Self {
        Self {
            known: self.known.clone(),
            watches: self.watches.clone(),
            clauses: self.clauses.clone(),
            next_clause: self.next_clause,
            pending: self.pending.clone(),
            draining: false,
        }
    }
}

/// Negation and condition polarity share one exact spelling. No comparison
/// respelling, alpha conversion, equality query, or memory erasure occurs.
fn literal(proposition: &Proposition, mut positive: bool) -> Proposition {
    let mut body = proposition;
    while let Proposition::Not(inner) = body {
        positive = !positive;
        body = inner;
    }
    match body {
        Proposition::ConditionIs(condition, truth) => {
            Proposition::ConditionIs(condition.clone(), *truth == positive)
        }
        _ if positive => body.clone(),
        _ => Proposition::Not(Box::new(body.clone())),
    }
}

fn constant(proposition: &Proposition) -> Option<bool> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(value), truth) => Some(value == truth),
        _ => None,
    }
}

fn falsehood() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

impl Index {
    fn admit(&mut self, proposition: Proposition) -> Vec<Proposition> {
        let fact = literal(&proposition, true);
        if self.known.contains(&fact) {
            return Vec::new();
        }
        self.known = self.known.with_value(fact.clone());
        let mut derived = Vec::new();
        if self.known.contains(&literal(&fact, false)) {
            derived.push(falsehood());
        }
        if fact != proposition {
            derived.push(fact.clone());
        }
        // This bucket is consumed, not rescanned on subsequent admissions.
        if let Some(watches) = self.watches.get(&fact).cloned() {
            self.watches.remove(&fact);
            let excluded = literal(&fact, false);
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
        match &fact {
            Proposition::And(left, right) => {
                derived.extend([left.as_ref().clone(), right.as_ref().clone()]);
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Or(left, right) => {
                    derived.extend([literal(left, false), literal(right, false)]);
                }
                Proposition::Implies(left, right) => {
                    derived.extend([left.as_ref().clone(), literal(right, false)]);
                }
                Proposition::And(_, _) => self.register_clause(&fact, &mut derived),
                _ => {}
            },
            Proposition::Or(_, _) | Proposition::Implies(_, _) => {
                self.register_clause(&fact, &mut derived);
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
    ) -> Option<PersistentSet<Proposition>> {
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
                    if constant(&entry) == Some(true) || self.known.contains(&entry) {
                        return None;
                    }
                    if constant(&entry) != Some(false)
                        && !self.known.contains(&literal(&entry, false))
                    {
                        remaining = remaining.with_value(entry);
                    }
                }
            }
        }
        Some(remaining)
    }

    fn watch_clause(
        &mut self,
        remaining: PersistentSet<Proposition>,
        derived: &mut Vec<Proposition>,
    ) {
        let id = self.next_clause;
        self.next_clause += 1;
        if remaining.len() > 1 {
            for entry in remaining.iter() {
                let trigger = literal(entry, false);
                let watches = self.watches.get(&trigger).cloned().unwrap_or_default();
                self.watches.insert(trigger, watches.with_value(id));
            }
        }
        self.finish_clause(id, remaining, derived);
    }

    fn finish_clause(
        &mut self,
        id: u64,
        remaining: PersistentSet<Proposition>,
        derived: &mut Vec<Proposition>,
    ) {
        match remaining.len() {
            0 => {
                self.clauses.remove(&id);
                derived.push(falsehood());
            }
            1 => {
                self.clauses.remove(&id);
                derived.push(remaining.last().expect("one remaining literal").clone());
            }
            _ => self.clauses.insert(id, remaining),
        }
    }
}

impl PureFactContext {
    /// Construct consequences from the newly admitted fact and previously
    /// admitted clauses. Re-entering normal admission maintains all existing
    /// fact/equality/provenance projections, without rechecking the inference.
    pub(super) fn admit_exact_propagation(&mut self, proposition: Proposition) {
        self.exact_propagation.pending.push_back(proposition);
        if self.exact_propagation.draining {
            return;
        }
        self.exact_propagation.draining = true;
        while let Some(fact) = self.exact_propagation.pending.pop_front() {
            for consequence in self.exact_propagation.admit(fact) {
                let context = std::mem::take(self);
                *self = context.assume_proposition(consequence);
            }
        }
        self.exact_propagation.draining = false;
    }
}

#[cfg(test)]
mod tests;
