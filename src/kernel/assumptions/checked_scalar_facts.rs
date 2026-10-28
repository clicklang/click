//! Endpoint-selected equalities and contiguous excluded-value runs.
//! Admission changes only the written endpoints; queries never enumerate facts.
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Clone, Debug, Default)]
struct Exclusions {
    counts: PersistentMap<i64, usize>,
    runs: PersistentMap<i64, i64>,
}

impl Exclusions {
    fn containing(&self, value: i64) -> Option<(i64, i64)> {
        self.runs
            .get_key_value(&value)
            .or_else(|| self.runs.get_less_than(&value))
            .filter(|(_, end)| **end >= value)
            .map(|(start, end)| (*start, *end))
    }

    fn adjust(&mut self, value: i64, insert: bool) {
        let count = self.counts.get(&value).copied().unwrap_or(0);
        if insert {
            self.counts = self.counts.with_inserted(value, count + 1);
            if count != 0 {
                return;
            }
            let mut start = value;
            let mut end = value;
            if let Some((left, _)) = self.containing(value - 1) {
                start = left;
                self.runs = self.runs.without_key(&left);
            }
            if let Some(right) = self.runs.get(&(value + 1)).copied() {
                end = right;
                self.runs = self.runs.without_key(&(value + 1));
            }
            self.runs = self.runs.with_inserted(start, end);
        } else {
            if count > 1 {
                self.counts = self.counts.with_inserted(value, count - 1);
                return;
            }
            self.counts = self.counts.without_key(&value);
            if let Some((start, end)) = self.containing(value) {
                self.runs = self.runs.without_key(&start);
                if start < value {
                    self.runs = self.runs.with_inserted(start, value - 1);
                }
                if value < end {
                    self.runs = self.runs.with_inserted(value + 1, end);
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct CheckedScalarFacts {
    literals: PersistentMap<Bitvector32Term, PersistentSet<ConditionTerm>>,
    equalities: PersistentMap<Bitvector32Term, PersistentSet<ConditionTerm>>,
    exclusions: PersistentMap<Bitvector32Term, Exclusions>,
}

impl CheckedScalarFacts {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        let ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return;
        };
        for (endpoint, other) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            crate::instrumentation::record_deterministic_work(1);
            if value && signed_bitvector_constant(other).is_some() {
                let sources = self.literals.get(endpoint).cloned().unwrap_or_default();
                let sources = if insert {
                    sources.with_value(condition.clone())
                } else {
                    sources.without_value(condition)
                };
                self.literals = if sources.is_empty() {
                    self.literals.without_key(endpoint)
                } else {
                    self.literals.with_inserted(endpoint.clone(), sources)
                };
            }
            if value {
                let sources = self.equalities.get(endpoint).cloned().unwrap_or_default();
                let sources = if insert {
                    sources.with_value(condition.clone())
                } else {
                    sources.without_value(condition)
                };
                self.equalities = if sources.is_empty() {
                    self.equalities.without_key(endpoint)
                } else {
                    self.equalities.with_inserted(endpoint.clone(), sources)
                };
            } else if let Some(number) = signed_bitvector_constant(other) {
                let canonical = crate::kernel::eval::canonical_term(endpoint);
                for key in
                    std::iter::once(endpoint).chain((&canonical != endpoint).then_some(&canonical))
                {
                    let mut excluded = self.exclusions.get(key).cloned().unwrap_or_default();
                    excluded.adjust(number, insert);
                    self.exclusions = if excluded.counts.is_empty() {
                        self.exclusions.without_key(key)
                    } else {
                        self.exclusions.with_inserted(key.clone(), excluded)
                    };
                }
            }
        }
    }

    pub(super) fn literal_equality(&self, term: &Bitvector32Term) -> Option<&ConditionTerm> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select literal equality", 1);
        crate::instrumentation::record_deterministic_work(1);
        self.literals.get(term)?.iter().next()
    }

    pub(super) fn singleton_equality(&self, term: &Bitvector32Term) -> Option<&ConditionTerm> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select anchored equality", 1);
        crate::instrumentation::record_deterministic_work(1);
        let sources = self.equalities.get(term)?;
        (sources.len() == 1).then(|| sources.iter().next().expect("singleton"))
    }

    pub(super) fn past_exclusions(
        &self,
        term: &Bitvector32Term,
        lower: i64,
        upper: i64,
    ) -> (i64, i64) {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read excluded interval endpoints", 1);
        crate::instrumentation::record_deterministic_work(1);
        let Some(excluded) = self.exclusions.get(term) else {
            return (lower, upper);
        };
        let lower = excluded
            .containing(lower)
            .map_or(lower, |(_, end)| (end + 1).min(upper));
        let upper = excluded
            .containing(upper)
            .map_or(upper, |(start, _)| (start - 1).max(lower));
        (lower, upper)
    }
}
