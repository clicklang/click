//! Direct extrema and witnesses for checked order queries. Each admitted fact
//! changes only its two endpoint keys; queries never enumerate those buckets.
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

type Bound = (i64, ConditionTerm, bool);

#[derive(Clone, Debug, Default)]
struct EndpointBounds {
    symbolic_lower: PersistentSet<(ConditionTerm, bool)>,
    symbolic_upper: PersistentSet<(ConditionTerm, bool)>,
    strict_lower: usize,
    strict_upper: usize,
    lower: PersistentSet<Bound>,
    upper: PersistentSet<Bound>,
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct CheckedOrderBounds {
    endpoints: [PersistentMap<Bitvector32Term, EndpointBounds>; 2],
    strict_upper: PersistentMap<Bitvector32Term, PersistentSet<(ConditionTerm, bool)>>,
}

impl CheckedOrderBounds {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        let (kind, left, right, strict) =
            if let Some((left, right, strict)) = condition_as_order_fact(condition, value) {
                (0, left, right, strict)
            } else if let Some((left, right, strict)) =
                condition_reasoning::condition_as_uint32_order_fact(condition, value)
            {
                (1, left, right, strict)
            } else {
                return;
            };
        if kind == 0 && strict {
            let mut sources = self.strict_upper.get(&left).cloned().unwrap_or_default();
            let source = (condition.clone(), value);
            sources = if insert {
                sources.with_value(source)
            } else {
                sources.without_value(&source)
            };
            self.strict_upper = if sources.is_empty() {
                self.strict_upper.without_key(&left)
            } else {
                self.strict_upper.with_inserted(left.clone(), sources)
            };
        }
        for (endpoint, other, upper) in [(&left, &right, true), (&right, &left, false)] {
            let number = if kind == 0 {
                signed_bitvector_constant(other)
            } else {
                other.as_const().map(i64::from)
            };
            let number = number.map(|number| {
                number
                    + if strict {
                        if upper { -1 } else { 1 }
                    } else {
                        0
                    }
            });
            let canonical = crate::kernel::eval::canonical_term(endpoint);
            for key in
                std::iter::once(endpoint).chain((&canonical != endpoint).then_some(&canonical))
            {
                crate::instrumentation::record_deterministic_work(1);
                let mut bounds = self.endpoints[kind].get(key).cloned().unwrap_or_default();
                if number.is_none() {
                    let sources = if upper {
                        &mut bounds.symbolic_upper
                    } else {
                        &mut bounds.symbolic_lower
                    };
                    let source = (condition.clone(), value);
                    *sources = if insert {
                        sources.with_value(source)
                    } else {
                        sources.without_value(&source)
                    };
                }
                if strict {
                    let count = if upper {
                        &mut bounds.strict_upper
                    } else {
                        &mut bounds.strict_lower
                    };
                    if insert {
                        *count += 1;
                    } else {
                        *count -= 1;
                    }
                }
                if let Some(number) = number {
                    let sources = if upper {
                        &mut bounds.upper
                    } else {
                        &mut bounds.lower
                    };
                    let source = (number, condition.clone(), value);
                    *sources = if insert {
                        sources.with_value(source)
                    } else {
                        sources.without_value(&source)
                    };
                }
                self.endpoints[kind] = if bounds.lower.is_empty()
                    && bounds.upper.is_empty()
                    && bounds.symbolic_lower.is_empty()
                    && bounds.symbolic_upper.is_empty()
                    && bounds.strict_lower == 0
                    && bounds.strict_upper == 0
                {
                    self.endpoints[kind].without_key(key)
                } else {
                    self.endpoints[kind].with_inserted(key.clone(), bounds)
                };
            }
        }
    }

    pub(super) fn interval(&self, term: &Bitvector32Term, unsigned: bool) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read indexed order bounds", 1);
        crate::instrumentation::record_deterministic_work(1);
        let bounds = self.endpoints[usize::from(unsigned)].get(term)?;
        if bounds.lower.is_empty() && bounds.upper.is_empty() {
            return None;
        }
        let (min, max) = if unsigned {
            (0, i64::from(u32::MAX))
        } else {
            (i64::from(i32::MIN), i64::from(i32::MAX))
        };
        Some((
            bounds
                .lower
                .iter()
                .next_back()
                .map_or(min, |bound| min.max(bound.0)),
            bounds
                .upper
                .iter()
                .next()
                .map_or(max, |bound| max.min(bound.0)),
        ))
    }

    /// At most one numeric extremum and one unambiguous symbolic source per
    /// direction. The fixed four slots are selected, never a bucket iterator.
    pub(super) fn constant_evidence_sources(
        &self,
        term: &Bitvector32Term,
    ) -> [Option<Proposition>; 4] {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select constant bound evidence", 1);
        crate::instrumentation::record_deterministic_work(1);
        let Some(bounds) = self.endpoints[0].get(term) else {
            return [None, None, None, None];
        };
        let proposition =
            |(_, condition, value): &Bound| Proposition::ConditionIs(condition.clone(), *value);
        let singleton = |sources: &PersistentSet<(ConditionTerm, bool)>| {
            if sources.len() != 1 {
                return None;
            }
            let (condition, value) = sources.iter().next()?;
            Some(Proposition::ConditionIs(condition.clone(), *value))
        };
        [
            bounds.lower.iter().next_back().map(proposition),
            bounds.upper.iter().next().map(proposition),
            singleton(&bounds.symbolic_lower),
            singleton(&bounds.symbolic_upper),
        ]
    }

    /// Numeric extrema and carrier limits implied by a direct strict edge.
    pub(super) fn interval_with_strict(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read direct signed interval", 1);
        crate::instrumentation::record_deterministic_work(1);
        let bounds = self.endpoints[0].get(term)?;
        let (lower, upper) = self
            .interval(term, false)
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        Some((
            lower.max(i64::from(i32::MIN) + i64::from(bounds.strict_lower > 0)),
            upper.min(i64::from(i32::MAX) - i64::from(bounds.strict_upper > 0)),
        ))
    }

    pub(super) fn strict_upper(&self, term: &Bitvector32Term) -> Option<Proposition> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed order witness", 1);
        crate::instrumentation::record_deterministic_work(1);
        let (condition, value) = self.strict_upper.get(term)?.iter().next()?;
        Some(Proposition::ConditionIs(condition.clone(), *value))
    }

    pub(super) fn upper_below_max(&self, term: &Bitvector32Term) -> Option<Proposition> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed order witness", 1);
        crate::instrumentation::record_deterministic_work(1);
        let (number, condition, value) = self.endpoints[0].get(term)?.upper.iter().next()?;
        (*number < i64::from(i32::MAX)).then(|| Proposition::ConditionIs(condition.clone(), *value))
    }
}
