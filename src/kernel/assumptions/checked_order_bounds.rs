//! Direct extrema and witnesses for checked order queries. Each admitted fact
//! changes only its two endpoint keys; queries never enumerate those buckets.
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

type Bound = (i64, ConditionTerm, bool);

#[derive(Clone, Debug, Default)]
struct EndpointBounds {
    lower: PersistentSet<Bound>,
    upper: PersistentSet<Bound>,
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct CheckedOrderBounds {
    constants: [PersistentMap<Bitvector32Term, EndpointBounds>; 2],
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
            let Some(number) = number else {
                continue;
            };
            let number = number
                + if strict {
                    if upper { -1 } else { 1 }
                } else {
                    0
                };
            let canonical = crate::kernel::eval::canonical_term(endpoint);
            for key in
                std::iter::once(endpoint).chain((&canonical != endpoint).then_some(&canonical))
            {
                crate::instrumentation::record_deterministic_work(1);
                let mut bounds = self.constants[kind].get(key).cloned().unwrap_or_default();
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
                self.constants[kind] = if bounds.lower.is_empty() && bounds.upper.is_empty() {
                    self.constants[kind].without_key(key)
                } else {
                    self.constants[kind].with_inserted(key.clone(), bounds)
                };
            }
        }
    }

    pub(super) fn interval(&self, term: &Bitvector32Term, unsigned: bool) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read indexed order bounds", 1);
        crate::instrumentation::record_deterministic_work(1);
        let bounds = self.constants[usize::from(unsigned)].get(term)?;
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
        let (number, condition, value) = self.constants[0].get(term)?.upper.iter().next()?;
        (*number < i64::from(i32::MAX)).then(|| Proposition::ConditionIs(condition.clone(), *value))
    }
}
