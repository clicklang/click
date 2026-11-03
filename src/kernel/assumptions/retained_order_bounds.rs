//! Retained endpoints for the remaining boxed order-query adapters. Admission
//! stores shared keys; a legacy reader exports only an entry it actually visits.
use super::checked_scalar_facts::ScalarOperandKey as Key;
use super::*;
use crate::kernel::MachineOperandView as V;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{NativeComparisonView, comparison_view},
};
use crate::persistent::PersistentMap;
use std::sync::{Arc, OnceLock};

type RawBound = (Bitvector32Term, Bitvector32Term, bool, bool);
type BoundKey = (Key, Key, bool, bool);

pub(super) fn order_view(
    condition: &ConditionTerm,
    truth: bool,
) -> Option<NativeComparisonView<'_>> {
    let view = comparison_view(condition, truth)?;
    let view = if !matches!(condition, ConditionTerm::Compare { .. }) {
        view.widened().unwrap_or(view)
    } else {
        view
    };
    matches!(view.relation, Relation::Less | Relation::LessEqual).then_some(view)
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct Bounds {
    entries: PersistentMap<BoundKey, (usize, Arc<OnceLock<RawBound>>)>,
}
impl Bounds {
    pub(in crate::kernel) fn iter(&self) -> impl Iterator<Item = (&RawBound, &usize)> {
        self.entries
            .iter()
            .map(|((own, other, strict, forward), (count, boxed))| {
                (
                    boxed.get_or_init(|| {
                        (
                            own.value().clone(),
                            other.value().clone(),
                            *strict,
                            *forward,
                        )
                    }),
                    count,
                )
            })
    }
    pub(in crate::kernel) fn keys(&self) -> impl Iterator<Item = &RawBound> {
        self.iter().map(|(key, _)| key)
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct OrderBoundIndex {
    format: Option<MachineIntegerType>,
    endpoints: PersistentMap<Key, Bounds>,
}
impl OrderBoundIndex {
    pub(in crate::kernel) fn get(&self, term: &Bitvector32Term) -> Option<&Bounds> {
        self.endpoints
            .get(&Key::for_format(self.format?, V::Legacy(term)))
    }
    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        self.format == other.format && self.endpoints.shares_root_with(&other.endpoints)
    }
    pub(super) fn adjust(&mut self, view: &NativeComparisonView<'_>, insert: bool) {
        self.format = Some(view.format);
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = view.relation == Relation::Less;
        for (own, other, forward) in [(left, right, true), (right, left, false)] {
            let key = Key::for_format(view.format, own);
            let canonical = Key::canonical(view.format, own);
            let bound = (
                key.clone(),
                Key::for_format(view.format, other),
                strict,
                forward,
            );
            for endpoint in
                std::iter::once(key.clone()).chain((canonical != key).then_some(canonical))
            {
                let mut bounds = self.endpoints.get(&endpoint).cloned().unwrap_or_default();
                let (count, boxed) = bounds.entries.get(&bound).cloned().unwrap_or_default();
                if let (V::Legacy(own), V::Legacy(other)) = (own, other) {
                    boxed.get_or_init(|| (own.clone(), other.clone(), strict, forward));
                }
                if insert {
                    bounds.entries = bounds
                        .entries
                        .with_inserted(bound.clone(), (count + 1, boxed));
                } else if count <= 1 {
                    bounds.entries = bounds.entries.without_key(&bound);
                } else {
                    bounds.entries = bounds
                        .entries
                        .with_inserted(bound.clone(), (count - 1, boxed));
                }
                self.endpoints = if bounds.entries.is_empty() {
                    self.endpoints.without_key(&endpoint)
                } else {
                    self.endpoints.with_inserted(endpoint, bounds)
                };
            }
        }
    }
}

type RawEdge = (Bitvector32Term, bool);
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct Edges {
    entries: PersistentMap<(Key, bool), (usize, Arc<OnceLock<RawEdge>>)>,
}
impl Edges {
    pub(in crate::kernel) fn keys(&self) -> impl Iterator<Item = &RawEdge> {
        self.entries.iter().map(|((term, strict), (_, boxed))| {
            boxed.get_or_init(|| (term.value().clone(), *strict))
        })
    }
}
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct OrderEdgeIndex {
    format: Option<MachineIntegerType>,
    endpoints: PersistentMap<Key, Edges>,
}
impl OrderEdgeIndex {
    pub(in crate::kernel) fn get(&self, term: &Bitvector32Term) -> Option<&Edges> {
        self.endpoints
            .get(&Key::for_format(self.format?, V::Legacy(term)))
    }
    pub(super) fn adjust(
        &mut self,
        format: MachineIntegerType,
        from: V<'_>,
        to: V<'_>,
        strict: bool,
        insert: bool,
    ) {
        self.format = Some(format);
        let raw_to = match to {
            V::Legacy(term) => Some(term),
            V::Shared(_) => None,
        };
        let from = Key::canonical(format, from);
        let edge = (Key::canonical(format, to), strict);
        let mut edges = self.endpoints.get(&from).cloned().unwrap_or_default();
        let (count, boxed) = edges.entries.get(&edge).cloned().unwrap_or_default();
        if let Some(to) = raw_to {
            boxed.get_or_init(|| (to.clone(), strict));
        }
        if insert {
            edges.entries = edges.entries.with_inserted(edge, (count + 1, boxed));
        } else if count <= 1 {
            edges.entries = edges.entries.without_key(&edge);
        } else {
            edges.entries = edges.entries.with_inserted(edge, (count - 1, boxed));
        }
        self.endpoints = if edges.entries.is_empty() {
            self.endpoints.without_key(&from)
        } else {
            self.endpoints.with_inserted(from, edges)
        };
    }
}
