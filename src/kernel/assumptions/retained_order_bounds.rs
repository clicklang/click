//! Shared endpoints and their original supporting propositions. Readers inspect
//! views; a consumer requiring a written output exports that selected value.
use super::checked_scalar_facts::ScalarOperandKey as Key;
use super::*;
use crate::kernel::MachineOperandView as V;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{NativeComparisonView, comparison_view},
};
use crate::persistent::{PersistentMap, PersistentSet};

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
    entries: PersistentMap<BoundKey, PersistentSet<Proposition>>,
}
impl Bounds {
    pub(in crate::kernel) fn sourced_operands(
        &self,
    ) -> impl Iterator<Item = (V<'_>, V<'_>, bool, bool, &Proposition)> {
        self.entries
            .iter()
            .map(|((own, other, strict, forward), sources)| {
                (
                    own.operand_view(),
                    other.operand_view(),
                    *strict,
                    *forward,
                    sources.iter().next().expect("bound source"),
                )
            })
    }
    pub(in crate::kernel) fn operand_keys(
        &self,
    ) -> impl Iterator<Item = (V<'_>, V<'_>, bool, bool)> {
        self.entries.keys().map(|(own, other, strict, forward)| {
            (own.operand_view(), other.operand_view(), *strict, *forward)
        })
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct OrderBoundIndex {
    format: Option<MachineIntegerType>,
    endpoints: PersistentMap<Key, Bounds>,
}
impl OrderBoundIndex {
    pub(in crate::kernel) fn get(&self, term: &Bitvector32Term) -> Option<&Bounds> {
        self.get_operand(V::Legacy(term))
    }
    pub(in crate::kernel) fn get_operand(&self, term: V<'_>) -> Option<&Bounds> {
        self.endpoints.get(&Key::for_format(self.format?, term))
    }
    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        self.format == other.format && self.endpoints.shares_root_with(&other.endpoints)
    }
    pub(super) fn adjust(
        &mut self,
        view: &NativeComparisonView<'_>,
        source: &Proposition,
        insert: bool,
    ) {
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
                let sources = bounds.entries.get(&bound).cloned().unwrap_or_default();
                let sources = if insert {
                    sources.with_value(source.clone())
                } else {
                    sources.without_value(source)
                };
                bounds.entries = if sources.is_empty() {
                    bounds.entries.without_key(&bound)
                } else {
                    bounds.entries.with_inserted(bound.clone(), sources)
                };
                self.endpoints = if bounds.entries.is_empty() {
                    self.endpoints.without_key(&endpoint)
                } else {
                    self.endpoints.with_inserted(endpoint, bounds)
                };
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct Edges {
    entries: PersistentMap<(Key, bool), usize>,
}
impl Edges {
    pub(in crate::kernel) fn operand_keys(&self) -> impl Iterator<Item = (V<'_>, bool)> {
        self.entries
            .keys()
            .map(|(term, strict)| (term.operand_view(), *strict))
    }
}
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct OrderEdgeIndex {
    format: Option<MachineIntegerType>,
    endpoints: PersistentMap<Key, Edges>,
}
impl OrderEdgeIndex {
    pub(in crate::kernel) fn get_operand(&self, term: V<'_>) -> Option<&Edges> {
        self.endpoints.get(&Key::for_format(self.format?, term))
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
        let from = Key::canonical(format, from);
        let edge = (Key::canonical(format, to), strict);
        let mut edges = self.endpoints.get(&from).cloned().unwrap_or_default();
        let count = edges.entries.get(&edge).copied().unwrap_or(0);
        if insert {
            edges.entries = edges.entries.with_inserted(edge, count + 1);
        } else if count <= 1 {
            edges.entries = edges.entries.without_key(&edge);
        } else {
            edges.entries = edges.entries.with_inserted(edge, count - 1);
        }
        self.endpoints = if edges.entries.is_empty() {
            self.endpoints.without_key(&from)
        } else {
            self.endpoints.with_inserted(from, edges)
        };
    }
}
