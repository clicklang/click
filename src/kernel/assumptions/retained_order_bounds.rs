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
    // Original true signed <=/< sources, retained separately from normalized
    // reversed/negated edges for the memory-containment premise rule.
    written_signed: PersistentMap<BoundKey, PersistentSet<Proposition>>,
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
    pub(super) fn written_signed_operands(
        &self,
    ) -> impl Iterator<Item = (V<'_>, V<'_>, bool, bool)> {
        self.written_signed
            .keys()
            .map(|(own, other, strict, forward)| {
                (own.operand_view(), other.operand_view(), *strict, *forward)
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
    pub(in crate::kernel) fn get(&self, term: &MachineTerm) -> Option<&Bounds> {
        self.get_operand(V::Legacy(term))
    }
    pub(in crate::kernel) fn get_operand(&self, term: V<'_>) -> Option<&Bounds> {
        self.endpoints.get(&Key::for_format(self.format?, term))
    }
    /// Select the original source of exactly this edge, without walking the
    /// endpoint's other bounds or materializing either operand.
    pub(in crate::kernel) fn exact_source(
        &self,
        left: V<'_>,
        right: V<'_>,
        strict: bool,
    ) -> Option<&Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        let format = self.format?;
        let left = Key::for_format(format, left);
        let right = Key::for_format(format, right);
        self.endpoints
            .get(&left)?
            .entries
            .get(&(left, right, strict, true))?
            .iter()
            .next()
    }

    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        self.format == other.format && self.endpoints.shares_root_with(&other.endpoints)
    }
    pub(super) fn adjust(&mut self, view: &NativeComparisonView<'_>, source: &Proposition) {
        self.format = Some(view.format);
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = view.relation == Relation::Less;
        let written_signed = matches!(source, Proposition::ConditionIs(condition, true)
            if crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
                .is_some_and(|view| view.format == MachineIntegerType::Int32 && !view.negated
                    && matches!(view.relation, CompareRelation::LessThan | CompareRelation::LessEqual)));
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
                let sources = sources.with_value(source.clone());
                bounds.entries = if sources.is_empty() {
                    bounds.entries.without_key(&bound)
                } else {
                    bounds.entries.with_inserted(bound.clone(), sources)
                };
                if written_signed {
                    let sources = bounds
                        .written_signed
                        .get(&bound)
                        .cloned()
                        .unwrap_or_default();
                    let sources = sources.with_value(source.clone());
                    bounds.written_signed = if sources.is_empty() {
                        bounds.written_signed.without_key(&bound)
                    } else {
                        bounds.written_signed.with_inserted(bound.clone(), sources)
                    };
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

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct Edges {
    entries: PersistentMap<(Key, bool), ()>,
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
    ) {
        self.format = Some(format);
        let from = Key::canonical(format, from);
        let edge = (Key::canonical(format, to), strict);
        let mut edges = self.endpoints.get(&from).cloned().unwrap_or_default();
        edges.entries = edges.entries.with_inserted(edge, ());

        self.endpoints = if edges.entries.is_empty() {
            self.endpoints.without_key(&from)
        } else {
            self.endpoints.with_inserted(from, edges)
        };
    }
}
