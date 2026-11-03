//! Endpoint-selected equalities and contiguous excluded-value runs.
//! Admission changes only the written endpoints; queries never enumerate facts.
use super::*;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{MachineOperandView, equality_graph::MachineAtom};
use crate::persistent::{PersistentMap, PersistentSet};

// Arithmetic has shared syntax identities. Opaque legacy leaves must stay in
// this context's index: globally interning a memory load compares snapshots
// from independent verification arenas and charges unrelated memory contents.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel) enum ScalarOperandKey {
    Shared(MachineAtom),
    Written(Bitvector32Term),
}

impl ScalarOperandKey {
    pub(in crate::kernel) fn operand_view(&self) -> MachineOperandView<'_> {
        match self {
            Self::Shared(term) => term.operand_view(),
            Self::Written(term) => MachineOperandView::Legacy(term),
        }
    }

    pub(super) fn canonical(ty: MachineIntegerType, view: MachineOperandView<'_>) -> Self {
        match view {
            MachineOperandView::Shared(_) => Self::for_format(ty, view),
            MachineOperandView::Legacy(term) => Self::for_format(
                ty,
                MachineOperandView::Legacy(&crate::kernel::eval::canonical_term(term)),
            ),
        }
    }

    pub(in crate::kernel) fn new(view: MachineOperandView<'_>) -> Self {
        Self::for_format(MachineIntegerType::Int32, view)
    }

    pub(in crate::kernel) fn for_format(
        ty: MachineIntegerType,
        view: MachineOperandView<'_>,
    ) -> Self {
        match view {
            MachineOperandView::Shared(_) => Self::Shared(MachineAtom::from_operand(ty, view)),
            MachineOperandView::Legacy(term) => {
                if let Some(shared) =
                    crate::kernel::KernelTermImport::default().machine_arithmetic(ty, term)
                {
                    Self::Shared(MachineAtom::from_operand(
                        ty,
                        MachineOperandView::Shared(&shared),
                    ))
                } else {
                    Self::Written(term.clone())
                }
            }
        }
    }
}

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
    literals: PersistentMap<ScalarOperandKey, PersistentSet<(ConditionTerm, bool)>>,
    equalities: PersistentMap<Bitvector32Term, PersistentSet<ConditionTerm>>,
    exclusions: PersistentMap<ScalarOperandKey, Exclusions>,
}

impl CheckedScalarFacts {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        let Some(view) = comparison_view(condition, value) else {
            return;
        };
        if !matches!(
            view.format,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32
        ) {
            return;
        }
        let equal = match view.relation {
            Relation::Equal => true,
            Relation::NotEqual => false,
            _ => return,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        for (endpoint, other) in [(left, right), (right, left)] {
            crate::instrumentation::record_deterministic_work(1);
            let number = other.word32_constant().map(|bits| i64::from(bits as i32));
            if equal && number.is_some() {
                let key = ScalarOperandKey::new(endpoint);
                let sources = self.literals.get(&key).cloned().unwrap_or_default();
                let source = (condition.clone(), value);
                let sources = if insert {
                    sources.with_value(source)
                } else {
                    sources.without_value(&source)
                };
                self.literals = if sources.is_empty() {
                    self.literals.without_key(&key)
                } else {
                    self.literals.with_inserted(key.clone(), sources)
                };
            }
            // Memory matching still consumes native written conditions. Keep
            // its unique-source policy separate from semantic scalar queries.
            if let MachineOperandView::Legacy(endpoint) = endpoint
                && matches!(
                    condition,
                    ConditionTerm::Compare {
                        relation: CompareRelation::Equal,
                        ..
                    }
                )
                && value
            {
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
            }
            if !equal && let Some(number) = number {
                let key = ScalarOperandKey::new(endpoint);
                let alias = match endpoint {
                    MachineOperandView::Shared(_) => None,
                    MachineOperandView::Legacy(term) => {
                        let canonical = crate::kernel::eval::canonical_term(term);
                        (canonical != *term)
                            .then(|| ScalarOperandKey::new(MachineOperandView::Legacy(&canonical)))
                    }
                };
                for key in std::iter::once(key).chain(alias) {
                    let mut excluded = self.exclusions.get(&key).cloned().unwrap_or_default();
                    excluded.adjust(number, insert);
                    self.exclusions = if excluded.counts.is_empty() {
                        self.exclusions.without_key(&key)
                    } else {
                        self.exclusions.with_inserted(key, excluded)
                    };
                }
            }
        }
    }

    pub(super) fn literal_equality(
        &self,
        term: MachineOperandView<'_>,
    ) -> Option<&(ConditionTerm, bool)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select literal equality", 1);
        crate::instrumentation::record_deterministic_work(1);
        let key = ScalarOperandKey::new(term);
        self.literals.get(&key)?.iter().next()
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
        term: MachineOperandView<'_>,
        lower: i64,
        upper: i64,
    ) -> (i64, i64) {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read excluded interval endpoints", 1);
        crate::instrumentation::record_deterministic_work(1);
        let key = ScalarOperandKey::new(term);
        let Some(excluded) = self.exclusions.get(&key) else {
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

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/checked_scalar_facts/tests.rs");
}
