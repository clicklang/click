//! Endpoint-selected equalities and contiguous excluded-value runs.
//! Admission changes only the written endpoints; queries never enumerate facts.
use super::*;
use crate::kernel::integer_exclusions::ExcludedIntegers;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{MachineOperandView, equality_graph::MachineAtom};
use crate::persistent::{PersistentMap, PersistentSet};

// Arithmetic has shared syntax identities. Opaque legacy leaves must stay in
// this context's index: globally interning a memory load compares states
// from independent verification arenas and charges unrelated memory contents.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) enum ScalarOperandKey {
    Shared(MachineAtom),
    Written(OldMachineTerm),
}

impl ScalarOperandKey {
    pub(in crate::kernel) fn operand_view(&self) -> MachineOperandView<'_> {
        match self {
            Self::Shared(term) => term.operand_view(),
            Self::Written(term) => MachineOperandView::Old(term),
        }
    }

    pub(super) fn canonical(ty: MachineIntegerType, view: MachineOperandView<'_>) -> Self {
        match view {
            MachineOperandView::Shared(_) => Self::for_format(ty, view),
            MachineOperandView::Old(term) => Self::for_format(
                ty,
                MachineOperandView::Old(&crate::kernel::eval::canonical_term(term)),
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
        // Both 32-bit literal spellings denote the same word at this format.
        // Normalize only the key's fixed-size literal; retain each fact's
        // original operand and source proposition unchanged.
        let literal = (ty.format().bits() == 32)
            .then(|| view.literal())
            .flatten()
            .filter(|literal| matches!(literal, crate::kernel::uint32_constant!(_)))
            .map(OldMachineTerm::constant_word32);
        let view = literal
            .as_ref()
            .map(MachineOperandView::Old)
            .unwrap_or(view);
        match view {
            MachineOperandView::Shared(_) => {
                Self::Shared(MachineAtom::from_numeric_operand(ty, view))
            }
            MachineOperandView::Old(term) => {
                if matches!(term, OldMachineTerm::ClickFunctionApplication { .. }) {
                    // A call retains its typed argument identity regardless
                    // of the producer's native/shared carrier choice.
                    return Self::Shared(MachineAtom::from_numeric_operand(ty, view));
                }
                // Leaf imports have fixed work. Retaining them merely changes
                // cold/warm accounting; only compound operands avoid a walk.
                if matches!(
                    term,
                    OldMachineTerm::Variable(_) | OldMachineTerm::Constant { .. }
                ) && let Some(shared) =
                    crate::kernel::KernelTermImport::default().machine_arithmetic(ty, term)
                {
                    return Self::Shared(MachineAtom::from_numeric_operand(
                        ty,
                        MachineOperandView::Shared(&shared),
                    ));
                }
                if let Some(shared) =
                    crate::kernel::SharedMachineIntegerTerm::import_arithmetic(ty, term)
                {
                    Self::Shared(MachineAtom::from_numeric_operand(ty, shared.operand_view()))
                } else if selected_call_expression(view) {
                    // Only a cold import needs this selected syntax walk;
                    // retained native imports above keep repeated lookup work.
                    Self::Shared(MachineAtom::from_numeric_operand(ty, view))
                } else {
                    Self::Written(term.clone())
                }
            }
        }
    }
}

// Inspect only the selected numeric syntax, never call arguments, states,
// or ambient facts. Other opaque leaves keep their existing context-local key.
fn selected_call_expression(root: MachineOperandView<'_>) -> bool {
    let mut pending = vec![root];
    let mut has_call = false;
    while let Some(view) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if matches!(
            view,
            MachineOperandView::Old(OldMachineTerm::ClickFunctionApplication { .. })
        ) {
            has_call = true;
        } else if view.variable().is_some() || view.literal().is_some() {
        } else if let Some((_, _, operands)) = view.binary() {
            pending.extend(operands);
        } else if let Some((_, _, operand)) = view.unary() {
            pending.push(operand);
        } else if let Some((_, _, _, operand)) = view.cast() {
            pending.push(operand);
        } else {
            return false;
        }
    }
    has_call
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct CheckedScalarFacts {
    literals: PersistentMap<ScalarOperandKey, PersistentSet<(ConditionTerm, bool)>>,
    equalities: PersistentMap<OldMachineTerm, PersistentSet<ConditionTerm>>,
    exclusions: PersistentMap<ScalarOperandKey, ExcludedIntegers>,
}

impl CheckedScalarFacts {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool) {
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
                let sources = sources.with_value(source);
                self.literals = if sources.is_empty() {
                    self.literals.without_key(&key)
                } else {
                    self.literals.with_inserted(key.clone(), sources)
                };
            }
            // SymbolicMemory matching still consumes native written conditions. Keep
            // its unique-source policy separate from semantic scalar queries.
            if let MachineOperandView::Old(endpoint) = endpoint
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
                let sources = sources.with_value(condition.clone());
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
                    MachineOperandView::Old(term) => {
                        let canonical = crate::kernel::eval::canonical_term(term);
                        (canonical != *term)
                            .then(|| ScalarOperandKey::new(MachineOperandView::Old(&canonical)))
                    }
                };
                for key in std::iter::once(key).chain(alias) {
                    let mut excluded = self.exclusions.get(&key).cloned().unwrap_or_default();
                    excluded.insert(i128::from(number));
                    self.exclusions.insert(key, excluded);
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

    pub(super) fn singleton_equality(&self, term: &OldMachineTerm) -> Option<&ConditionTerm> {
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
            .containing(i128::from(lower))
            .map_or(lower, |(_, end)| (end + 1).min(i128::from(upper)) as i64);
        let upper = excluded
            .containing(i128::from(upper))
            .map_or(upper, |(start, _)| {
                (start - 1).max(i128::from(lower)) as i64
            });
        (lower, upper)
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/checked_scalar_facts/tests.rs");
}
