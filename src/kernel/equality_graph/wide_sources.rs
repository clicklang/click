//! Exact wide equality premises indexed by shallow operand identity.
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{ConditionTerm, MachineIntegerType, MachineOperandView, Proposition};
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct WideEqualitySources {
    endpoints: PersistentMap<Key, PersistentMap<Key, PersistentSet<Proposition>>>,
}

impl WideEqualitySources {
    pub(in crate::kernel) fn adjust(
        &mut self,
        condition: &ConditionTerm,
        truth: bool,
        insert: bool,
    ) {
        let Some(view) = comparison_view(condition, truth) else {
            return;
        };
        if view.relation != Relation::Equal || view.format.format().bits() != 64 {
            return;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| Key::for_format(MachineIntegerType::UInt64, operand.operand_view()));
        let source = Proposition::ConditionIs(condition.clone(), truth);
        for (own, other) in [(&left, &right), (&right, &left)] {
            let mut neighbors = self.endpoints.get(own).cloned().unwrap_or_default();
            let sources = neighbors.get(other).cloned().unwrap_or_default();
            let sources = if insert {
                sources.with_value(source.clone())
            } else {
                sources.without_value(&source)
            };
            if sources.is_empty() {
                neighbors.remove(other);
            } else {
                neighbors.insert(other.clone(), sources);
            }
            if neighbors.is_empty() {
                self.endpoints.remove(own);
            } else {
                self.endpoints.insert(own.clone(), neighbors);
            }
        }
    }

    pub(in crate::kernel) fn neighbors(
        &self,
        operand: MachineOperandView<'_>,
    ) -> impl Iterator<Item = (MachineOperandView<'_>, &Proposition)> {
        self.endpoints
            .get(&Key::for_format(MachineIntegerType::UInt64, operand))
            .into_iter()
            .flat_map(|neighbors| neighbors.iter())
            .filter_map(|(other, sources)| {
                sources
                    .iter()
                    .next()
                    .map(|source| (other.operand_view(), source))
            })
    }

    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        self.endpoints.shares_root_with(&other.endpoints)
    }
}
