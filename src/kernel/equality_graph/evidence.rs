//! Exact source evidence owned by the service, distinct from closure queries.
use super::*;
use crate::kernel::assumptions::equality_graph_term_key;
use crate::kernel::{BitvectorEqualityDerivationStep, ConditionTerm, Proposition};
use crate::kernel::{
    CompareRelation, MachineIntegerType, MachineOperandView, SharedMachineIntegerTerm,
};
use std::collections::{BTreeMap, BTreeSet};

/// The two equality-graph keys a true condition records as scalar evidence:
/// the sides of an `int32` equality, or the element indexes of a true
/// pointer-offset equality. Context-free, so a fact's evidence edge is the
/// same in every context that holds it.
pub(in crate::kernel) fn scalar_evidence_pair(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(SharedMachineIntegerTerm, SharedMachineIntegerTerm)> {
    if !value {
        return None;
    }
    let (a, b) = match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: a,
            right: b,
        } => (
            evidence_key(MachineOperandView::Legacy(a)),
            evidence_key(MachineOperandView::Legacy(b)),
        ),
        ConditionTerm::IntegerEqual(..) => {
            let view =
                crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
            if view.relation != CompareRelation::Equal
                || view.negated
                || !matches!(
                    view.format,
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32
                )
            {
                return None;
            }
            (
                evidence_key(view.operands[0].operand_view()),
                evidence_key(view.operands[1].operand_view()),
            )
        }
        other => other.true_pointer_offset_sides().and_then(|(a, b)| {
            crate::kernel::reasoning::shared_element_index_from_offset(a, 4).zip(
                crate::kernel::reasoning::shared_element_index_from_offset(b, 4),
            )
        })?,
    };
    Some((a, b))
}

fn evidence_key(operand: MachineOperandView<'_>) -> SharedMachineIntegerTerm {
    match operand {
        MachineOperandView::Legacy(term) => SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            equality_graph_term_key(term),
        ),
        MachineOperandView::Shared(_) => operand.retain(MachineIntegerType::Int32),
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn adjust_scalar_evidence_input(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        if !value {
            return;
        }
        if !matches!(
            condition,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                ..
            } | ConditionTerm::IntegerEqual(..)
        ) && condition.true_pointer_offset_sides().is_none()
        {
            return;
        }
        // The new shared source form must actually be a machine equality.
        // Pure Integer equalities do not enter this coordinate index. Keep
        // the existing conservative dependency rule for pointer sources.
        let shared_pair = if matches!(condition, ConditionTerm::IntegerEqual(..)) {
            let Some(pair) = scalar_evidence_pair(condition, value) else {
                return;
            };
            Some(pair)
        } else {
            None
        };
        let (variables, deferred) = if insert {
            let mut variables = BTreeSet::new();
            let deferred =
                crate::kernel::reasoning::variable_collection::collect_condition_coordinate_index_variables(
                    condition,
                    &mut variables,
                );
            self.admitted
                .scalar_dependency_inputs
                .insert(condition.clone(), (variables.clone(), deferred));
            (variables, deferred)
        } else {
            let dependencies = self
                .admitted
                .scalar_dependency_inputs
                .get(condition)
                .cloned()
                .unwrap_or_default();
            self.admitted.scalar_dependency_inputs.remove(condition);
            dependencies
        };
        if deferred {
            if insert {
                self.admitted.scalar_deferred_inputs += 1;
            } else {
                self.admitted.scalar_deferred_inputs -= 1;
            }
        }
        for variable in variables {
            let count = self
                .admitted
                .scalar_dependencies
                .get(&variable)
                .copied()
                .unwrap_or(0);
            if insert {
                self.admitted
                    .scalar_dependencies
                    .insert(variable, count + 1);
            } else if count > 1 {
                self.admitted
                    .scalar_dependencies
                    .insert(variable, count - 1);
            } else {
                self.admitted.scalar_dependencies.remove(&variable);
            }
        }
        let (a, b) = if insert {
            let Some((a, b)) = shared_pair.or_else(|| scalar_evidence_pair(condition, value))
            else {
                return;
            };
            self.admitted
                .scalar_evidence_keys
                .insert(condition.clone(), (a.clone(), b.clone()));
            (a, b)
        } else {
            let Some(pair) = self.admitted.scalar_evidence_keys.get(condition).cloned() else {
                return;
            };
            self.admitted.scalar_evidence_keys.remove(condition);
            pair
        };
        for (key, other) in [(&a, &b), (&b, &a)] {
            crate::instrumentation::record_deterministic_work(1);
            let neighbors = self
                .admitted
                .scalar_evidence_inputs
                .get(key)
                .cloned()
                .unwrap_or_default();
            let sources = neighbors.get(other).cloned().unwrap_or_default();
            let sources = if insert {
                sources.with_inserted(
                    condition.clone(),
                    Proposition::ConditionIs(condition.clone(), true),
                )
            } else {
                sources.without_key(condition)
            };
            let neighbors = if sources.is_empty() {
                neighbors.without_key(other)
            } else {
                neighbors.with_inserted(other.clone(), sources)
            };
            if neighbors.is_empty() {
                self.admitted.scalar_evidence_inputs.remove(key);
            } else {
                self.admitted
                    .scalar_evidence_inputs
                    .insert(key.clone(), neighbors);
            }
        }
    }

    /// Select an exact common-base address equality by its indexed offset
    /// coordinates. The index nominates sources; their complete offset sides
    /// must still match, so this does not cancel scaling or discard a base.
    pub(in crate::kernel) fn exact_pointer_offset_equality_source(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> Option<&Proposition> {
        let left_index = crate::kernel::reasoning::shared_element_index_from_offset(left, 4)?;
        let right_index = crate::kernel::reasoning::shared_element_index_from_offset(right, 4)?;
        self.admitted
            .scalar_evidence_inputs
            .get(&left_index)?
            .get(&right_index)?
            .iter()
            .find_map(|(_, premise)| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::ConditionIs(condition, true) = premise else {
                    return None;
                };
                let (a, b) = condition.pointer_offset_sides()?;
                ((a == left && b == right) || (a == right && b == left)).then_some(premise)
            })
    }

    pub(in crate::kernel) fn scalar_evidence_class(&self, term: &MachineTerm) -> Vec<MachineTerm> {
        if self.admitted.scalar_evidence_inputs.is_empty() {
            return Vec::new();
        }
        let start = evidence_key(MachineOperandView::Legacy(term));
        if !self.admitted.scalar_evidence_inputs.contains_key(&start) {
            return Vec::new();
        }
        let mut seen = BTreeSet::from([start.clone()]);
        let mut pending = vec![start.clone()];
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(neighbors) = self.admitted.scalar_evidence_inputs.get(&current) {
                for next in neighbors.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if seen.insert(next.clone()) {
                        pending.push(next.clone());
                    }
                }
            }
        }
        seen.remove(&start);
        seen.remove(&MachineOperandView::Legacy(term).retain(MachineIntegerType::Int32));
        // This legacy search API orders candidates by native syntax, not by
        // the allocation order of retained handles.
        seen.into_iter()
            .map(|term| term.value().clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// The pointers joined to `pointer` by a chain of recorded cross-block
    /// equalities, excluding `pointer` itself: the pointer counterpart of
    /// [`Self::scalar_evidence_class`]. The edges are symmetric, so the walk
    /// costs the equalities in this one component.
    pub(in crate::kernel) fn pointer_alias_class(&self, pointer: &Pointer) -> Vec<Pointer> {
        let aliases = &self.admitted.pointer_block_aliases;
        if !aliases.contains_key(pointer) {
            return Vec::new();
        }
        let mut seen = BTreeSet::from([pointer.clone()]);
        let mut pending = vec![pointer.clone()];
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            for next in aliases
                .get(&current)
                .into_iter()
                .flat_map(|next| next.keys())
            {
                crate::instrumentation::record_deterministic_work(1);
                if seen.insert(next.clone()) {
                    pending.push(next.clone());
                }
            }
        }
        seen.remove(pointer);
        seen.into_iter().collect()
    }

    pub(in crate::kernel) fn exact_scalar_evidence_path(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<Vec<BitvectorEqualityDerivationStep>> {
        let left = left.retain(MachineIntegerType::Int32);
        let right = right.retain(MachineIntegerType::Int32);
        if left == right {
            return None;
        }
        let mut visited = BTreeSet::new();
        let mut parents =
            BTreeMap::<SharedMachineIntegerTerm, (SharedMachineIntegerTerm, Proposition)>::new();
        let mut pending = vec![left.clone()];
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if !visited.insert(current.clone()) {
                continue;
            }
            if current == right {
                let mut path = Vec::new();
                let mut cursor = current;
                while cursor != left {
                    let (source, premise) = parents.get(&cursor)?;
                    path.push(BitvectorEqualityDerivationStep {
                        source: source.clone(),
                        target: cursor,
                        premise: premise.clone(),
                    });
                    cursor = source.clone();
                }
                path.reverse();
                return Some(path);
            }
            let Some(neighbors) = self.admitted.scalar_evidence_inputs.get(&current) else {
                continue;
            };
            for (next, sources) in neighbors.iter().rev() {
                if visited.contains(next) {
                    continue;
                }
                let Some(premise) = sources.iter().find_map(|(_, premise)| {
                    let Proposition::ConditionIs(condition, true) = premise else {
                        return None;
                    };
                    let view =
                        crate::kernel::machine_integer::comparison::structural_comparison_view(
                            condition,
                        )?;
                    if view.negated
                        || view.relation != CompareRelation::Equal
                        || !matches!(
                            view.format,
                            MachineIntegerType::Int32 | MachineIntegerType::UInt32
                        )
                    {
                        return None;
                    }
                    view.operands
                        .iter()
                        .all(|operand| match operand.operand_view() {
                            MachineOperandView::Legacy(term) => {
                                equality_graph_term_key(term) == *term
                            }
                            MachineOperandView::Shared(_) => true,
                        })
                        .then_some(premise)
                }) else {
                    continue;
                };
                parents.insert(next.clone(), (current.clone(), premise.clone()));
                pending.push(next.clone());
            }
        }
        None
    }
}

impl EqualityGraph {
    /// Read a literal or one exact written equality to it; never follow a chain.
    /// The existing class summary nominates the constant, but does not supply
    /// the written premise. State that equality explicitly when a chain or
    /// arithmetic folding is needed to derive it. Ambiguous classes decline.
    pub(in crate::kernel) fn direct_scalar_constant(&self, term: &MachineTerm) -> Option<u32> {
        if let Some(value) = term.as_const() {
            return Some(value);
        }
        use crate::kernel::assumptions::SignedConstantResolution as R;
        let (_, R::Known(value)) = self.scalar_constant_class(term)? else {
            return None;
        };
        let literal = MachineTerm::constant(value as u32);
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            for (left, right) in [(term, &literal), (&literal, term)] {
                crate::instrumentation::record_deterministic_work(1);
                let condition = ConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                if self.admitted.scalar_evidence_keys.contains_key(&condition) {
                    return Some(value as u32);
                }
            }
        }
        None
    }
}

impl EqualityGraph {
    /// A selected pointer may use the flat parameter shortcut only when no
    /// admitted scalar/offset source can change its coordinate. Complex load
    /// dependencies conservatively stay on the ordinary store ladder.
    pub(in crate::kernel) fn offset_has_source_dependencies(
        &self,
        offset: &PointerOffsetTerm,
    ) -> bool {
        if self.admitted.scalar_deferred_inputs != 0 {
            return true;
        }
        let root = crate::kernel::primitives::offset_root_atom(offset);
        if self
            .admitted
            .pointer_offset_aliases_by_root
            .contains_key(&root)
        {
            return true;
        }
        let mut variables = BTreeSet::new();
        let selector = ConditionTerm::PointerOffsetEqual(
            Box::new(offset.clone()),
            Box::new(PointerOffsetTerm::Constant(0)),
        );
        if crate::kernel::reasoning::variable_collection::collect_condition_coordinate_index_variables(&selector, &mut variables) { return true; }
        variables
            .iter()
            .any(|variable| self.admitted.scalar_dependencies.contains_key(variable))
    }
}
