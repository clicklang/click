//! Exact source evidence owned by the service, distinct from closure queries.
use super::*;
use crate::kernel::assumptions::equality_graph_term_key;
use crate::kernel::{BitvectorEqualityDerivationStep, ConditionTerm, Proposition};
use std::collections::{BTreeMap, BTreeSet};

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
        if !matches!(condition, ConditionTerm::Bitvector32Equal(..))
            && condition.pointer_offset_sides().is_none()
        {
            return;
        }
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
            let pair = match condition {
                ConditionTerm::Bitvector32Equal(a, b) => {
                    Some((a.as_ref().clone(), b.as_ref().clone()))
                }
                other => other.pointer_offset_sides().and_then(|(a, b)| {
                    crate::kernel::reasoning::int32_element_index_from_offset(a)
                        .zip(crate::kernel::reasoning::int32_element_index_from_offset(b))
                }),
            };
            let Some((a, b)) = pair else {
                return;
            };
            let a = equality_graph_term_key(&a);
            let b = equality_graph_term_key(&b);
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
        let left_index = crate::kernel::reasoning::int32_element_index_from_offset(left)?;
        let right_index = crate::kernel::reasoning::int32_element_index_from_offset(right)?;
        self.admitted
            .scalar_evidence_inputs
            .get(&equality_graph_term_key(&left_index))?
            .get(&equality_graph_term_key(&right_index))?
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

    pub(in crate::kernel) fn has_scalar_evidence(&self, term: &Bitvector32Term) -> bool {
        self.admitted
            .scalar_evidence_inputs
            .contains_key(&equality_graph_term_key(term))
    }

    pub(in crate::kernel) fn scalar_evidence_class(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<Bitvector32Term> {
        if self.admitted.scalar_evidence_inputs.is_empty() {
            return Vec::new();
        }
        let start = equality_graph_term_key(term);
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
        seen.remove(term);
        seen.into_iter().collect()
    }

    pub(in crate::kernel) fn exact_scalar_evidence_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<Vec<BitvectorEqualityDerivationStep>> {
        if left == right
            || equality_graph_term_key(left) != *left
            || equality_graph_term_key(right) != *right
        {
            return None;
        }
        let mut visited = BTreeSet::new();
        let mut parents = BTreeMap::<Bitvector32Term, (Bitvector32Term, Proposition)>::new();
        let mut pending = vec![left.clone()];
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if !visited.insert(current.clone()) {
                continue;
            }
            if current == *right {
                let mut path = Vec::new();
                let mut cursor = current;
                while cursor != *left {
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
                    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), true) =
                        premise
                    else {
                        return None;
                    };
                    (equality_graph_term_key(a) == **a && equality_graph_term_key(b) == **b)
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
    /// Literal discovery constrained to exact written scalar premises.
    pub(in crate::kernel) fn direct_scalar_constant(&self, term: &Bitvector32Term) -> Option<u32> {
        if let Some(value) = term.as_const() {
            return Some(value);
        }
        use crate::kernel::assumptions::SignedConstantResolution as R;
        if matches!(
            self.scalar_constant_class(term).map(|(_, value)| value),
            None | Some(R::Unknown)
        ) {
            return None;
        }
        let mut pending = vec![term.clone()];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(value) = current.as_const() {
                return Some(value);
            }
            let mut sources = BTreeMap::new();
            if let Some(neighbors) = self
                .admitted
                .scalar_evidence_inputs
                .get(&equality_graph_term_key(&current))
            {
                for (_, premises) in neighbors.iter() {
                    for (condition, _) in premises.iter() {
                        let ConditionTerm::Bitvector32Equal(a, b) = condition else {
                            continue;
                        };
                        let other = if **a == current {
                            b
                        } else if **b == current {
                            a
                        } else {
                            continue;
                        };
                        sources.insert(condition, other.as_ref());
                    }
                }
            }
            for other in sources.values() {
                crate::instrumentation::record_deterministic_work(1);
                crate::kernel::assumptions::count_condition_fact_visit();
                pending.push((*other).clone());
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
