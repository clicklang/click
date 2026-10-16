//! Selected source queries; enumeration carries exact premises, not new authority.
use super::*;
use crate::kernel::assumptions::load_snapshot_and_pointer;
use crate::kernel::assumptions::{parameter_alias_bucket, parameter_partition_variable};
use crate::kernel::reasoning::memories_match_for_pointer_load;
use crate::kernel::{ConditionTerm, Proposition, PureFunctionArgument};
use std::collections::BTreeSet;

impl EqualityGraph {
    pub(in crate::kernel) fn offsets_with_an_alias_at_root(
        &self,
        root: &Option<PointerOffsetTerm>,
    ) -> Vec<PointerOffsetTerm> {
        self.admitted
            .pointer_offset_aliases_by_root
            .get(root)
            .into_iter()
            .flat_map(|pairs| pairs.iter())
            .map(|(aliased, _)| {
                crate::instrumentation::record_deterministic_work(1);
                aliased.clone()
            })
            .collect()
    }

    pub(in crate::kernel) fn has_pointer_block_aliases(&self) -> bool {
        !self.admitted.pointer_block_aliases.is_empty()
    }

    pub(in crate::kernel) fn exact_pointer_offset_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = Pointer> + '_ {
        let block = pointer.block.clone();
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .into_iter()
            .flat_map(|aliases| aliases.iter())
            .map(move |offset| Pointer {
                block: block.clone(),
                offset: offset.clone(),
            })
    }

    pub(in crate::kernel) fn exact_pointer_offset_alias_count(&self, pointer: &Pointer) -> usize {
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .map_or(0, |aliases| aliases.len())
    }

    pub(in crate::kernel) fn exactly_aliased_pointers(
        &self,
    ) -> impl ExactSizeIterator<Item = &Pointer> {
        self.admitted.pointer_block_aliases.keys()
    }

    pub(in crate::kernel) fn exact_pointer_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = &Pointer> {
        self.admitted
            .pointer_block_aliases
            .get(pointer)
            .into_iter()
            .flat_map(|aliases| aliases.iter().map(|(alias, _)| alias))
    }

    pub(in crate::kernel) fn exact_uint64_equalities(
        &self,
        term: &Bitvector32Term,
    ) -> impl Iterator<Item = (&Bitvector32Term, &ConditionTerm)> {
        self.admitted
            .bitvector64_equality_facts
            .get(term)
            .into_iter()
            .flat_map(|neighbors| neighbors.iter())
    }

    pub(in crate::kernel) fn algebraic_constructor_field_sources(
        &self,
        field: &Proposition,
    ) -> impl Iterator<Item = &(Proposition, usize)> {
        self.admitted
            .algebraic_constructor_field_equalities
            .get(field)
            .into_iter()
            .flat_map(|sources| sources.iter().map(|(source, ())| source))
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn rebuild_from_inputs(&mut self) {
        let mut classes = EqualityGraph::default();
        for (left, aliases) in self.admitted.pointer_block_aliases.iter() {
            for (right, _) in aliases.iter() {
                if left < right {
                    classes.add_equality(left, right);
                }
            }
        }
        for (left, aliases) in self.admitted.pointer_offset_aliases.iter() {
            for right in aliases.iter() {
                if left < right {
                    classes.add_offset_equality(left, right);
                }
            }
        }
        for ((left, right), _) in self.admitted.uint64_graph_equalities.iter() {
            classes.add_uint64_equality(left.value(), right.value());
        }
        for ((left, right), _) in self.admitted.algebraic_graph_equalities.iter() {
            let PureFunctionArgument::Algebraic(left) = &left.arguments()[0] else {
                unreachable!()
            };
            let PureFunctionArgument::Algebraic(right) = &right.arguments()[0] else {
                unreachable!()
            };
            classes.add_algebraic_equality(left, right);
        }
        for (left, right) in self.admitted.pointer_value_equalities.iter() {
            classes.add_pointer_value_equality(left, right);
        }
        for ((left, right), _) in self.admitted.int32_graph_equalities.iter() {
            classes.add_int32_equality(left.value(), right.value());
        }
        for (_, definitions) in self.admitted.typed_pointer_read_definitions.iter() {
            for ((_, address), (value, memory)) in definitions.iter() {
                classes.add_equality(value, &Pointer::loaded_value(memory, address));
            }
        }
        for ((pointer, alignment), _) in self.admitted.pointer_alignment_facts.iter() {
            classes.register_alignment(pointer, *alignment);
        }
        for (condition, value) in self.admitted.congruence_conditions.iter() {
            classes.add_condition(condition, *value);
        }
        let sources = self
            .state
            .lock()
            .expect("equality graph")
            .pointer_predicate_inputs
            .clone();
        for (_, source) in sources.iter() {
            classes.adjust_pointer_predicate_source(source, true);
        }
        classes.admitted = self.admitted.clone();
        *self = classes;
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn recorded_uint64_equals(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<(Bitvector32Term, ConditionTerm)> {
        let exact = self
            .admitted
            .bitvector64_equality_facts
            .get(term)
            .map(|neighbors| {
                neighbors
                    .iter()
                    .map(|(equal, fact)| (equal.clone(), fact.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        if !exact.is_empty() {
            return exact;
        }
        let Some((query_memory, pointer, kind)) = load_snapshot_and_pointer(term) else {
            return exact;
        };
        let mut transported = Vec::new();
        let candidates = self
            .admitted
            .wide_load_sources
            .get(&(pointer.clone(), kind));
        for condition in candidates.into_iter().flat_map(|sources| sources.iter()) {
            crate::instrumentation::record_deterministic_work(1);
            let ConditionTerm::Bitvector64Equal(left, right) = condition else {
                continue;
            };
            for (side, other) in [(left, right), (right, left)] {
                let Some((fact_memory, fact_pointer, fact_kind)) = load_snapshot_and_pointer(side)
                else {
                    continue;
                };
                if fact_pointer != pointer
                    || fact_kind != kind
                    || !memories_match_for_pointer_load(&fact_memory, &query_memory, &pointer)
                {
                    continue;
                }
                transported.push((other.as_ref().clone(), condition.clone()));
            }
        }
        transported
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn has_uint64_source(&self, term: &Bitvector32Term) -> bool {
        self.admitted.bitvector64_equality_facts.contains_key(term)
    }
    pub(in crate::kernel) fn exact_literal_sources(
        &self,
        term: &Bitvector32Term,
    ) -> Option<&crate::persistent::PersistentMap<ConditionTerm, i64>> {
        self.admitted.exact_constant_equalities.get(term)
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn parameter_store_alias_bases(
        &self,
        base: &Pointer,
    ) -> Option<BTreeSet<Pointer>> {
        let mut pending = vec![base.clone()];
        let mut seen = BTreeSet::new();
        let mut bases = BTreeSet::new();
        let mut visited_terms = BTreeSet::new();
        while let Some(pointer) = pending.pop() {
            let pointer = parameter_alias_bucket(&pointer);
            if !seen.insert(pointer.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(variable) = parameter_partition_variable(&pointer) {
                if self
                    .admitted
                    .bitvector64_equality_facts
                    .contains_key(&Bitvector32Term::Variable(*variable))
                {
                    return None;
                }
                bases.insert(pointer.clone());
            }
            let mut terms: Vec<_> = self
                .admitted
                .wide_pointer_alias_endpoints_by_object
                .get(&pointer)
                .into_iter()
                .flat_map(|endpoints| endpoints.iter().cloned())
                .collect();
            while let Some(term) = terms.pop() {
                if !visited_terms.insert(term.clone()) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if let Bitvector32Term::PointerAddress(address) = &term {
                    pending.push(address.as_ref().clone());
                }
                if let Some(neighbors) = self.admitted.bitvector64_equality_facts.get(&term) {
                    terms.extend(neighbors.keys().cloned());
                }
            }
            if let Some(endpoints) = self
                .admitted
                .pointer_alias_endpoints_by_object
                .get(&pointer)
            {
                for endpoint in endpoints.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(aliases) = self.admitted.pointer_block_aliases.get(endpoint) {
                        pending.extend(aliases.keys().cloned());
                    }
                }
            }
        }
        Some(bases)
    }

    pub(in crate::kernel) fn address_connected_objects(
        &self,
        pointer: &Pointer,
    ) -> BTreeSet<Pointer> {
        let mut reached_objects = BTreeSet::new();
        if self
            .admitted
            .wide_pointer_alias_endpoints_by_object
            .is_empty()
        {
            return reached_objects;
        }
        let mut pending = vec![parameter_alias_bucket(pointer)];
        let mut seen = BTreeSet::new();
        let mut visited_terms = BTreeSet::new();
        while let Some(bucket) = pending.pop() {
            if !seen.insert(bucket.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let mut terms: Vec<_> = self
                .admitted
                .wide_pointer_alias_endpoints_by_object
                .get(&bucket)
                .into_iter()
                .flat_map(|endpoints| endpoints.iter().cloned())
                .collect();
            while let Some(term) = terms.pop() {
                if !visited_terms.insert(term.clone()) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if let Bitvector32Term::PointerAddress(address) = &term {
                    let reached = parameter_alias_bucket(address);
                    reached_objects.insert(reached.clone());
                    pending.push(reached);
                }
                if let Some(neighbors) = self.admitted.bitvector64_equality_facts.get(&term) {
                    terms.extend(neighbors.keys().cloned());
                }
            }
        }
        reached_objects
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn reset_closure(&mut self) {
        let sources = self
            .state
            .lock()
            .expect("equality graph")
            .pointer_predicate_inputs
            .clone();
        let admitted = std::mem::take(&mut self.admitted);
        *self = Self::default();
        self.admitted = admitted;
        for (_, source) in sources.iter() {
            self.adjust_pointer_predicate_source(source, true);
        }
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn identity_only(&self) -> Self {
        let mut identity = Self::default();
        identity.admitted.typed_pointer_read_definitions =
            self.admitted.typed_pointer_read_definitions.clone();
        identity
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn exact_offset_aliases(
        &self,
        offset: &PointerOffsetTerm,
    ) -> Option<&crate::persistent::PersistentSet<PointerOffsetTerm>> {
        self.admitted.pointer_offset_aliases.get(offset)
    }
    pub(in crate::kernel) fn alias_endpoints_at_offset(
        &self,
        offset: &PointerOffsetTerm,
    ) -> impl Iterator<Item = &Pointer> {
        self.admitted
            .pointer_block_aliases_by_offset
            .get(offset)
            .into_iter()
            .flat_map(|pointers| pointers.iter())
    }
    pub(in crate::kernel) fn has_wide_pointer_sources(&self) -> bool {
        !self
            .admitted
            .wide_pointer_alias_endpoints_by_object
            .is_empty()
    }
}
