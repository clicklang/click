//! Selected source queries; enumeration carries exact premises, not new authority.
use super::*;
use crate::kernel::assumptions::load_state_and_pointer;
use crate::kernel::assumptions::{parameter_alias_bucket, parameter_partition_variable};
use crate::kernel::reasoning::memories_match_for_pointer_load;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{ConditionTerm, Proposition};
use std::collections::BTreeSet;

impl EqualityGraph {
    pub(in crate::kernel) fn offsets_with_an_alias_at_root(
        &self,
        root: &Option<AddressOffset>,
    ) -> Vec<AddressOffset> {
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

    pub(in crate::kernel) fn has_address_base_aliases(&self) -> bool {
        !self.admitted.address_base_aliases.is_empty()
    }

    pub(in crate::kernel) fn exact_pointer_offset_aliases(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = Address> + '_ {
        let block = pointer.base.clone();
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .into_iter()
            .flat_map(|aliases| aliases.iter())
            .map(move |offset| Address {
                base: block.clone(),
                offset: offset.clone(),
            })
    }

    pub(in crate::kernel) fn exact_pointer_offset_alias_count(&self, pointer: &Address) -> usize {
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .map_or(0, |aliases| aliases.len())
    }

    pub(in crate::kernel) fn exactly_aliased_pointers(
        &self,
    ) -> impl ExactSizeIterator<Item = &Address> {
        self.admitted.address_base_aliases.keys()
    }

    /// A unique directly stated alias, selected by cached bucket length.
    /// Multiple alternatives belong to premise search, not checked lookup.
    pub(in crate::kernel) fn unique_exact_pointer_alias(
        &self,
        pointer: &Address,
    ) -> Option<&Address> {
        let aliases = self.admitted.address_base_aliases.get(pointer)?;
        if aliases.len() != 1 {
            return None;
        }
        aliases.iter().next().map(|(alias, _)| alias)
    }

    pub(in crate::kernel) fn exact_pointer_aliases(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = &Address> {
        self.admitted
            .address_base_aliases
            .get(pointer)
            .into_iter()
            .flat_map(|aliases| aliases.iter().map(|(alias, _)| alias))
    }

    pub(in crate::kernel) fn exact_uint64_equalities(
        &self,
        term: &OldMachineTerm,
    ) -> impl Iterator<Item = (&OldMachineTerm, &ConditionTerm)> {
        self.exact_uint64_equalities_view(crate::kernel::MachineOperandView::Old(term))
    }

    pub(in crate::kernel) fn exact_uint64_equalities_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> impl Iterator<Item = (&OldMachineTerm, &ConditionTerm)> {
        self.admitted
            .bitvector64_equality_facts
            .get(
                &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                    MachineIntegerType::UInt64,
                    term,
                ),
            )
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
    pub(in crate::kernel) fn recorded_uint64_equals(
        &self,
        term: &OldMachineTerm,
    ) -> Vec<(OldMachineTerm, ConditionTerm)> {
        let exact = self
            .admitted
            .bitvector64_equality_facts
            .get(
                &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                    MachineIntegerType::UInt64,
                    crate::kernel::MachineOperandView::Old(term),
                ),
            )
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
        let Some((query_memory, pointer, kind)) = load_state_and_pointer(term) else {
            return exact;
        };
        let mut transported = Vec::new();
        let candidates = self
            .admitted
            .wide_load_sources
            .get(&(pointer.clone(), kind));
        for condition in candidates.into_iter().flat_map(|sources| sources.iter()) {
            crate::instrumentation::record_deterministic_work(1);
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                continue;
            };
            for (side, other) in [(left, right), (right, left)] {
                let Some((fact_memory, fact_pointer, fact_kind)) = load_state_and_pointer(side)
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
    pub(in crate::kernel) fn exact_literal_sources(
        &self,
        term: &OldMachineTerm,
    ) -> Option<&crate::persistent::PersistentMap<ConditionTerm, i64>> {
        self.exact_literal_sources_view(crate::kernel::MachineOperandView::Old(term))
    }

    pub(in crate::kernel) fn exact_literal_sources_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<&crate::persistent::PersistentMap<ConditionTerm, i64>> {
        self.admitted
            .exact_constant_equalities
            .get(&crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::new(term))
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn has_parameter_store_alias_sources(&self, pointer: &Address) -> bool {
        let bucket = parameter_alias_bucket(pointer);
        self.admitted
            .wide_pointer_alias_endpoints_by_object
            .contains_key(&bucket)
            || self
                .admitted
                .pointer_alias_endpoints_by_object
                .contains_key(&bucket)
            || parameter_partition_variable(&bucket).is_some_and(|variable| {
                self.exact_uint64_equalities(&OldMachineTerm::Variable(*variable))
                    .next()
                    .is_some()
            })
    }

    pub(in crate::kernel) fn parameter_store_numeric_connectivity(
        &self,
        base: Option<&Address>,
    ) -> Option<&super::NumericAddressConnectivity> {
        // A write can use the numeric projection unless its own component
        // can reach an exact pointer edge or a raw coordinate equality.
        // Cache warm-up names no write.
        let connectivity = &self.admitted.numeric_address_connectivity;
        base.is_none_or(|base| {
            !connectivity.reaches_raw_store_coordinate(base)
                && (self.admitted.address_base_aliases.is_empty()
                    || (!self
                        .admitted
                        .pointer_alias_endpoints_by_object
                        .contains_key(base)
                        && !connectivity.reaches_pointer_alias(base)))
        })
        .then_some(connectivity)
    }

    pub(in crate::kernel) fn parameter_store_alias_bases(
        &self,
        base: &Address,
    ) -> Option<BTreeSet<Address>> {
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
                if self.admitted.bitvector64_equality_facts.contains_key(
                    &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                        MachineIntegerType::UInt64,
                        crate::kernel::MachineOperandView::Old(&OldMachineTerm::Variable(
                            *variable,
                        )),
                    ),
                ) {
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
                if let Some(address) = term.address_pointer() {
                    pending.push(address.clone());
                }
                if let Some(neighbors) = self.admitted.bitvector64_equality_facts.get(
                    &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                        MachineIntegerType::UInt64,
                        crate::kernel::MachineOperandView::Old(&term),
                    ),
                ) {
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
                    if let Some(aliases) = self.admitted.address_base_aliases.get(endpoint) {
                        pending.extend(aliases.keys().cloned());
                    }
                }
            }
        }
        Some(bases)
    }

    pub(in crate::kernel) fn addresses_numerically_connected(
        &self,
        left: &Address,
        right: &Address,
    ) -> bool {
        self.admitted
            .numeric_address_connectivity
            .connected(left, right)
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn reset_closure(&mut self) {
        let sources = {
            let state = self.state.lock().expect("equality graph");
            (
                state.pointer_fact_inputs.clone(),
                state.condition_pointer_fact_inputs.clone(),
            )
        };
        let admitted = std::mem::take(&mut self.admitted);
        *self = Self::default();
        self.admitted = admitted;
        for (_, source) in sources.0.iter().chain(sources.1.iter()) {
            self.adjust_pointer_fact_source(source, true);
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
    pub(in crate::kernel) fn has_wide_pointer_sources(&self) -> bool {
        !self
            .admitted
            .wide_pointer_alias_endpoints_by_object
            .is_empty()
    }
}
