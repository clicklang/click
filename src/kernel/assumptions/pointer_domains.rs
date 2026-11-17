//! Read-only knowledge of a complete pointer's domain. This is a checker
//! result, not a pointer value, resource, or new proof-state term.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::kernel) enum PointerDomain {
    Unknown,
    Root,
    Selected(SubobjectBounds),
}

impl PointerDomain {
    pub(in crate::kernel) fn intrinsic(value: &PointerValue) -> Self {
        match value.bounds() {
            Some(bounds) => Self::Selected(bounds.clone()),
            None if value.bounds_are_known() => Self::Root,
            None => Self::Unknown,
        }
    }
}

/// Access descriptors already retain an opaque origin; other consumers have
/// the full value. Neither entry point reconstructs a synthetic pointer.
pub(in crate::kernel) enum PointerDomainSource<'a> {
    Value(&'a PointerValue),
    BoundsOwner(&'a Address),
}

impl<'a> From<&'a PointerValue> for PointerDomainSource<'a> {
    fn from(value: &'a PointerValue) -> Self {
        Self::Value(value)
    }
}

impl PureFactContext {
    /// Intrinsic bounds, or the cached witness for this bounds-owner class.
    /// Complete-pointer equality can establish that witness; equal numeric
    /// addresses cannot. No aliases, resources or memory history are searched,
    /// no terms are registered, and the input value remains unchanged.
    pub(in crate::kernel) fn pointer_domain<'a>(
        &self,
        source: impl Into<PointerDomainSource<'a>>,
    ) -> PointerDomain {
        let origin = match source.into() {
            PointerDomainSource::Value(value) => match PointerDomain::intrinsic(value) {
                PointerDomain::Unknown => match value.bounds_owner() {
                    Some(origin) => origin,
                    None => return PointerDomain::Unknown,
                },
                known => return known,
            },
            PointerDomainSource::BoundsOwner(origin) => origin,
        };
        self.equality_graph.opaque_pointer_domain(origin)
    }

    /// The selected-domain extension of access matching. A matching object
    /// identity is still required, and the entire offered range must fit the
    /// known selected domain. A larger enclosing owner is not evidence for a
    /// larger domain; per-access bounds checking remains a separate consumer.
    pub(super) fn selected_domain_access_matches(
        &self,
        required: (&Address, Option<&Address>),
        available: &MemoryRange,
    ) -> bool {
        let Some(origin) = required.1 else {
            return false;
        };
        if !available.carrier_bounds_known {
            return false;
        }
        let PointerDomain::Selected(bounds) =
            self.pointer_domain(PointerDomainSource::BoundsOwner(origin))
        else {
            return false;
        };
        if !self.provenance_equal(required.0, &available.provenance) {
            return false;
        }
        let (start, end, wide) = match available.wide_bounds() {
            Some((start, end)) => (start, end, true),
            None => (available.start(), available.end(), false),
        };
        // Exact typed offsets retain full-width coordinates. Check both ends
        // as positions (one-past allowed), without narrowing a uint64 range
        // or searching for another footprint with a convenient bounds.
        [start, end].into_iter().all(|bound| {
            let endpoint = available.base().offset_by_typed_elements(
                bound.clone(),
                available.element_width(),
                wide,
                wide,
            );
            self.pointer_access_in_range(
                &endpoint,
                0,
                &bounds.start,
                &0u32.into(),
                &bounds.width,
                1,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pointer(id: u64) -> PointerValue {
        PointerValue::new(Address::symbolic(Variable(id)), ProgramType::Int32Pointer)
    }
    fn equal(facts: PureFactContext, a: &PointerValue, b: &PointerValue) -> PureFactContext {
        facts.assume_condition(
            ConditionTerm::pointer_value_equal(a.clone(), b.clone()),
            true,
        )
    }
    fn member(parent: &PointerValue) -> PointerValue {
        parent
            .clone()
            .with_address(parent.pointer().offset_by_bytes(4))
            .with_bounds(Some(SubobjectBounds {
                start: parent.pointer().offset_by_bytes(4),
                width: 4u32.into(),
            }))
    }

    #[test]
    fn pointer_domain_keeps_intrinsic_and_admitted_knowledge_separate() {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = pointer(997_001);
        let selected = member(&parent);
        let returned = pointer(997_002);
        let original = returned.clone();
        let empty = PureFactContext::new();
        assert_eq!(empty.pointer_domain(&parent), PointerDomain::Unknown);
        assert_eq!(
            empty.pointer_domain(&selected),
            PointerDomain::Selected(selected.bounds().unwrap().clone())
        );
        assert_eq!(
            empty.pointer_domain(&parent.clone().with_root_bounds()),
            PointerDomain::Root
        );
        assert_eq!(empty.pointer_domain(&returned), PointerDomain::Unknown);
        for facts in [
            equal(empty.clone(), &returned, &selected),
            equal(empty.clone(), &selected, &returned),
        ] {
            assert_eq!(
                facts.pointer_domain(&returned),
                PointerDomain::Selected(selected.bounds().unwrap().clone())
            );
            assert_eq!(
                facts.pointer_domain(&parent),
                PointerDomain::Unknown,
                "narrowing a child must not narrow its parent"
            );
            assert_eq!(returned, original);
        }
        assert_eq!(
            empty.pointer_domain(&returned),
            PointerDomain::Unknown,
            "branch knowledge must not leak"
        );
    }

    #[test]
    fn pointer_domain_rejects_address_and_widened_view_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = pointer(997_011);
        let selected = member(&parent);
        let returned = pointer(997_012);
        let numeric = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(returned.pointer().clone(), selected.pointer().clone()),
            true,
        );
        assert_eq!(numeric.pointer_domain(&returned), PointerDomain::Unknown);
        let widened = equal(
            numeric.clone(),
            &returned.clone().with_root_bounds(),
            &parent.clone().with_root_bounds(),
        );
        assert_eq!(widened.pointer_domain(&returned), PointerDomain::Unknown);
        let root = equal(numeric, &returned, &parent.clone().with_root_bounds());
        assert_eq!(root.pointer_domain(&returned), PointerDomain::Root);
    }

    #[test]
    fn pointer_domain_reads_only_admitted_metadata_for_a_stored_pointer() {
        let _session = crate::kernel::VerificationSession::enter();
        let selected = member(&pointer(997_041));
        let cell = Address::symbolic(Variable(997_042));
        let memory = crate::kernel::intern_memory(
            Memory::new().store(cell.clone(), ProgramValue::Pointer(selected.clone())),
        );
        let read = PointerValue::from_read(
            Address::loaded_value(&memory, &cell),
            ProgramType::Int32Pointer,
            &memory,
            &cell,
        );
        let original = read.clone();
        let empty = PureFactContext::new();
        assert_eq!(
            empty.pointer_domain(&read),
            PointerDomain::Unknown,
            "a domain query must not recover a stored pointer from memory"
        );
        let facts = equal(empty.clone(), &read, &selected);
        assert_eq!(
            facts.pointer_domain(&read),
            PointerDomain::Selected(selected.bounds().unwrap().clone())
        );
        assert_eq!(read, original);
        assert_eq!(empty.pointer_domain(&read), PointerDomain::Unknown);
    }

    #[test]
    fn admitted_selected_domain_matches_only_covered_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = pointer(997_021);
        let selected = member(&parent);
        let returned = pointer(997_022);
        let held = MemoryRange::from_pointer_value(&selected, 0u32.into(), 1u32.into(), 4);
        let empty = PureFactContext::new();
        assert!(!empty.access_provenance_match(returned.access_provenance(), &held));
        let facts = equal(empty.clone(), &returned, &selected);
        assert!(facts.access_provenance_match(returned.access_provenance(), &held));
        let resources =
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(held.clone()));
        assert!(resources.permits_designated_memory_read(
            returned.pointer(),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    returned.pointer(),
                    Some(returned.access_provenance()),
                    4,
                    &facts
                )
                .is_some()
        );
        assert!(!ResourceContext::new().permits_designated_memory_read(
            returned.pointer(),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        assert!(!resources.permits_designated_memory_read(
            &returned.pointer().offset_by_bytes(4),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        let sibling = held.with_bounds(parent.pointer().clone(), 0u32.into(), 1u32.into());
        assert!(!facts.access_provenance_match(returned.access_provenance(), &sibling));
        let oversized = held.with_bounds(held.base().clone(), 0u32.into(), 2u32.into());
        assert!(!facts.access_provenance_match(returned.access_provenance(), &oversized));
        assert!(!empty.access_provenance_match(returned.access_provenance(), &held));
    }

    #[test]
    fn selected_domain_access_keeps_full_width_range_coordinates() {
        let _session = crate::kernel::VerificationSession::enter();
        let selected = member(&pointer(997_031));
        let returned = pointer(997_032);
        let facts = equal(PureFactContext::new(), &returned, &selected);
        let held = MemoryRange::from_pointer_value_wide(
            &selected,
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1),
            4,
        );
        assert!(facts.access_provenance_match(returned.access_provenance(), &held));
        let outside = MemoryRange::from_pointer_value_wide(
            &selected,
            MachineTerm::uint64_constant(1 << 32),
            MachineTerm::uint64_constant((1 << 32) + 1),
            4,
        );
        assert!(!facts.access_provenance_match(returned.access_provenance(), &outside));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/pointer_domains.rs");
}
