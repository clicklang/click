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
    pub(in crate::kernel) fn intrinsic(value: &OldPointer) -> Self {
        match value.bounds() {
            Some(bounds) => Self::Selected(bounds.clone()),
            None if value.bounds_are_known() => Self::Root,
            None => Self::Unknown,
        }
    }
}

/// Access descriptors already retain an opaque origin; other consumers have
/// the full value. Neither entry point reconstructs a synthetic pointer.
#[derive(Clone, Copy)]
pub(in crate::kernel) enum PointerDomainSource<'a> {
    Retained {
        bounds: Option<&'a SubobjectBounds>,
        known: bool,
        opaque: Option<&'a Address>,
    },
    BoundsOwner(&'a Address),
}

impl<'a> From<&'a OldPointer> for PointerDomainSource<'a> {
    fn from(value: &'a OldPointer) -> Self {
        Self::Retained {
            bounds: value.bounds(),
            known: value.bounds_are_known(),
            opaque: value.bounds_owner(),
        }
    }
}

impl<'a> From<&'a LValue> for PointerDomainSource<'a> {
    fn from(value: &'a LValue) -> Self {
        Self::Retained {
            bounds: value.bounds(),
            known: value.bounds_known(),
            opaque: value.bounds_owner().map(|owner| &**owner),
        }
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
            PointerDomainSource::Retained {
                bounds: Some(bounds),
                ..
            } => return PointerDomain::Selected(bounds.clone()),
            PointerDomainSource::Retained { known: true, .. } => return PointerDomain::Root,
            PointerDomainSource::Retained {
                opaque: Some(origin),
                ..
            } => origin,
            PointerDomainSource::Retained { opaque: None, .. } => return PointerDomain::Unknown,
            PointerDomainSource::BoundsOwner(origin) => origin,
        };
        self.equality_graph.opaque_pointer_domain(origin)
    }

    /// Match the held resource's carrier, or check a particular access against
    /// an admitted domain for the required pointer. Supplier coverage and
    /// ownership are checked separately. Callers also accept a holding of the
    /// same provenance when coverage evidence for the required pointer's own
    /// opaque domain contains the access: whether the bytes are held and
    /// whether this pointer may reach them are separate questions.
    fn access_provenance_matches_span(
        &self,
        required: (&Address, Option<&Address>),
        available: &MemoryRange,
        fits: impl FnOnce(&SubobjectBounds) -> bool,
    ) -> bool {
        if pointer_checks::access_match(
            required,
            (
                &available.provenance,
                available.carrier_owner().map(|owner| &**owner),
                available.carrier_known(),
            ),
            self,
        ) {
            return true;
        }
        let Some(owner) = required.1 else {
            return false;
        };
        match self.pointer_domain(PointerDomainSource::BoundsOwner(owner)) {
            PointerDomain::Unknown => false,
            PointerDomain::Root => self.provenance_equal(required.0, &available.provenance),
            PointerDomain::Selected(bounds) => {
                self.provenance_equal(required.0, &available.provenance) && fits(&bounds)
            }
        }
    }

    /// A narrow pointer may use a broader holding of the same object. Check
    /// the bytes being accessed, not the width or carrier of the holding.
    pub(in crate::kernel) fn access_provenance_matches_bytes(
        &self,
        required: (&Address, Option<&Address>),
        pointer: &Address,
        bytes: u32,
        available: &MemoryRange,
    ) -> bool {
        self.access_provenance_matches_span(required, available, |bounds| {
            self.pointer_access_in_range(
                pointer,
                bytes,
                &bounds.start,
                &0u32.into(),
                &bounds.width,
                1,
            )
        }) || required.1.is_some_and(|owner| {
            // An opaque domain known only by coverage: evidence that the
            // reader's own domain contains these bytes bounds the access,
            // and the holding of the same provenance supplies them.
            self.provenance_equal(required.0, &available.provenance)
                && self.opaque_domain_covers(owner, pointer, pointer, bytes)
        })
    }

    /// Match a clause's complete requested range to a supplier.
    pub(in crate::kernel) fn access_provenance_matches_range(
        &self,
        required: (&Address, Option<&Address>),
        range: &MemoryRange,
        available: &MemoryRange,
    ) -> bool {
        self.access_provenance_matches_span(required, available, |bounds| {
            let (start, end, wide) = match range.wide_bounds() {
                Some((start, end)) => (start, end, true),
                None => (range.start(), range.end(), false),
            };
            // Exact typed offsets retain full-width coordinates. Check both ends
            // as positions (one-past allowed), without narrowing a uint64 range
            // or searching for another footprint with a convenient bounds.
            [start, end].into_iter().all(|bound| {
                let endpoint = range.base().offset_by_typed_elements(
                    bound.clone(),
                    range.element_width(),
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
        }) || required.1.is_some_and(|owner| {
            // As for one access: coverage evidence for the clause pointer's
            // own domain contains both ends of the range.
            let (start, end, wide) = match range.wide_bounds() {
                Some((start, end)) => (start, end, true),
                None => (range.start(), range.end(), false),
            };
            self.provenance_equal(required.0, &available.provenance)
                && [start, end].into_iter().all(|bound| {
                    let endpoint = range.base().offset_by_typed_elements(
                        bound.clone(),
                        range.element_width(),
                        wide,
                        wide,
                    );
                    self.opaque_domain_covers(owner, range.base(), &endpoint, 0)
                })
        })
    }

    #[cfg(test)]
    pub(in crate::kernel) fn access_provenance_match(
        &self,
        required: (&Address, Option<&Address>),
        range: &MemoryRange,
    ) -> bool {
        self.access_provenance_matches_range(required, range, range)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pointer(id: u64) -> OldPointer {
        OldPointer::new(Address::symbolic(Variable(id)), ProgramType::Int32Pointer)
    }
    fn equal(facts: PureFactContext, a: &OldPointer, b: &OldPointer) -> PureFactContext {
        facts.assume_condition(OldConditionTerm::pointer_equal(a.clone(), b.clone()), true)
    }
    fn member(parent: &OldPointer) -> OldPointer {
        parent
            .clone()
            .with_address(parent.address().offset_by_bytes(4))
            .with_bounds(Some(SubobjectBounds {
                start: parent.address().offset_by_bytes(4),
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
        assert_eq!(
            empty.pointer_domain(PointerDomainSource::Retained {
                bounds: None,
                known: true,
                opaque: returned.bounds_owner(),
            }),
            PointerDomain::Root
        );
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
            OldConditionTerm::address_equal(returned.address().clone(), selected.address().clone()),
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
            SymbolicMemory::new().store(cell.clone(), ProgramValue::Pointer(selected.clone())),
        );
        let read = OldPointer::from_read(
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
            returned.address(),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    returned.address(),
                    Some(returned.access_provenance()),
                    4,
                    &facts
                )
                .is_some()
        );
        assert!(!ResourceContext::new().permits_designated_memory_read(
            returned.address(),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        assert!(!resources.permits_designated_memory_read(
            &returned.address().offset_by_bytes(4),
            Some(returned.access_provenance()),
            4,
            &facts
        ));
        let sibling = held.with_bounds(parent.address().clone(), 0u32.into(), 1u32.into());
        assert!(!facts.access_provenance_match(returned.access_provenance(), &sibling));
        let oversized = held.with_bounds(held.base().clone(), 0u32.into(), 2u32.into());
        assert!(!facts.access_provenance_match(returned.access_provenance(), &oversized));
        assert!(!empty.access_provenance_match(returned.access_provenance(), &held));

        // Coalescing adjacent holdings can leave one supplier whose carrier
        // names the parent, with no selected bounds of its own.
        let parent_range = MemoryRange::from_pointer_value(&parent, 0u32.into(), 2u32.into(), 4);
        let resources = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(parent_range.clone()));
        let required = returned.access_provenance();
        assert!(resources.permits_designated_memory_read(
            returned.address(),
            Some(required),
            4,
            &facts
        ));
        assert!(!resources.permits_designated_memory_read(
            parent.address(),
            Some(required),
            4,
            &facts,
        ));
        assert!(facts.access_provenance_matches_range(required, &held, &parent_range));
        assert!(!facts.access_provenance_matches_range(required, &parent_range, &parent_range));
    }

    #[test]
    fn selected_domain_access_keeps_full_width_range_coordinates() {
        let _session = crate::kernel::VerificationSession::enter();
        let selected = member(&pointer(997_031));
        let returned = pointer(997_032);
        let facts = equal(PureFactContext::new(), &returned, &selected);
        let held = MemoryRange::from_pointer_value_wide(
            &selected,
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(1),
            4,
        );
        assert!(facts.access_provenance_match(returned.access_provenance(), &held));
        let outside = MemoryRange::from_pointer_value_wide(
            &selected,
            OldMachineTerm::uint64_constant(1 << 32),
            OldMachineTerm::uint64_constant((1 << 32) + 1),
            4,
        );
        assert!(!facts.access_provenance_match(returned.access_provenance(), &outside));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/pointer_domains.rs");
}
