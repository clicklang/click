//! Bounded separation of a symbolic range from a retained owner partition.
//! No owner bucket or pointer-alias class is enumerated at a query.
use super::*;

impl ResourceContext {
    pub(in crate::kernel::primitives) fn owned_boundary_overlap(
        &self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> ConstantOwnedOverlap {
        use ConstantOwnedOverlap::*;
        if let Some(range) = fact.memory_own_range() {
            if matches!(range.base().base, AddressBase::StringLiteral { .. })
                && let Resource::Memory(held) = self.storage.index.boundary_memory.footprint()
                && super::super::resource_algebra::string_literal_blocks_may_alias(
                    &range.base().base,
                    &held.base().base,
                )
            {
                // Distinct equal-content literals are shared read-only storage,
                // rather than competing mutable owners. Select a singleton
                // frame by its cached footprint; do not enumerate literals.
                return Clear;
            }
            // A single written memory-memory premise already has an exact
            // fact key. Do not build a second canonical certificate for it.
            if self.storage.index.boundary_memory.len() == 1
                && !assumptions.memory_separation_facts.is_empty()
            {
                let frame = self.storage.index.boundary_memory.footprint();
                for (left, right) in [
                    (Resource::Memory(range.clone()), frame.clone()),
                    (frame, Resource::Memory(range.clone())),
                ] {
                    if assumptions.contains_assumed_exact(&Proposition::ResourceSeparate {
                        left: Box::new(left),
                        right: Box::new(right),
                    }) {
                        return Clear;
                    }
                }
            }
            if let Some((_, source)) = assumptions
                .explicit_memory_boundaries
                .get(&(range.clone(), self.storage.index.boundary_memory.identity()))
            {
                crate::kernel::assumptions::record_implicit_consulted_premises(assumptions, source);
                return Clear;
            }
        }
        if fact.owned_quantity_term().and_then(MachineTerm::as_const) == Some(0) {
            return Clear;
        }
        // A compiler-private scalar slot has no address any pointer value
        // can denote. The producer count certifies the entire partition;
        // no local-name or owner bucket is visited here.
        if self.storage.index.boundary_private_entries.len()
            == self.storage.index.boundary_memory_count
            && self
                .storage
                .index
                .boundary_private_registry
                .as_ref()
                .is_some_and(|registry| {
                    std::sync::Arc::ptr_eq(
                        registry,
                        &super::super::never_address_taken_locals_key(),
                    )
                })
            && assumptions
                .equality_graph
                .admitted
                .local_pointer_aliases
                .is_empty()
            && fact.memory_own_range().is_some_and(|range| {
                matches!(
                    range.base().base,
                    AddressBase::Symbolic(_)
                        | AddressBase::Load(_)
                        | AddressBase::FunctionSymbolic(_)
                        | AddressBase::ExternalArgument
                        | AddressBase::ExternalObject(_)
                )
            })
        {
            return Clear;
        }
        if self.storage.index.boundary_non_nominal_count == 0
            && fact.memory_own_range().is_some_and(|range| {
                super::super::resource_algebra::nominal_ownership_block(&range.base().base)
                    && !self
                        .storage
                        .index
                        .owned_memory_by_block
                        .contains_key(&range.base().base)
            })
        {
            return Clear;
        }
        if let Some(range) = fact.memory_own_range() {
            let block = &range.base().base;
            // Allocation classes and counts are maintained at publication.
            // External argument objects predate the callee's automatic locals.
            if self.storage.index.boundary_may_alias_argument_count == 0
                && matches!(
                    block,
                    AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
                )
                || self.storage.index.boundary_non_argument_or_nominal_count == 0
                    && block.is_local_block()
                    && !self.storage.index.owned_memory_by_block.contains_key(block)
            {
                return Clear;
            }
            // A singleton is selected by cardinality, never by searching for
            // a candidate among the frame's owners.
            if self.storage.index.owned_memory_ranges.len() == 1
                && let Some((held, _)) = self.storage.index.owned_memory_ranges.iter().next()
                && range.base().blocks_proven_distinct(held.base())
            {
                return Clear;
            }
        }
        match self.constant_owned_overlap(fact, assumptions) {
            Unsupported => {}
            result => return result,
        }
        let Some(range) = fact.memory_own_range() else {
            return Clear;
        };
        if self.flat_owned_memory_ranges().is_empty() {
            return Clear;
        }
        if self.storage.index.boundary_memory_count == 1
            && let Resource::Memory(held) = self.storage.index.boundary_memory.footprint()
            && let Some(entry) = self
                .storage
                .index
                .owned_memory_by_block
                .get(&held.base().base)
                .and_then(|entries| entries.iter().next())
                .copied()
        {
            // Cardinality nominates one live owner. Exact address-class
            // equality and direct endpoint bounds need no ambient pairing.
            let graph = graph_for_memory_query(assumptions, range.base());
            match checked_pair(
                self.storage.facts.get(&entry).expect("singleton owner"),
                fact,
                assumptions,
                &graph,
            ) {
                Some(true) => return Clear,
                Some(false) => return Overlap(entry),
                None => {}
            }
        }
        // Only a producer-published lineage is eligible. A query must never
        // initialize an ambient resource/fact snapshot to obtain coverage.
        {
            let cache = self
                .memory_equalities
                .lock()
                .expect("memory equality index");
            let Some(published) = &cache.published else {
                return Unsupported;
            };
            let current = std::sync::Arc::ptr_eq(&published.resources, &self.storage);
            let one_delta =
                std::sync::Arc::ptr_eq(&published.resources.origin, &self.storage.origin)
                    && Self::history_tail_is(
                        self.storage
                            .history
                            .as_ref()
                            .and_then(|change| change.parent.as_ref()),
                        published.resources.history.as_ref(),
                    );
            if !published.points_initialized
                || !(current || one_delta)
                || published.graph.input_key().root()
                    != assumptions.equality_graph.input_key().root()
            {
                return Unsupported;
            }
        }
        let source = graph_for_memory_query(assumptions, range.base());
        let source_key = source.input_key();
        let index = self.pair_memory_equalities_in_graph(
            source,
            true,
            Some(MemoryQuery::Address(range.base())),
        );
        if !index.points_initialized
            || !std::sync::Arc::ptr_eq(&index.resources, &self.storage)
            || index.graph.input_key() != source_key
        {
            return Unsupported;
        }
        if let Some(class) = index.graph.address_class(range.base())
            && let Some(entry) = index.symbolic.boundary_overlap(class, range)
            && checked_pair(
                self.storage.facts.get(&entry).expect("selected owner"),
                fact,
                assumptions,
                &index.graph,
            ) == Some(false)
        {
            return Overlap(entry);
        }
        if let Some(class) = index.graph.address_class(range.base())
            && let Some((intervals, unknown)) = index
                .symbolic
                .boundary_parts(class, self.storage.index.boundary_memory_count)
        {
            return self.check_owned_boundary_partition(
                fact,
                assumptions,
                &index.graph,
                &intervals,
                unknown,
                AffineOffset::constant(0),
            );
        }
        if index.addresses.incomplete {
            return Unsupported;
        }
        let Some(base) = index.graph.canonical_pointer(range.base()) else {
            return Unsupported;
        };
        if !index.graph.affine_addresses_complete(&base.representative) {
            return Unsupported;
        }
        let Some(bucket) = index.addresses.classes.get(&base.representative) else {
            return Clear;
        };
        // This count is the coverage evidence: every retained owner is either
        // in the constant interval tree or in the explicitly maintained set.
        if bucket.boundary_entries.len() + bucket.boundary_unknown.len() != bucket.owners.len()
            || bucket.boundary_unknown.len() > 1
        {
            return Unsupported;
        }
        self.check_owned_boundary_partition(
            fact,
            assumptions,
            &index.graph,
            &bucket.boundary_intervals,
            bucket.boundary_unknown.iter().next().copied(),
            match base
                .offset
                .checked_add(&bucket.origin)
                .and_then(|offset| offset.checked_add(&bucket.boundary_origin))
            {
                Some(offset) => offset,
                None => return Unsupported,
            },
        )
    }

    fn check_owned_boundary_partition(
        &self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        graph: &EqualityGraph,
        intervals: &ReadIntervals,
        unknown: Option<ResourceEntryId>,
        coordinate: AffineOffset,
    ) -> ConstantOwnedOverlap {
        use ConstantOwnedOverlap::*;
        let range = fact.memory_own_range().expect("owned query");
        if let Some(entry) = unknown {
            match checked_pair(
                self.storage.facts.get(&entry).expect("selected owner"),
                fact,
                assumptions,
                graph,
            ) {
                Some(true) => {}
                Some(false) => return Overlap(entry),
                None => return Unsupported,
            }
        }
        if intervals.len() == 0 {
            return Clear;
        }
        if let (Some((first, last)), Some((start, end))) =
            (intervals.bounding_span(), range.int32_bounds())
        {
            let bound = |term: &MachineTerm| {
                term.as_const()
                    .map(|n| (i64::from(n as i32), i64::from(n as i32)))
                    .or_else(|| assumptions.indexed_constant_interval(term))
            };
            let at = |value: i64| {
                coordinate.checked_add(&AffineOffset::constant(
                    i128::from(value) * i128::from(range.element_width()),
                ))
            };
            if bound(start)
                .and_then(|(lo, _)| at(lo))
                .and_then(|start| start.constant_difference(&last.0))
                .is_some_and(|difference| difference >= 0)
                || bound(end)
                    .and_then(|(_, hi)| at(hi))
                    .and_then(|end| first.0.constant_difference(&end))
                    .is_some_and(|difference| difference >= 0)
            {
                return Clear;
            }
        }
        let Some((lo, hi)) = enclosing_bounds(range, assumptions) else {
            return Unsupported;
        };
        let (Some(start), Some(end)) = (
            coordinate.checked_add(&AffineOffset::constant(lo)),
            coordinate.checked_add(&AffineOffset::constant(hi)),
        ) else {
            return Unsupported;
        };
        if !start.is_constant() || !end.is_constant() {
            return Unsupported;
        }
        match intervals.first_overlap(&AddressCoordinate(start), &AddressCoordinate(end)) {
            None => Clear,
            Some(entry) => match checked_pair(
                self.storage.facts.get(&entry).expect("selected owner"),
                fact,
                assumptions,
                graph,
            ) {
                Some(false) => Overlap(entry),
                // An overlapping envelope never proves an actual overlap,
                // and clearing one candidate does not cover the other rows.
                Some(true) | None => Unsupported,
            },
        }
    }
}

fn enclosing_bounds(range: &MemoryRange, facts: &PureFactContext) -> Option<(i128, i128)> {
    let (start, end) = range.int32_bounds()?;
    let lower = start
        .as_const()
        .map(|value| i64::from(value as i32))
        .or_else(|| facts.indexed_constant_interval(start).map(|(lo, _)| lo))?;
    let upper = end
        .as_const()
        .map(|value| i64::from(value as i32))
        .or_else(|| facts.indexed_constant_interval(end).map(|(_, hi)| hi))?;
    (lower <= upper).then_some((
        i128::from(lower) * i128::from(range.element_width()),
        i128::from(upper) * i128::from(range.element_width()),
    ))
}

// Some(true): selected pair is separate. Some(false): positive overlap.
// None: the written bounds or explicit separation premise are missing.
fn checked_pair(
    left: &ResourceFact,
    right: &ResourceFact,
    facts: &PureFactContext,
    graph: &EqualityGraph,
) -> Option<bool> {
    let (a, b) = (left.memory_own_range()?, right.memory_own_range()?);
    for (a, b) in [(a, b), (b, a)] {
        if facts.contains_assumed_exact(&Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(a.clone())),
            right: Box::new(Resource::Memory(b.clone())),
        }) {
            return Some(true);
        }
    }
    if a.element_width() != b.element_width() {
        return None;
    }
    if a.base() != b.base()
        && facts.decide(&ConditionTerm::address_equal(
            a.base().clone(),
            b.base().clone(),
        )) != Some(true)
    {
        let a = graph.address_class(a.base())?;
        let b = graph.address_class(b.base())?;
        if graph.address_class_root(a) != graph.address_class_root(b) {
            return None;
        }
    }
    let ((as_, ae), (bs, be)) = (a.int32_bounds()?, b.int32_bounds()?);
    let le = |a: &MachineTerm, b: &MachineTerm| direct_endpoint_separation(a, b, facts);
    if le(ae, as_) || le(be, bs) || le(ae, bs) || le(be, as_) {
        return Some(true);
    }
    if !left.owned_quantity_term().is_some_and(|quantity| {
        super::super::resource_algebra::resource_quantity_is_positive(quantity, facts)
    }) || !right.owned_quantity_term().is_some_and(|quantity| {
        super::super::resource_algebra::resource_quantity_is_positive(quantity, facts)
    }) {
        return None;
    }
    let lt = |a: &MachineTerm, b: &MachineTerm| {
        if facts.exact_condition_value(&ConditionTerm::signed_less_than(a.clone(), b.clone()))
            == Some(true)
        {
            return true;
        }
        let bound = |term: &MachineTerm| {
            term.as_const()
                .map(|value| (i64::from(value as i32), i64::from(value as i32)))
                .or_else(|| facts.indexed_constant_interval(term))
        };
        matches!((bound(a), bound(b)), (Some((_, upper)), Some((lower, _))) if upper < lower)
    };
    (lt(as_, ae) && lt(bs, be) && lt(as_, be) && lt(bs, ae)).then_some(false)
}

impl PureFactContext {
    pub(in crate::kernel) fn index_explicit_memory_boundary(&mut self, proposition: &Proposition) {
        let Proposition::ResourceSeparate { left, right } = proposition else {
            return;
        };
        for (query, frame) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            let Resource::Memory(range) = query else {
                continue;
            };
            if !matches!(frame, Resource::Star(_)) {
                continue;
            }
            let mut partition = super::super::canonical_fact_set::CanonicalFactSet::default();
            let mut pending = vec![frame];
            let mut seen = std::collections::BTreeSet::new();
            let mut complete = true;
            while let Some(resource) = pending.pop() {
                crate::instrumentation::record_deterministic_work(1);
                match resource {
                    Resource::Emp => {}
                    Resource::Memory(range) => {
                        if seen.insert(range.clone()) {
                            partition = partition.with_memory_range(range);
                        }
                    }
                    Resource::Star(pair) => {
                        pending.push(&pair.1);
                        pending.push(&pair.0);
                    }
                    _ => {
                        complete = false;
                        break;
                    }
                }
            }
            if complete {
                self.explicit_memory_boundaries = self.explicit_memory_boundaries.with_inserted(
                    (range.clone(), partition.identity()),
                    (partition, std::sync::Arc::new(proposition.clone())),
                );
            }
        }
    }
}
