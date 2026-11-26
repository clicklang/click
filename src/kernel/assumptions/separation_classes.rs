use super::*;
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::Mutex;

type Pair = (u64, u64);

#[cfg(test)]
thread_local! { static SOURCE_VISITS: Cell<usize> = const { Cell::new(0) }; }

fn source_visit() {
    #[cfg(test)]
    SOURCE_VISITS.with(|visits| visits.set(visits.get() + 1));
}

/// Disposable, persistent index over exact stated separation authority. Each
/// context fork owns its cache lock; graph hypotheses never cross branches.
#[derive(Default)]
pub(in crate::kernel) struct SeparatedAddressIndex(Mutex<Option<Box<Index>>>);

#[derive(Clone, Debug, Default)]
struct Index {
    graph: Option<EqualityGraph>,
    sources: PersistentMap<Proposition, (Address, Address)>,
    pairs: PersistentMap<Pair, PersistentSet<Proposition>>,
    exact_spans: PersistentMap<Pair, PersistentMap<(SpanWidth, SpanWidth), Proposition>>,
    incident: PersistentMap<u64, PersistentSet<Pair>>,
}

impl Clone for SeparatedAddressIndex {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.0.lock().expect("separation index").clone()))
    }
}

impl std::fmt::Debug for SeparatedAddressIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SeparatedAddressIndex")
            .finish_non_exhaustive()
    }
}

fn pair(left: u64, right: u64) -> Pair {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

// A fixed nonempty byte interval is identified by its start address and
// span, independently of the pointer spelling or element type.
/// The size of a fixed nonempty interval: a byte count, or all the bytes of
/// one object whose size is a term, `sizeof(L)` or `sizeof(T)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum SpanWidth {
    Bytes(u32),
    Layout(SymbolicLayoutName),
    Parameter(TypeParameterName),
}

fn fixed_span_bytes(range: &MemoryRange) -> Option<SpanWidth> {
    if let Some(layout) = range.symbolic_object() {
        return Some(SpanWidth::Layout(layout));
    }
    if let Some((start, end)) = range.wide_bounds() {
        return (range.element_width() == 1 && start.uint64_as_const() == Some(0))
            .then(|| TypeParameterName::of_size_term(end))
            .flatten()
            .map(SpanWidth::Parameter);
    }
    let elements = range
        .signed_constant_end()?
        .checked_sub(range.signed_constant_start()?)?;
    let bytes = u32::try_from(elements)
        .ok()?
        .checked_mul(range.element_width())?;
    (bytes != 0).then_some(SpanWidth::Bytes(bytes))
}

fn span_key(
    left: u64,
    right: u64,
    left_bytes: SpanWidth,
    right_bytes: SpanWidth,
) -> (Pair, (SpanWidth, SpanWidth)) {
    if (left, left_bytes) <= (right, right_bytes) {
        ((left, right), (left_bytes, right_bytes))
    } else {
        ((right, left), (right_bytes, left_bytes))
    }
}

impl Index {
    fn attach(&mut self, key: Pair, fact: Proposition) {
        source_visit();
        self.pairs = self.pairs.with_inserted(
            key,
            self.pairs
                .get(&key)
                .cloned()
                .unwrap_or_default()
                .with_value(fact),
        );
        for endpoint in [key.0, key.1] {
            self.incident = self.incident.with_inserted(
                endpoint,
                self.incident
                    .get(&endpoint)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(key),
            );
        }
    }

    fn attach_exact(&mut self, key: Pair, widths: (SpanWidth, SpanWidth), fact: Proposition) {
        crate::instrumentation::record_deterministic_work(1);
        let spans = self.exact_spans.get(&key).cloned().unwrap_or_default();
        // Equal address classes and spans denote the same physical spans;
        // retain one selected authority rather than a growing fact bucket.
        self.exact_spans = self
            .exact_spans
            .with_inserted(key, spans.with_inserted(widths, fact));
    }

    fn attach_exact_fact(&mut self, fact: &Proposition, left: u64, right: u64) {
        let Proposition::ResourceSeparate { left: a, right: b } = fact else {
            return;
        };
        let (Resource::Memory(a), Resource::Memory(b)) = (a.as_ref(), b.as_ref()) else {
            return;
        };
        if let (Some(a), Some(b)) = (fixed_span_bytes(a), fixed_span_bytes(b)) {
            let (key, widths) = span_key(left, right, a, b);
            self.attach_exact(key, widths, fact.clone());
        }
    }

    fn detach_pair(&mut self, key: Pair) {
        self.exact_spans = self.exact_spans.without_key(&key);
        self.pairs = self.pairs.without_key(&key);
        for endpoint in [key.0, key.1] {
            if let Some(incident) = self.incident.get(&endpoint) {
                let remaining = incident.without_value(&key);
                self.incident = if remaining.is_empty() {
                    self.incident.without_key(&endpoint)
                } else {
                    self.incident.with_inserted(endpoint, remaining)
                };
            }
        }
    }

    fn synchronize(&mut self, graph: &EqualityGraph) {
        let Some(previous) = &self.graph else {
            self.graph = Some(graph.clone());
            return;
        };
        if let Some(merges) = graph.address_merges_since(previous) {
            for merge in merges {
                crate::instrumentation::record_deterministic_work(1);
                let incident = self.incident.get(&merge.moved).cloned().unwrap_or_default();
                for old in incident.iter() {
                    let facts = self.pairs.get(old).cloned().unwrap_or_default();
                    let exact = self.exact_spans.get(old).cloned().unwrap_or_default();
                    self.detach_pair(*old);
                    let replace = |id| if id == merge.moved { merge.kept } else { id };
                    let new = pair(replace(old.0), replace(old.1));
                    for fact in facts.iter() {
                        crate::instrumentation::record_deterministic_work(1);
                        self.attach(new, fact.clone());
                    }
                    for (widths, fact) in exact.iter() {
                        let (key, widths) =
                            span_key(replace(old.0), replace(old.1), widths.0, widths.1);
                        self.attach_exact(key, widths, fact.clone());
                    }
                }
            }
        } else {
            // Restriction reconstructs the checked graph from its selected
            // exact support. Class IDs from that lineage cannot be reused.
            self.pairs = Default::default();
            self.exact_spans = Default::default();
            self.incident = Default::default();
            let sources = self.sources.clone();
            let registered = sources
                .iter()
                .filter_map(|(fact, (left, right))| {
                    crate::instrumentation::record_deterministic_work(1);
                    Some((
                        fact.clone(),
                        graph.address_class(left)?,
                        graph.address_class(right)?,
                    ))
                })
                .collect::<Vec<_>>();
            // Registration may join classes through producer definitions.
            // Attach only after every selected source has been registered.
            for (fact, left, right) in registered {
                let (left, right) = (
                    graph.address_class_root(left),
                    graph.address_class_root(right),
                );
                self.attach(pair(left, right), fact.clone());
                self.attach_exact_fact(&fact, left, right);
            }
        }
        self.graph = Some(graph.clone());
    }
}

impl SeparatedAddressIndex {
    pub(in crate::kernel) fn adjust(
        &self,
        fact: &Proposition,
        left: Address,
        right: Address,
        graph: &EqualityGraph,
    ) {
        let mut cache = self.0.lock().expect("separation index");
        let index = cache.get_or_insert_with(Box::default);
        let (Some(left_class), Some(right_class)) =
            (graph.address_class(&left), graph.address_class(&right))
        else {
            return;
        };
        index.synchronize(graph);
        let key = pair(
            graph.address_class_root(left_class),
            graph.address_class_root(right_class),
        );
        index.sources = index.sources.with_inserted(fact.clone(), (left, right));
        index.attach(key, fact.clone());
        index.attach_exact_fact(
            fact,
            graph.address_class_root(left_class),
            graph.address_class_root(right_class),
        );
    }

    /// One stated authority for exactly these two physical byte intervals.
    /// Widths select a map entry, never a bucket of related separation facts.
    pub(in crate::kernel) fn exact_spans(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
        graph: &EqualityGraph,
    ) -> Option<Proposition> {
        self.exact_spans_with_upkeep(left, right, graph, true)
    }

    pub(in crate::kernel) fn prepared_exact_spans(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
        graph: &EqualityGraph,
    ) -> Option<Proposition> {
        self.exact_spans_with_upkeep(left, right, graph, false)
    }

    fn exact_spans_with_upkeep(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
        graph: &EqualityGraph,
        synchronize: bool,
    ) -> Option<Proposition> {
        let (left_bytes, right_bytes) = (fixed_span_bytes(left)?, fixed_span_bytes(right)?);
        let mut cache = self.0.lock().expect("separation index");
        let index = cache.as_deref_mut()?;
        let (left, right) = (
            graph.address_class(&left.start_pointer())?,
            graph.address_class(&right.start_pointer())?,
        );
        if synchronize {
            index.synchronize(graph);
        }
        let current_key = |left, right, left_bytes, right_bytes| {
            span_key(
                graph.address_class_root(left),
                graph.address_class_root(right),
                left_bytes,
                right_bytes,
            )
        };
        let (key, widths) = current_key(left, right, left_bytes, right_bytes);
        // Registering the selected addresses can itself expose an equality.
        // Nonempty intervals starting at one address always overlap.
        if key.0 == key.1 {
            return None;
        }
        let fact = index.exact_spans.get(&key)?.get(&widths)?;
        source_visit();
        crate::instrumentation::record_deterministic_work(1);
        if !synchronize {
            // A prepared key can survive new equalities. Match the one
            // nominated premise in the live graph, without replaying the
            // merge journal or trying another source after a miss.
            let Proposition::ResourceSeparate { left: a, right: b } = fact else {
                return None;
            };
            let (Resource::Memory(a), Resource::Memory(b)) = (a.as_ref(), b.as_ref()) else {
                return None;
            };
            let (a_class, b_class) = (
                graph.address_class(&a.start_pointer())?,
                graph.address_class(&b.start_pointer())?,
            );
            let source = current_key(a_class, b_class, fixed_span_bytes(a)?, fixed_span_bytes(b)?);
            let target = current_key(left, right, left_bytes, right_bytes);
            if target.0.0 == target.0.1 || source != target {
                return None;
            }
        }
        Some(fact.clone())
    }

    pub(in crate::kernel) fn candidates(
        &self,
        left: &Address,
        right: &Address,
        graph: &EqualityGraph,
    ) -> Vec<Proposition> {
        let mut cache = self.0.lock().expect("separation index");
        let Some(index) = cache.as_deref_mut() else {
            return Vec::new();
        };
        if index.sources.is_empty() {
            return Vec::new();
        }
        let (Some(left), Some(right)) = (graph.address_class(left), graph.address_class(right))
        else {
            return Vec::new();
        };
        index.synchronize(graph);
        let key = pair(
            graph.address_class_root(left),
            graph.address_class_root(right),
        );
        index
            .pairs
            .get(&key)
            .into_iter()
            .flat_map(|facts| {
                facts.iter().map(|fact| {
                    source_visit();
                    fact.clone()
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/separation_classes.rs");
}
