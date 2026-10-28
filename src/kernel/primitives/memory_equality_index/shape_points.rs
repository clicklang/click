//! Token/composite candidates attached to the graph's typed address classes.
use super::*;

type Shape = (ResourceFamily, String, usize);

pub(super) fn payload_is_empty(storage: &ResourceContextStorage) -> bool {
    storage.index.memory_by_block.is_empty() && storage.index.exact_shapes.is_empty()
}

fn shape_pointer(fact: &CResourceFact) -> Option<(Shape, &Pointer)> {
    let (CResource::Token { name, arguments } | CResource::Composite { name, arguments }) =
        fact.resource()
    else {
        return None;
    };
    let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = arguments.first() else {
        return None;
    };
    Some((
        (fact.family(), name.clone(), arguments.len()),
        pointer.pointer(),
    ))
}

#[derive(Clone, Default)]
struct Bucket {
    weight: usize,
    shapes: PersistentMap<Shape, ResourceEntryIds>,
}

#[derive(Clone, Default)]
pub(super) struct ShapePoints {
    classes: PersistentMap<u64, Bucket>,
    entries: PersistentMap<ResourceEntryId, u64>,
}

impl ShapePoints {
    pub(super) fn register(fact: &CResourceFact, graph: &EqualityGraph) {
        if let Some((_, pointer)) = shape_pointer(fact) {
            graph.address_class(pointer);
        }
    }

    pub(super) fn merge(&mut self, moved: u64, kept: u64) {
        let Some(mut smaller) = self.classes.get(&moved).cloned() else {
            return;
        };
        self.classes.remove(&moved);
        let mut larger = self.classes.get(&kept).cloned().unwrap_or_default();
        if larger.weight < smaller.weight {
            std::mem::swap(&mut larger, &mut smaller);
        }
        for (shape, entries) in smaller.shapes.iter() {
            let mut combined = larger.shapes.get(shape).cloned().unwrap_or_default();
            for entry in entries.iter() {
                crate::instrumentation::record_deterministic_work(1);
                combined = combined.with_value(*entry);
            }
            larger.shapes.insert(shape.clone(), combined);
        }
        larger.weight += smaller.weight;
        self.classes.insert(kept, larger);
    }

    pub(super) fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        fact: &CResourceFact,
        graph: &EqualityGraph,
    ) {
        let Some((shape, pointer)) = shape_pointer(fact) else {
            return;
        };
        let class = if insert {
            let Some(class) = graph.address_class(pointer) else {
                return;
            };
            self.entries.insert(entry, class);
            class
        } else {
            let Some(class) = self.entries.get(&entry).copied() else {
                return;
            };
            self.entries.remove(&entry);
            graph.address_class_root(class)
        };
        let mut bucket = self.classes.get(&class).cloned().unwrap_or_default();
        let entries = bucket.shapes.get(&shape).cloned().unwrap_or_default();
        let entries = if insert {
            bucket.weight += 1;
            entries.with_value(entry)
        } else {
            bucket.weight -= 1;
            entries.without_value(&entry)
        };
        if entries.is_empty() {
            bucket.shapes.remove(&shape);
        } else {
            bucket.shapes.insert(shape, entries);
        }
        if bucket.weight == 0 {
            self.classes.remove(&class);
        } else {
            self.classes.insert(class, bucket);
        }
    }
}

impl ResourceContext {
    /// Published inputs use class payloads; a raw, unpublished composition
    /// retains its structural index and is never registered by a lookup.
    pub(in crate::kernel::primitives) fn class_shape_candidates(
        &self,
        fact: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceEntryIds> {
        let (shape, pointer) = shape_pointer(fact)?;
        let prepared = self
            .memory_equalities
            .lock()
            .expect("memory equality index")
            .by_inputs
            .get(&assumptions.equality_graph.input_key().root())
            .is_some_and(|index| index.points_initialized);
        if !prepared {
            return None;
        }
        let index = self.pair_memory_equalities_in_graph(
            assumptions.equality_graph.clone(),
            false,
            Some(MemoryQuery::Address(pointer)),
        );
        if !index.points_initialized {
            return None;
        }
        let class = index.graph.address_class(pointer)?;
        Some(
            index
                .shapes
                .classes
                .get(&class)
                .and_then(|bucket| bucket.shapes.get(&shape))
                .cloned()
                .unwrap_or_default(),
        )
    }
}
