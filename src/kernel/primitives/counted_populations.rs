//! Persistent population storage. Order remains insertion order, including
//! duplicate keys produced by term substitution; exact updates select the
//! first such entry, as the former vector representation did.
use super::*;
use std::cmp::Ordering;

type Key = (String, ResourceArguments, bool);

#[derive(Clone, Default)]
struct Store {
    ordered: SnapshotMap<u64, CCountedPopulation>,
    exact: SnapshotMap<Key, SnapshotSet<u64>>,
    families: SnapshotMap<String, SnapshotSet<u64>>,
    unary_pointers: SnapshotMap<(String, Pointer), SnapshotSet<u64>>,
    unsupported_pointers: SnapshotMap<String, usize>,
    symbolic_pointers: SnapshotMap<String, usize>,
    /// Ordinary entries keyed on one pointer into a separable block
    /// ([`block_is_separable`]), by that block: the only entries a pattern
    /// naming the block may denote once every entry of the family is such a
    /// pointer.
    separable_blocks: SnapshotMap<(String, PointerBlock), SnapshotSet<u64>>,
    /// Per family, the ordinary entries that are not one pointer into a
    /// separable block. While it is zero the family's entries are pairwise
    /// distinct objects whenever their blocks differ.
    inseparable: SnapshotMap<String, usize>,
    next: u64,
    content_hash: u64,
}

/// One pointer in CState, so adding indices does not enlarge executor frames.
#[derive(Clone, Default)]
pub(crate) struct CountedPopulations(Option<Arc<Store>>);

fn key(population: &CCountedPopulation) -> Key {
    (
        population.name.clone(),
        population.arguments.clone(),
        population.family_observation_marker,
    )
}

fn population_hash(population: &CCountedPopulation) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    population.hash(&mut hasher);
    hasher.finish()
}

// Index classification must depend only on the stored term. In particular,
// load IDs stay unsupported even before their registry entry is installed or
// after an epoch clears it: later load congruence could reveal aliases that
// this syntactic pointer index does not enumerate.
fn normalized_pointer(pointer: &Pointer) -> Option<Pointer> {
    let mut pending = vec![&pointer.offset];
    let mut constant = 0i64;
    let mut root = None;
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Constant(value) => constant = constant.checked_add(*value)?,
            PointerOffsetTerm::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            PointerOffsetTerm::Variable(variable) if !crate::kernel::is_load_variable(variable) => {
                if root.replace(offset.clone()).is_some() {
                    return None;
                }
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width > 0 => {
                match value.as_ref() {
                    Bitvector32Term::Variable(variable)
                        if !crate::kernel::is_load_variable(variable) =>
                    {
                        if root.replace(offset.clone()).is_some() {
                            return None;
                        }
                    }
                    Bitvector32Term::Constant(value) => {
                        constant = constant
                            .checked_add(i64::from(*value as i32).checked_mul(*byte_width)?)?;
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    Some(Pointer {
        block: pointer.block.clone(),
        offset: match root {
            Some(root) => PointerOffsetTerm::add(root, PointerOffsetTerm::Constant(constant)),
            None => PointerOffsetTerm::Constant(constant),
        },
    })
}

fn unary_pointer(arguments: &[AlgebraicValue]) -> Option<Pointer> {
    let [AlgebraicValue::C(CValue::Pointer(pointer))] = arguments else {
        return None;
    };
    normalized_pointer(pointer.pointer())
}

/// Blocks whose distinct identities are distinct objects by structure alone
/// (`PointerBlock::proven_distinct`): a fresh heap or temporary object, or a
/// named concrete object. A pointer into any other kind of block, a parameter
/// or a loaded pointer above all, may alias a pointer into any of these.
fn block_is_separable(block: &PointerBlock) -> bool {
    matches!(
        block,
        PointerBlock::Heap(_) | PointerBlock::Temporary(_) | PointerBlock::Concrete(_)
    )
}

/// The block of an ordinary entry's one pointer argument when that block is
/// separable, which is when the entry joins `separable_blocks` rather than
/// the family's `inseparable` count.
fn separable_block(arguments: &[AlgebraicValue]) -> Option<&PointerBlock> {
    let [AlgebraicValue::C(CValue::Pointer(pointer))] = arguments else {
        return None;
    };
    let block = &pointer.pointer().block;
    block_is_separable(block).then_some(block)
}

impl CountedPopulations {
    pub(crate) fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |store| store.ordered.len())
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => self.is_empty() && other.is_empty(),
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &CCountedPopulation> {
        self.0
            .iter()
            .flat_map(|store| store.ordered.values())
            .inspect(|_| {
                #[cfg(test)]
                crate::instrumentation::record_deterministic_work(1);
            })
    }

    pub(crate) fn family<'a>(
        &'a self,
        name: &'a str,
    ) -> impl Iterator<Item = &'a CCountedPopulation> {
        self.0.iter().flat_map(move |store| {
            store.families.get(name).into_iter().flat_map(move |ids| {
                ids.iter()
                    .map(move |id| store.ordered.get(id).expect("indexed population"))
            })
        })
    }

    pub(crate) fn get(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
        marker: bool,
    ) -> Option<&CCountedPopulation> {
        crate::instrumentation::record_deterministic_work(1);
        let store = self.0.as_ref()?;
        let key = (name.to_owned(), arguments.into(), marker);
        let id = store.exact.get(&key)?.iter().next()?;
        store.ordered.get(id)
    }

    pub(crate) fn insert(&mut self, population: CCountedPopulation) {
        let identity = key(&population);
        let existing = self
            .0
            .as_ref()
            .and_then(|store| store.exact.get(&identity))
            .and_then(|ids| ids.iter().next())
            .copied();
        if let Some(id) = existing {
            let old = self.0.as_ref().unwrap().ordered.get(&id).unwrap();
            if old == &population {
                return;
            }
            let old_hash = population_hash(old);
            let store = Arc::make_mut(self.0.as_mut().unwrap());
            store.content_hash = store
                .content_hash
                .wrapping_sub(old_hash)
                .wrapping_add(population_hash(&population));
            store.ordered.insert(id, population);
        } else {
            self.append(population);
        }
    }

    fn append(&mut self, population: CCountedPopulation) {
        crate::instrumentation::record_deterministic_work(1);
        let store = Arc::make_mut(self.0.get_or_insert_with(|| Arc::new(Store::default())));
        let id = store.next;
        store.next = id.checked_add(1).expect("population order exhausted");
        let mut exact = store
            .exact
            .get(&key(&population))
            .cloned()
            .unwrap_or_default();
        exact.insert(id);
        store.exact.insert(key(&population), exact);
        let mut family = store
            .families
            .get(&population.name)
            .cloned()
            .unwrap_or_default();
        family.insert(id);
        store.families.insert(population.name.clone(), family);
        if !population.family_observation_marker {
            if let Some(pointer) = unary_pointer(&population.arguments) {
                if offset_root_atom(&pointer.offset).is_some() {
                    let count = store
                        .symbolic_pointers
                        .get(&population.name)
                        .copied()
                        .unwrap_or(0);
                    store
                        .symbolic_pointers
                        .insert(population.name.clone(), count + 1);
                }
                let pointer_key = (population.name.clone(), pointer);
                let mut ids = store
                    .unary_pointers
                    .get(&pointer_key)
                    .cloned()
                    .unwrap_or_default();
                ids.insert(id);
                store.unary_pointers.insert(pointer_key, ids);
            } else {
                let count = store
                    .unsupported_pointers
                    .get(&population.name)
                    .copied()
                    .unwrap_or(0);
                store
                    .unsupported_pointers
                    .insert(population.name.clone(), count + 1);
            }
            match separable_block(&population.arguments) {
                Some(block) => {
                    let block_key = (population.name.clone(), block.clone());
                    let mut ids = store
                        .separable_blocks
                        .get(&block_key)
                        .cloned()
                        .unwrap_or_default();
                    ids.insert(id);
                    store.separable_blocks.insert(block_key, ids);
                }
                None => {
                    let count = store
                        .inseparable
                        .get(&population.name)
                        .copied()
                        .unwrap_or(0);
                    store.inseparable.insert(population.name.clone(), count + 1);
                }
            }
        }
        store.content_hash = store
            .content_hash
            .wrapping_add(population_hash(&population));
        store.ordered.insert(id, population);
    }

    pub(crate) fn remove(&mut self, name: &str, arguments: &[AlgebraicValue]) {
        let identity = (name.to_owned(), arguments.into(), false);
        let Some(ids) = self
            .0
            .as_ref()
            .and_then(|store| store.exact.get(&identity))
            .cloned()
        else {
            return;
        };
        let store = Arc::make_mut(self.0.as_mut().unwrap());
        let mut family = store.families.get(name).cloned().expect("indexed family");
        for id in ids.iter() {
            let old = store.ordered.remove(id).expect("indexed population");
            store.content_hash = store.content_hash.wrapping_sub(population_hash(&old));
            family.remove(id);
            if let Some(pointer) = unary_pointer(&old.arguments) {
                if offset_root_atom(&pointer.offset).is_some() {
                    let count = *store
                        .symbolic_pointers
                        .get(name)
                        .expect("symbolic pointer count");
                    if count == 1 {
                        store.symbolic_pointers.remove(name);
                    } else {
                        store.symbolic_pointers.insert(name.to_owned(), count - 1);
                    }
                }
                let pointer_key = (old.name.clone(), pointer);
                let mut pointers = store
                    .unary_pointers
                    .get(&pointer_key)
                    .cloned()
                    .expect("indexed pointer");
                pointers.remove(id);
                if pointers.len() == 0 {
                    store.unary_pointers.remove(&pointer_key);
                } else {
                    store.unary_pointers.insert(pointer_key, pointers);
                }
            } else {
                let count = *store
                    .unsupported_pointers
                    .get(name)
                    .expect("unsupported pointer count");
                if count == 1 {
                    store.unsupported_pointers.remove(name);
                } else {
                    store
                        .unsupported_pointers
                        .insert(name.to_owned(), count - 1);
                }
            }
            match separable_block(&old.arguments) {
                Some(block) => {
                    let block_key = (old.name.clone(), block.clone());
                    let mut ids = store
                        .separable_blocks
                        .get(&block_key)
                        .cloned()
                        .expect("indexed separable block");
                    ids.remove(id);
                    if ids.len() == 0 {
                        store.separable_blocks.remove(&block_key);
                    } else {
                        store.separable_blocks.insert(block_key, ids);
                    }
                }
                None => {
                    let count = *store.inseparable.get(name).expect("inseparable count");
                    if count == 1 {
                        store.inseparable.remove(name);
                    } else {
                        store.inseparable.insert(name.to_owned(), count - 1);
                    }
                }
            }
        }
        store.exact.remove(&identity);
        if family.len() == 0 {
            store.families.remove(name);
        } else {
            store.families.insert(name.to_owned(), family);
        }
    }

    /// Complete indexed matches for the supported exact unary-pointer case.
    /// `None` means the caller must retain its general alias-aware scan; it
    /// never means that an unindexed population has quantity zero.
    pub(crate) fn indexed_unary_matches(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
        assumptions: &PureFactContext,
    ) -> Option<Vec<&CCountedPopulation>> {
        let ids = self.indexed_unary_match_ids(name, arguments, assumptions)?;
        let store = self.0.as_ref()?;
        Some(
            ids.into_iter()
                .map(|id| store.ordered.get(&id).expect("indexed population"))
                .collect(),
        )
    }

    /// [`Self::indexed_unary_matches`] by entry id.
    fn indexed_unary_match_ids(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
        assumptions: &PureFactContext,
    ) -> Option<BTreeSet<u64>> {
        let pointer = unary_pointer(arguments)?;
        let Some(store) = &self.0 else {
            return Some(BTreeSet::new());
        };
        let Some(family) = store.families.get(name) else {
            return Some(BTreeSet::new());
        };
        if family.len() == 1 && self.get(name, &[], true).is_some() {
            return Some(BTreeSet::new());
        }
        if store.unsupported_pointers.contains_key(name) {
            return None;
        }
        let root = offset_root_atom(&pointer.offset);
        let only_constant_offsets = root.is_none() && !store.symbolic_pointers.contains_key(name);
        if !only_constant_offsets && assumptions.has_pointer_block_aliases() {
            return None;
        }
        if !assumptions.offsets_with_an_alias_at_root(&root).is_empty() {
            return None;
        }
        match &root {
            Some(PointerOffsetTerm::Int32Scaled { value, .. }) => {
                if assumptions.equality_graph.int32_may_have_aliases(value)
                    || crate::kernel::assumptions::exact_signed_constant(value, assumptions)
                        .is_some()
                    || assumptions.indexed_constant_interval(value).is_some()
                {
                    return None;
                }
            }
            None if !only_constant_offsets => return None,
            _ => {}
        }
        let mut spellings = BTreeSet::from([pointer.clone()]);
        if only_constant_offsets {
            spellings.extend(assumptions.equality_graph.pointer_spellings(&pointer));
            spellings.extend(
                assumptions
                    .pointer_equality_component(&pointer)
                    .into_iter()
                    .map(|(pointer, _)| pointer),
            );
        }
        let mut candidates = BTreeSet::new();
        for spelling in spellings {
            let Some(spelling) = normalized_pointer(&spelling) else {
                continue;
            };
            if let Some(ids) = store.unary_pointers.get(&(name.to_owned(), spelling)) {
                candidates.extend(ids.iter().copied());
            }
        }
        Some(
            candidates
                .into_iter()
                .filter(|id| {
                    crate::instrumentation::record_deterministic_work(1);
                    let population = store.ordered.get(id).expect("indexed population");
                    crate::kernel::resource_arguments_proven_equal(
                        &population.arguments[0],
                        &arguments[0],
                        assumptions,
                    )
                })
                .collect(),
        )
    }
}

impl FromIterator<CCountedPopulation> for CountedPopulations {
    fn from_iter<T: IntoIterator<Item = CCountedPopulation>>(iter: T) -> Self {
        let mut populations = Self::default();
        for population in iter {
            populations.append(population);
        }
        populations
    }
}

impl PartialEq for CountedPopulations {
    fn eq(&self, other: &Self) -> bool {
        self.shares_storage_with(other)
            || (self.len() == other.len()
                && self.0.as_ref().map_or(0, |s| s.content_hash)
                    == other.0.as_ref().map_or(0, |s| s.content_hash)
                && self.iter().eq(other.iter()))
    }
}
impl Eq for CountedPopulations {}
impl Hash for CountedPopulations {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.len().hash(hasher);
        self.0.as_ref().map_or(0, |s| s.content_hash).hash(hasher);
    }
}
impl Ord for CountedPopulations {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.shares_storage_with(other) {
            Ordering::Equal
        } else {
            self.iter().cmp(other.iter())
        }
    }
}
impl PartialOrd for CountedPopulations {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl std::fmt::Debug for CountedPopulations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
