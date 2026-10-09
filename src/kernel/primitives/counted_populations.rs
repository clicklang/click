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

    /// Exactly one added ordinary population, with every previous entry
    /// unchanged. Persistent diff visits changed paths rather than the frame.
    pub(crate) fn single_insertion_from<'a>(
        &'a self,
        before: &Self,
    ) -> Option<&'a CCountedPopulation> {
        if self.len() != before.len().checked_add(1)? {
            return None;
        }
        let after = self.0.as_ref()?;
        let empty = SnapshotMap::new();
        let previous = before.0.as_ref().map_or(&empty, |store| &store.ordered);
        let mut changes = previous.diff(&after.ordered);
        let SnapshotMapChange::Added(id) = changes.next()? else {
            return None;
        };
        if changes.next().is_some() {
            return None;
        }
        let population = after.ordered.get(id)?;
        (!population.family_observation_marker).then_some(population)
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

    /// The populations of `name`'s family that `pattern` names, or the first
    /// one it may or may not name.
    ///
    /// Two keys `R(p)` and `R(q)` denote one population whenever `p == q`, so
    /// a total over the entries proven equal to the pattern is a count only
    /// when every other same-arity entry is proven different from it. An
    /// entry that is neither is the error: `count(R(p))` has no value the
    /// facts determine until `p == q` or `p != q` is established, and a
    /// transfer keyed on `p` may be spending `R(q)`'s units.
    ///
    /// Equality comes from the exact unary-pointer index where it applies, so
    /// no decision runs per entry on that side. Distinctness is structural
    /// for most of a family in practice: when every entry is one pointer
    /// into a separable block and so is the pattern, only the entries in the
    /// pattern's block are visited, the others being distinct objects. A
    /// family holding a parameter-keyed entry is scanned, one work unit per
    /// entry, and the scan ends at the first undecided entry.
    pub(crate) fn pattern_matches(
        &self,
        name: &str,
        pattern: &[Option<AlgebraicValue>],
        assumptions: &PureFactContext,
    ) -> Result<Vec<&CCountedPopulation>, &CCountedPopulation> {
        use crate::kernel::CountedPopulationArgumentRelation as Relation;
        let Some(store) = &self.0 else {
            return Ok(Vec::new());
        };
        let Some(family) = store.families.get(name) else {
            return Ok(Vec::new());
        };
        let equal_ids = match pattern {
            [Some(argument)] => {
                self.indexed_unary_match_ids(name, std::slice::from_ref(argument), assumptions)
            }
            _ => None,
        };
        let separable_candidates = match pattern {
            [Some(AlgebraicValue::C(CValue::Pointer(pointer)))]
                if block_is_separable(&pointer.pointer().block)
                    && store.inseparable.get(name).is_none_or(|count| *count == 0) =>
            {
                Some(
                    store
                        .separable_blocks
                        .get(&(name.to_owned(), pointer.pointer().block.clone()))
                        .map(|ids| ids.iter().copied().collect::<Vec<_>>())
                        .unwrap_or_default(),
                )
            }
            _ => None,
        };
        let candidates: Box<dyn Iterator<Item = u64> + '_> = match separable_candidates {
            Some(ids) => Box::new(ids.into_iter()),
            None => Box::new(family.iter().copied()),
        };
        let mut matching = Vec::new();
        for id in candidates {
            crate::instrumentation::record_deterministic_work(1);
            let population = store.ordered.get(&id).expect("indexed population");
            if population.family_observation_marker || population.arguments.len() != pattern.len() {
                continue;
            }
            let relation = match &equal_ids {
                Some(ids) if ids.contains(&id) => Relation::Equal,
                // The index is complete for proven equality, so an entry it
                // leaves out is not proven equal; only its distinctness is
                // open.
                Some(_) => {
                    if crate::kernel::resource_arguments_proven_different(
                        &population.arguments[0],
                        pattern[0].as_ref().expect("unary pattern"),
                        assumptions,
                    ) {
                        Relation::Different
                    } else {
                        Relation::Undecided
                    }
                }
                None => crate::kernel::counted_population_arguments_relation(
                    &population.arguments,
                    pattern,
                    assumptions,
                ),
            };
            match relation {
                Relation::Equal => matching.push(population),
                Relation::Different => {}
                Relation::Undecided => return Err(population),
            }
        }
        Ok(matching)
    }

    /// Bounded absence checking for the first local-allocation slice. Both
    /// queried and existing arguments must use one-base unary pointers;
    /// rejecting unsupported candidates is essential: an incomplete alias
    /// search cannot establish freshness.
    pub(crate) fn has_unary_pointer_alias(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
        assumptions: &PureFactContext,
    ) -> Result<bool, &'static str> {
        let pointer = unary_pointer(arguments).ok_or("local population initialization requires one pointer argument with a simple symbolic base and constant displacement")?;
        let Some(store) = &self.0 else {
            return Ok(false);
        };
        let Some(family) = store.families.get(name) else {
            return Ok(false);
        };
        if family.len() == 1 && self.get(name, &[], true).is_some() {
            return Ok(false);
        }
        if store.unsupported_pointers.contains_key(name) {
            return Err("existing population arguments require unsupported alias checking");
        }
        let mut spellings = BTreeSet::from([pointer.clone()]);
        spellings.extend(assumptions.equality_graph.pointer_spellings(&pointer));
        spellings.extend(
            assumptions
                .pointer_equality_component(&pointer)
                .into_iter()
                .map(|(pointer, _)| pointer),
        );
        for spelling in spellings {
            let Some(spelling) = normalized_pointer(&spelling) else {
                continue;
            };
            let Some(ids) = store.unary_pointers.get(&(name.to_owned(), spelling)) else {
                continue;
            };
            for id in ids.iter() {
                crate::instrumentation::record_deterministic_work(1);
                let population = store.ordered.get(id).expect("indexed pointer population");
                if crate::kernel::resource_arguments_proven_equal(
                    &population.arguments[0],
                    &arguments[0],
                    assumptions,
                ) {
                    return Ok(true);
                }
            }
        }
        // Exact pointer reasoning also admits translated equalities. Until
        // their full root relation has an index here, refuse an unresolved
        // alias-rich context rather than treating a candidate miss as absence.
        if assumptions.has_pointer_block_aliases() {
            return Err(
                "local population initialization cannot establish freshness through unresolved pointer aliases",
            );
        }
        let root = offset_root_atom(&pointer.offset);
        if !assumptions.offsets_with_an_alias_at_root(&root).is_empty() {
            return Err(
                "local population initialization cannot establish freshness through displaced offset aliases",
            );
        }
        match root {
            Some(PointerOffsetTerm::Int32Scaled { value, .. }) => {
                if assumptions.equality_graph.int32_may_have_aliases(&value)
                    || crate::kernel::assumptions::exact_signed_constant(&value, assumptions)
                        .is_some()
                    || assumptions.indexed_constant_interval(&value).is_some()
                {
                    return Err(
                        "local population initialization cannot establish freshness through integer-index aliases",
                    );
                }
            }
            None if store.symbolic_pointers.contains_key(name) => {
                return Err(
                    "local population initialization cannot establish a constant address fresh from symbolic population indices",
                );
            }
            _ => {}
        }
        Ok(false)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn args(pointer: &Pointer) -> ResourceArguments {
        vec![CValue::pointer(pointer.clone()).into()].into()
    }

    fn external(index: u64) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(index)), 1),
        }
    }

    fn population(index: u64, count: u32) -> CCountedPopulation {
        CCountedPopulation {
            name: "remaining".into(),
            arguments: args(&external(index)),
            count: Bitvector32Term::Constant(count),
            family_observation_marker: false,
        }
    }

    #[test]
    fn population_indices_preserve_order_duplicates_and_marker_distinction() {
        let first = population(1, 2);
        let second = population(2, 3);
        let duplicate = population(1, 4);
        let mut ledger: CountedPopulations = [first.clone(), second.clone(), duplicate.clone()]
            .into_iter()
            .collect();
        assert_eq!(
            ledger.iter().cloned().collect::<Vec<_>>(),
            vec![first.clone(), second.clone(), duplicate]
        );
        ledger.insert(population(1, 7));
        assert_eq!(
            ledger
                .get("remaining", &first.arguments, false)
                .unwrap()
                .count
                .as_const(),
            Some(7)
        );
        assert_eq!(ledger.iter().last().unwrap().count.as_const(), Some(4));
        ledger.remove("remaining", &first.arguments);
        let rebuilt: CountedPopulations = [second].into_iter().collect();
        assert_eq!(ledger, rebuilt);
        assert_eq!(ledger.cmp(&rebuilt), Ordering::Equal);
        let hash = |ledger: &CountedPopulations| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            ledger.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&ledger), hash(&rebuilt));
        let state = CState::new()
            .with_counted_population("empty_args", [].into(), Bitvector32Term::Constant(2))
            .with_observed_population_family("empty_args");
        let state = state.without_counted_population("empty_args", &[]);
        assert!(state.observes_population_family("empty_args"));
        assert!(state.counted_population("empty_args", &[]).is_none());
    }

    #[test]
    fn population_delta_accepts_only_one_insertion_and_no_replacement() {
        let original: CountedPopulations =
            [population(1, 2), population(2, 3)].into_iter().collect();
        let mut after = original.clone();
        after.insert(population(3, 3));
        assert_eq!(
            after.single_insertion_from(&original),
            Some(&population(3, 3))
        );
        let same = after.clone();
        after.insert(population(3, 3));
        assert!(after.shares_storage_with(&same));
        after.insert(population(1, 1));
        assert!(after.single_insertion_from(&original).is_none());
        let mut after = original.clone();
        after.insert(population(3, 3));
        after.insert(population(4, 3));
        assert!(after.single_insertion_from(&original).is_none());
    }

    #[test]
    fn population_freshness_rejects_zero_aliases_and_unresolved_numeric_aliases() {
        let base = external(101);
        let other = external(102);
        let state = CState::new().with_counted_population(
            "remaining",
            args(&base),
            Bitvector32Term::Constant(0),
        );
        let empty = PureFactContext::new();
        assert_eq!(
            state.has_counted_population_unary_pointer_alias("remaining", &args(&base), &empty),
            Ok(true)
        );
        assert_eq!(
            state.has_counted_population_unary_pointer_alias("remaining", &args(&other), &empty),
            Ok(false)
        );
        let aliases = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), other.clone()),
            true,
        );
        assert_eq!(
            state.has_counted_population_unary_pointer_alias("remaining", &args(&other), &aliases),
            Ok(true)
        );
        let integers = empty.assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(101)),
                Bitvector32Term::Variable(Variable(102)),
            ),
            true,
        );
        assert!(
            state
                .has_counted_population_unary_pointer_alias("remaining", &args(&other), &integers)
                .is_err()
        );
        let a = Pointer::symbolic(Variable(201));
        let b = Pointer::symbolic(Variable(202));
        let shifted = CState::new().with_counted_population(
            "remaining",
            args(&a.offset_by_bytes(16)),
            Bitvector32Term::Constant(0),
        );
        let relation = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.offset_by_bytes(8), b.offset_by_bytes(12)),
            true,
        );
        assert_eq!(
            shifted.has_counted_population_unary_pointer_alias(
                "remaining",
                &args(&b.offset_by_bytes(20)),
                &relation
            ),
            Ok(true)
        );
    }

    #[test]
    fn exact_population_lookup_insertion_and_delta_ignore_unrelated_populations() {
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut before = CState::new();
            for index in 0..size {
                before = before.with_counted_population(
                    "remaining",
                    args(&external(index)),
                    Bitvector32Term::Constant(3),
                );
            }
            let assumptions = PureFactContext::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let original = before.clone();
                assert!(
                    original
                        .counted_populations
                        .shares_storage_with(&before.counted_populations)
                );
                assert_eq!(
                    before
                        .counted_population("remaining", &args(&external(size - 1)))
                        .and_then(Bitvector32Term::as_const),
                    Some(3)
                );
                assert_eq!(
                    before.has_counted_population_unary_pointer_alias(
                        "remaining",
                        &args(&external(size)),
                        &assumptions
                    ),
                    Ok(false)
                );
                let added = before.clone().with_counted_population(
                    "remaining",
                    args(&external(size)),
                    Bitvector32Term::Constant(3),
                );
                assert!(
                    added
                        .counted_populations
                        .single_insertion_from(&before.counted_populations)
                        .is_some()
                );
                let updated = added.clone().with_counted_population(
                    "remaining",
                    args(&external(size)),
                    Bitvector32Term::Constant(2),
                );
                assert_eq!(
                    updated
                        .counted_population("remaining", &args(&external(size)))
                        .and_then(Bitvector32Term::as_const),
                    Some(2)
                );
                assert!(
                    updated
                        .counted_populations
                        .single_insertion_from(&added.counted_populations)
                        .is_none()
                );
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 2 + 16,
                "population operation scans its frame: {samples:?}"
            );
        }
    }

    #[test]
    fn population_freshness_does_not_build_an_index_of_unrelated_path_facts() {
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let state = CState::new().with_counted_population(
                "remaining",
                args(&external(40_000)),
                Bitvector32Term::Constant(3),
            );
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(50_000 + index)),
                        Bitvector32Term::Constant(index as u32),
                    ),
                    true,
                );
            }
            // Registration of a use is not a second member of the index's
            // equality class and must not forbid an unrelated initializer.
            let index = Bitvector32Term::Variable(Variable(40_001));
            let offset = PointerOffsetTerm::scale_int32(index.clone(), 1);
            assert!(
                assumptions
                    .equality_graph
                    .are_offsets_equal(&offset, &offset)
            );
            assert!(!assumptions.equality_graph.int32_may_have_aliases(&index));
            PureFactContext::reset_bitvector_equality_index_fact_visits();
            let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
                state.has_counted_population_unary_pointer_alias(
                    "remaining",
                    &args(&external(40_001)),
                    &assumptions,
                )
            });
            assert_eq!(answer, Ok(false));
            assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 2 + 16,
                "freshness scans unrelated facts: {samples:?}"
            );
        }
        let marker_only = CState::new().with_observed_population_family("remaining");
        let aliases = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(external(1), external(2)), true);
        assert_eq!(
            marker_only.has_counted_population_unary_pointer_alias(
                "remaining",
                &args(&external(3)),
                &aliases
            ),
            Ok(false)
        );
        assert_eq!(
            marker_only.has_counted_population_unary_pointer_alias(
                "other",
                &args(&external(3)),
                &aliases
            ),
            Ok(false)
        );
    }
}
