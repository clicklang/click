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
        let pointer = unary_pointer(arguments)?;
        let Some(store) = &self.0 else {
            return Some(Vec::new());
        };
        let Some(family) = store.families.get(name) else {
            return Some(Vec::new());
        };
        if family.len() == 1 && self.get(name, &[], true).is_some() {
            return Some(Vec::new());
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
                .filter_map(|id| {
                    crate::instrumentation::record_deterministic_work(1);
                    let population = store.ordered.get(&id).expect("indexed population");
                    crate::kernel::resource_arguments_proven_equal(
                        &population.arguments[0],
                        &arguments[0],
                        assumptions,
                    )
                    .then_some(population)
                })
                .collect(),
        )
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
    fn load_population_classification_is_stable_across_registry_changes() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("load-source", 4));
        let address = Pointer {
            block: "load-source".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mint = || {
            crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &address,
                crate::kernel::LoadKind::Bits32,
                4,
            )
        };
        let variable = mint();
        assert!(crate::kernel::is_load_variable(&variable));
        let assumptions = PureFactContext::new();
        for raw_offset in [false, true] {
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: if raw_offset {
                    PointerOffsetTerm::Variable(variable)
                } else {
                    PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(variable), 1)
                },
            };
            let population = CCountedPopulation {
                name: "remaining".into(),
                arguments: args(&pointer),
                count: Bitvector32Term::Constant(2),
                family_observation_marker: false,
            };
            for insert_registered in [false, true] {
                crate::kernel::eval::clear_load_variable_registry();
                if insert_registered {
                    assert_eq!(mint(), variable);
                }
                let mut ledger: CountedPopulations = [population.clone()].into_iter().collect();
                for registered in [false, true, false] {
                    crate::kernel::eval::clear_load_variable_registry();
                    if registered {
                        assert_eq!(mint(), variable);
                    }
                    assert!(normalized_pointer(&pointer).is_none());
                    assert!(
                        ledger
                            .indexed_unary_matches("remaining", &args(&external(123)), &assumptions)
                            .is_none(),
                        "a stored reserved load ID prevents an incomplete absence answer"
                    );
                    assert!(
                        ledger
                            .has_unary_pointer_alias(
                                "remaining",
                                &args(&external(123)),
                                &assumptions
                            )
                            .is_err()
                    );
                    assert!(
                        ledger
                            .has_unary_pointer_alias("remaining", &args(&pointer), &assumptions)
                            .is_err()
                    );
                    assert_eq!(
                        ledger.get("remaining", &args(&pointer), false),
                        Some(&population)
                    );
                    let mut state = CState::new();
                    state.counted_populations = ledger.clone();
                    let aliased = assumptions.clone().assume_condition(
                        ConditionTerm::pointer_equal(pointer.clone(), external(123)),
                        true,
                    );
                    assert_eq!(
                        evaluate_count(&state, Some(&external(123)), &aliased),
                        2,
                        "general Count matching must retain aliased load populations"
                    );
                }
                // Remove in the opposite registry state from insertion. The
                // structural classification must debit the same index.
                if !insert_registered {
                    assert_eq!(mint(), variable);
                }
                ledger.remove("remaining", &args(&pointer));
                assert!(ledger.is_empty());
                assert_eq!(
                    ledger.has_unary_pointer_alias(
                        "remaining",
                        &args(&external(123)),
                        &assumptions
                    ),
                    Ok(false)
                );
            }
        }
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

    fn evaluate_count(
        state: &CState,
        pointer: Option<&Pointer>,
        assumptions: &PureFactContext,
    ) -> u32 {
        let expression = crate::kernel::SpecExpression::CountedResourceCount {
            name: "remaining".into(),
            arguments: vec![pointer.map(|pointer| {
                crate::kernel::SpecExpression::Value(CValue::pointer(pointer.clone()))
            })],
        };
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &expression,
            assumptions,
            &BTreeMap::new(),
            &mut crate::kernel::ExecutionBudget::beside_live_state(),
        )
        .expect("count evaluates");
        assert_eq!(paths.len(), 1);
        assert!(paths[0].obligations.is_empty());
        let CValue::Int32(value) = &paths[0].value else {
            panic!("count must be int32")
        };
        value.as_const().expect("constant population sum")
    }

    #[test]
    fn indexed_count_sums_duplicate_keys_and_known_pointer_aliases() {
        let mut state = CState::new();
        state.counted_populations = [population(10, 2), population(10, 3)].into_iter().collect();
        assert_eq!(
            evaluate_count(&state, Some(&external(10)), &PureFactContext::new()),
            5
        );
        assert_eq!(evaluate_count(&state, None, &PureFactContext::new()), 5);

        let left = Pointer::symbolic(Variable(20));
        let right = Pointer::symbolic(Variable(21));
        let state = CState::new()
            .with_counted_population(
                "remaining",
                args(&left.offset_by_bytes(16)),
                Bitvector32Term::Constant(2),
            )
            .with_counted_population(
                "remaining",
                args(&right.offset_by_bytes(20)),
                Bitvector32Term::Constant(3),
            );
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(left.offset_by_bytes(8), right.offset_by_bytes(12)),
            true,
        );
        let query = right.offset_by_bytes(20);
        let indexed = state
            .counted_populations
            .indexed_unary_matches("remaining", &args(&query), &assumptions)
            .expect("constant-displacement pointer aliases are indexed");
        assert_eq!(indexed.len(), 2);
        assert_eq!(evaluate_count(&state, Some(&query), &assumptions), 5);
        // The original sequence API selected the first matching alias even
        // when a later population has the query's exact spelling.
        let selected = state
            .counted_population_proven_equal("remaining", &args(&query), &assumptions)
            .unwrap();
        assert_eq!(selected.1, args(&left.offset_by_bytes(16)));
        assert_eq!(selected.2.as_const(), Some(2));
    }

    #[test]
    fn count_falls_back_for_scalar_and_displaced_scalar_aliases() {
        let x = external(30);
        let y = external(31);
        let state = CState::new()
            .with_counted_population("remaining", args(&x), Bitvector32Term::Constant(2))
            .with_counted_population("remaining", args(&y), Bitvector32Term::Constant(3));
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(30)),
                Bitvector32Term::Variable(Variable(31)),
            ),
            true,
        );
        assert!(
            state
                .counted_populations
                .indexed_unary_matches("remaining", &args(&x), &assumptions)
                .is_none()
        );
        assert_eq!(evaluate_count(&state, Some(&x), &assumptions), 5);

        let x = x.offset_by_bytes(5);
        let y = y.offset_by_bytes(4);
        let state = CState::new()
            .with_counted_population("remaining", args(&x), Bitvector32Term::Constant(2))
            .with_counted_population("remaining", args(&y), Bitvector32Term::Constant(3));
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::add(
                    Bitvector32Term::Variable(Variable(30)),
                    Bitvector32Term::Constant(5),
                ),
                Bitvector32Term::add(
                    Bitvector32Term::Variable(Variable(31)),
                    Bitvector32Term::Constant(4),
                ),
            ),
            true,
        );
        assert!(
            state
                .counted_populations
                .indexed_unary_matches("remaining", &args(&x), &assumptions)
                .is_none()
        );
        assert!(
            state
                .has_counted_population_unary_pointer_alias(
                    "remaining",
                    &args(&external(30).offset_by_bytes(6)),
                    &assumptions
                )
                .is_err()
        );
        // The indexed path must preserve precisely the general evaluator's
        // matching relation, including displacement overflow obligations.
        let expected: u32 = state
            .counted_populations()
            .filter(|population| {
                crate::kernel::resource_arguments_proven_equal(
                    &population.arguments[0],
                    &args(&x)[0],
                    &assumptions,
                )
            })
            .map(|population| population.count.as_const().unwrap())
            .sum();
        assert_eq!(evaluate_count(&state, Some(&x), &assumptions), expected);
    }

    #[test]
    fn exact_count_evaluation_ignores_unrelated_same_family_populations() {
        for pointer_kind in 0..3 {
            let mut samples = Vec::new();
            for size in [16u64, 64, 256, 1024] {
                let pointer = |index| match pointer_kind {
                    0 => external(80_000 + index),
                    1 => Pointer::symbolic(Variable(80_000 + index)),
                    _ => Pointer {
                        block: PointerBlock::Concrete(format!("population-{index}")),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                };
                let mut state = CState::new();
                let mut assumptions = PureFactContext::new();
                for index in 0..size {
                    state = state.with_counted_population(
                        "remaining",
                        args(&pointer(index)),
                        Bitvector32Term::Constant(3),
                    );
                    assumptions = assumptions.assume_condition(
                        ConditionTerm::equal(
                            Bitvector32Term::Variable(Variable(90_000 + index)),
                            Bitvector32Term::Constant(index as u32),
                        ),
                        true,
                    );
                }
                PureFactContext::reset_bitvector_equality_index_fact_visits();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    assert_eq!(
                        evaluate_count(&state, Some(&pointer(size - 1)), &assumptions),
                        3
                    );
                    assert_eq!(
                        evaluate_count(&state, Some(&pointer(size)), &assumptions),
                        0
                    );
                });
                assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0] * 2 + 32,
                    "exact Count scans unrelated populations or facts: {samples:?}"
                );
            }
        }
    }
}
