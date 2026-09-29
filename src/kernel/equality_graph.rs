//! Trusted kernel equality graph.
//!
//! This graph is part of the trusted kernel. Kernel rules may accept its
//! equality answers directly in the current proof context; it does not emit
//! a separate proof or run proof search. Only established equalities may be
//! added. Branches clone persistent state so local assumptions do not leak.
//!
//! The current supported fragment is pointers, affine byte offsets, and
//! registered same-snapshot pointer loads, plus whole-offset equality, int32 addition and same-snapshot int32 load congruence.
//! Pointer and offset queries are typed separately; the offset fragment only
//! supports stated equalities, offset addition and int32 scaling congruence. Pointer spelling
//! helpers serve legacy consumers and are not the general equality interface.
//!
//! The pointer fragment uses a persistent union-find with offsets.
//!
//! A pointer is a block and a byte offset, and its address is the block's
//! base address plus the offset. A true pointer equality `p == q` between
//! two blocks therefore states a relation between the two blocks' bases:
//! `base(p.block) = base(q.block) + (q.offset - p.offset)`. The index keeps
//! every block that such facts connect in one class, with each member's base
//! stated relative to the class representative:
//! `base(member) = base(representative) + delta`.
//!
//! Two pointers are then equal exactly when their blocks share a
//! representative and `delta + offset` normalizes to the same affine form on
//! both sides. That answers transitive chains (`a == b`, `b == c`) and
//! displaced spellings (`a + 8` against `c + 8`) with two lookups, with no
//! walk over the facts and no displacement rule. It is the pointer sort of
//! the equality closure described in `docs/internals/equality-closure.md`.
//!
//! Offsets are compared in an exact integer affine normal form: constants
//! folded, each scaled index an atom with its accumulated byte coefficient,
//! and each atom in the kernel's canonical term form, so a load and the load
//! variable naming it are one atom.
//! The form is exact integer arithmetic with overflow checked, so two offsets
//! with one normal form denote one integer under any reading of the offset,
//! wrapping or not. An offset whose arithmetic overflows the form is not
//! normalized, and a fact about it is not filed.
//!
//! The index is persistent and append-only. A union relabels every member of
//! the lighter class (blocks plus application uses), so member lookup is one
//! map access and each moved block/use is charged to a growing class. Affine
//! payload work is charged separately. Same-snapshot load signatures propagate
//! merges iteratively through indexed parent uses, with no nesting cutoff. An
//! equality between two blocks already in one class adds nothing here: it
//! relates offsets, not bases, and stays with the offset facts.

use super::prelude::*;

#[cfg(test)]
mod int32_addition_tests;
#[cfg(test)]
mod int32_load_tests;
#[cfg(test)]
mod int32_tests;
#[cfg(test)]
mod scaled_int32_tests;
mod terms;

/// A retained, interned machine atom. Equality and ordering use the stable
/// ID; the original term is retained for exact premise support and spelling
/// reconstruction.
#[derive(Clone)]
pub(in crate::kernel) struct MachineAtom(crate::kernel::SharedMachineIntegerTerm);

impl MachineAtom {
    fn new(ty: crate::kernel::MachineIntegerType, value: Bitvector32Term) -> Self {
        Self(crate::kernel::SharedMachineIntegerTerm::intern(ty, value))
    }
    pub(in crate::kernel) fn int32(value: Bitvector32Term) -> Self {
        Self::new(crate::kernel::MachineIntegerType::Int32, value)
    }
    pub(in crate::kernel) fn value(&self) -> &Bitvector32Term {
        self.0.value()
    }
}
impl std::fmt::Debug for MachineAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.id().fmt(f)
    }
}
impl PartialEq for MachineAtom {
    fn eq(&self, other: &Self) -> bool {
        self.0.id() == other.0.id()
    }
}
impl Eq for MachineAtom {}
impl PartialOrd for MachineAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for MachineAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.id().cmp(&other.0.id())
    }
}
impl std::hash::Hash for MachineAtom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.id().hash(state);
    }
}

/// One atom of an affine offset: a quantity the normal form does not
/// decompose, with the numeric reading the offset term gives it.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) enum OffsetAtom {
    /// A 64-bit offset variable.
    Variable(Variable),
    /// A 32-bit index, sign-extended.
    Int32(MachineAtom),
    /// A 64-bit index, signed or unsigned.
    Int64 { value: MachineAtom, unsigned: bool },
}

impl OffsetAtom {
    fn spelling_cmp(&self, other: &Self) -> std::cmp::Ordering {
        use OffsetAtom::*;
        match (self, other) {
            (Variable(a), Variable(b)) => a.cmp(b),
            (Int32(a), Int32(b)) => a.value().cmp(b.value()),
            (
                Int64 {
                    value: a,
                    unsigned: au,
                },
                Int64 {
                    value: b,
                    unsigned: bu,
                },
            ) => a.value().cmp(b.value()).then(au.cmp(bu)),
            (Variable(_), _) | (Int32(_), Int64 { .. }) => std::cmp::Ordering::Less,
            _ => std::cmp::Ordering::Greater,
        }
    }
}

/// `constant + sum(coefficient * atom)` over exact integers, with no zero
/// coefficient stored.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) struct AffineOffset {
    constant: i128,
    terms: std::collections::BTreeMap<OffsetAtom, i128>,
}

impl AffineOffset {
    pub(in crate::kernel) fn constant(value: i128) -> Self {
        Self {
            constant: value,
            terms: std::collections::BTreeMap::new(),
        }
    }

    fn add_atom(&mut self, atom: OffsetAtom, coefficient: i128) -> Option<()> {
        if coefficient != 0 {
            let entry = self.terms.entry(atom.clone()).or_insert(0);
            *entry = entry.checked_add(coefficient)?;
            if *entry == 0 {
                self.terms.remove(&atom);
            }
        }
        Some(())
    }

    /// Normalize the explicit offset in one iterative traversal. Building a
    /// fresh form at every Add node would copy a growing prefix quadratically.
    pub(in crate::kernel) fn of(offset: &PointerOffsetTerm) -> Option<Self> {
        let mut result = Self::default();
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Constant(value) => {
                    result.constant = result.constant.checked_add(i128::from(*value))?;
                }
                PointerOffsetTerm::Variable(variable) => {
                    result.add_atom(OffsetAtom::Variable(*variable), 1)?;
                }
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    let width = i128::from(*byte_width);
                    if let Some(value) = value.as_const() {
                        result.constant = result
                            .constant
                            .checked_add(i128::from(value as i32).checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int32(MachineAtom::new(
                                crate::kernel::MachineIntegerType::Int32,
                                crate::kernel::canonical_term(value),
                            )),
                            width,
                        )?;
                    }
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let width = i128::from(*byte_width);
                    let constant = if *unsigned {
                        value.uint64_as_const().map(i128::from)
                    } else {
                        value.int64_as_const().map(i128::from)
                    };
                    if let Some(value) = constant {
                        result.constant = result.constant.checked_add(value.checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int64 {
                                value: MachineAtom::new(
                                    if *unsigned {
                                        crate::kernel::MachineIntegerType::UInt64
                                    } else {
                                        crate::kernel::MachineIntegerType::Int64
                                    },
                                    crate::kernel::canonical_term(value),
                                ),
                                unsigned: *unsigned,
                            },
                            width,
                        )?;
                    }
                }
            }
        }
        Some(result)
    }

    pub(in crate::kernel) fn checked_add(&self, other: &Self) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(self.terms.len() + other.terms.len());
        let mut sum = self.clone();
        sum.constant = sum.constant.checked_add(other.constant)?;
        for (atom, coefficient) in &other.terms {
            let entry = sum.terms.entry(atom.clone()).or_insert(0);
            *entry = entry.checked_add(*coefficient)?;
            if *entry == 0 {
                sum.terms.remove(atom);
            }
        }
        Some(sum)
    }

    pub(in crate::kernel) fn checked_negate(&self) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(self.terms.len());
        let mut negated = Self::constant(self.constant.checked_neg()?);
        for (atom, coefficient) in &self.terms {
            negated
                .terms
                .insert(atom.clone(), coefficient.checked_neg()?);
        }
        Some(negated)
    }

    pub(in crate::kernel) fn checked_sub(&self, other: &Self) -> Option<Self> {
        self.checked_add(&other.checked_negate()?)
    }

    /// The offset term this form denotes, or `None` when an atom's
    /// coefficient has no offset spelling (a variable scaled by anything but
    /// one) or a value leaves `i64`.
    pub(in crate::kernel) fn to_offset_term(&self) -> Option<PointerOffsetTerm> {
        let mut term = PointerOffsetTerm::Constant(i64::try_from(self.constant).ok()?);
        // Compact IDs depend on interning order. Legacy spelling output must
        // retain structural order so proof routes do not depend on that order.
        let mut terms: Vec<_> = self.terms.iter().collect();
        terms.sort_by(|(left, _), (right, _)| left.spelling_cmp(right));
        for (atom, coefficient) in terms {
            let coefficient = i64::try_from(*coefficient).ok()?;
            let addend = match atom {
                OffsetAtom::Variable(variable) if coefficient == 1 => {
                    PointerOffsetTerm::Variable(*variable)
                }
                OffsetAtom::Variable(_) => return None,
                OffsetAtom::Int32(value) => PointerOffsetTerm::Int32Scaled {
                    value: Box::new(value.value().clone()),
                    byte_width: coefficient,
                },
                OffsetAtom::Int64 { value, unsigned } => PointerOffsetTerm::Int64Scaled {
                    value: Box::new(value.value().clone()),
                    byte_width: coefficient,
                    unsigned: *unsigned,
                },
            };
            term = PointerOffsetTerm::add(term, addend);
        }
        Some(term)
    }
}

/// A pointer in class-relative form: the representative block, and the
/// address's offset from that representative's base.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) struct CanonicalPointer {
    pub(in crate::kernel) representative: PointerBlock,
    pub(in crate::kernel) offset: AffineOffset,
}

/// Closed, persistent pointer, offset, and int32 equality state. Query registration
/// adds only terms and definitional load applications; hypotheses enter through
/// `add_equality`, `add_offset_equality`, and `add_int32_equality`.
/// Cloning copies the persistent roots into a new lock, never a shared mutable
/// graph. The lock preserves `PureFactContext`'s Send/Sync contract.
#[derive(Default)]
pub(in crate::kernel) struct EqualityGraph {
    state: std::sync::Mutex<EqualityGraphState>,
}

impl Clone for EqualityGraph {
    fn clone(&self) -> Self {
        Self {
            state: std::sync::Mutex::new(self.state.lock().expect("equality graph").clone()),
        }
    }
}

impl std::fmt::Debug for EqualityGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self.state.lock().expect("equality graph");
        f.debug_struct("EqualityGraph")
            .field("members", &state.parent.len())
            .field("loads", &state.loads.len())
            .finish()
    }
}

/// A signature compares only snapshot identities, block identities and an
/// interned affine-offset ID. It never compares snapshots or load trees.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct LoadSignature {
    memory: (u32, u32),
    address_block: PointerBlock,
    address_offset: u64,
}

#[derive(Clone)]
struct LoadApplication {
    memory: (u32, u32),
    address_block: PointerBlock,
    address_offset: AffineOffset,
}

/// Hash-consing the affine sequence uses shallow keys. Offset atoms hold
/// interned machine terms, so a map comparison never descends into a term.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum OffsetPart {
    Constant(i128),
    Term(u64, OffsetAtom, i128),
}

#[derive(Clone, Default)]
struct EqualityGraphState {
    terms: terms::TermClasses,
    parent: crate::persistent::PersistentMap<PointerBlock, (PointerBlock, AffineOffset)>,
    members: crate::persistent::PersistentMap<
        PointerBlock,
        crate::persistent::PersistentMap<PointerBlock, AffineOffset>,
    >,
    // Weight includes application uses, so repeatedly joining a fresh block
    // to one with many parents never reindexes the large side.
    weights: crate::persistent::PersistentMap<PointerBlock, usize>,
    loads: crate::persistent::PersistentMap<PointerBlock, LoadApplication>,
    uses: crate::persistent::PersistentMap<
        PointerBlock,
        crate::persistent::PersistentSet<PointerBlock>,
    >,
    signatures: crate::persistent::PersistentMap<LoadSignature, PointerBlock>,
    load_signatures: crate::persistent::PersistentMap<PointerBlock, LoadSignature>,
    offset_parts: crate::persistent::PersistentMap<OffsetPart, u64>,
}

impl EqualityGraph {
    /// Whether term classes have established any nontrivial equivalence.
    /// Callers can avoid interning unrelated query terms in an empty graph.
    pub(in crate::kernel) fn has_term_equivalences(&self) -> bool {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .has_equivalences()
    }

    /// Query the maintained closure, registering supported load applications
    /// on demand. A false answer means equality is not established here,
    /// not that the operands are unequal. No frame or heuristic search runs.
    pub(in crate::kernel) fn are_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        if left == right {
            return true;
        }
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([left.block.clone(), right.block.clone()]);
        // Different classes cannot meet by offset normalization. In
        // particular, do not traverse an unrelated allocation's offset just
        // to discover that its block has no equality with the query's block.
        let (left_rep, left_delta) = state.find(&left.block);
        let (right_rep, right_delta) = state.find(&right.block);
        if left_rep != right_rep {
            return false;
        }
        let affine_equal = match (
            AffineOffset::of(&left.offset).and_then(|offset| left_delta.checked_add(&offset)),
            AffineOffset::of(&right.offset).and_then(|offset| right_delta.checked_add(&offset)),
        ) {
            (Some(left), Some(right)) => left == right,
            _ => false,
        };
        affine_equal
            // Term-class offset equality is exact byte-offset equality. For
            // one block, it can close explicit offset edges and int32-scaled
            // congruence without changing the affine relation between blocks.
            || (left.block == right.block && state.terms.are_equal(&left.offset, &right.offset))
    }

    /// Query explicit offset equality, addition and int32 scaling congruence.
    /// This fragment does not solve arithmetic or perform cancellation.
    pub(in crate::kernel) fn are_offsets_equal(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .are_equal(left, right)
    }

    /// Query int32 equality, addition and registered same-snapshot load congruence.
    /// A false answer is unknown. Other scalar operations remain opaque.
    pub(in crate::kernel) fn are_int32_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .are_int32_equal(left, right)
    }

    /// A conservative indexed alias-presence query. This does not establish
    /// any equality; callers may use a positive answer to decline a narrow
    /// freshness rule without rebuilding or walking the context's fact index.
    pub(in crate::kernel) fn int32_may_have_aliases(&self, term: &Bitvector32Term) -> bool {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .int32_may_have_aliases(term)
    }

    /// Admit an already established int32 equality in this proof context.
    pub(in crate::kernel) fn add_int32_equality(
        &mut self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.state
            .get_mut()
            .expect("equality graph")
            .terms
            .add_int32_equality(left, right)
    }

    /// Admit an already established offset equality in this proof context.
    pub(in crate::kernel) fn add_offset_equality(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        self.state
            .get_mut()
            .expect("equality graph")
            .terms
            .add_equality(left, right)
    }

    /// Admit an equality already established in this proof context and
    /// propagate its supported congruence consequences. Returns whether a
    /// class merge occurred, not whether the supplied equality is valid.
    pub(in crate::kernel) fn add_equality(&mut self, left: &Pointer, right: &Pointer) -> bool {
        let state = self.state.get_mut().expect("equality graph");
        state.register_blocks([left.block.clone(), right.block.clone()]);
        state.close(vec![(left.clone(), right.clone())])
    }
}

/// Pointer-specific compatibility queries for consumers not yet indexed by
/// equality. These enumerate spellings separately from `are_equal`.
impl EqualityGraph {
    pub(in crate::kernel) fn pointer_is_classed(&self, block: &PointerBlock) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        state.parent.contains_key(block) || state.members.contains_key(block)
    }

    /// Transitional resource consumers still enumerate spellings. This is
    /// deliberately separate from congruence lookup, which never enumerates.
    fn pointer_class_members(&self, block: &PointerBlock) -> Vec<(PointerBlock, AffineOffset)> {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        let (representative, own) = state.find(block);
        let mut blocks = Vec::new();
        let mut push = |member: &PointerBlock, delta: &AffineOffset| {
            if let Some(delta) = own.checked_sub(delta) {
                blocks.push((member.clone(), delta));
            }
        };
        push(&representative, &AffineOffset::default());
        if let Some(members) = state.members.get(&representative) {
            for (member, delta) in members {
                push(member, delta);
            }
        }
        blocks
    }

    pub(in crate::kernel) fn pointer_spellings(&self, pointer: &Pointer) -> Vec<Pointer> {
        if !self.pointer_is_classed(&pointer.block) {
            return Vec::new();
        }
        self.pointer_class_members(&pointer.block)
            .into_iter()
            .filter(|(member, _)| member != &pointer.block)
            .filter_map(|(member, delta)| {
                Some(Pointer {
                    block: member,
                    offset: PointerOffsetTerm::add(pointer.offset.clone(), delta.to_offset_term()?),
                })
            })
            .collect()
    }
}

impl EqualityGraphState {
    fn find(&self, block: &PointerBlock) -> (PointerBlock, AffineOffset) {
        crate::instrumentation::record_deterministic_work(1);
        self.parent
            .get(block)
            .cloned()
            .unwrap_or_else(|| (block.clone(), AffineOffset::default()))
    }

    fn canonical(&self, pointer: &Pointer) -> Option<CanonicalPointer> {
        let offset = AffineOffset::of(&pointer.offset)?;
        let (representative, delta) = self.find(&pointer.block);
        Some(CanonicalPointer {
            representative,
            offset: delta.checked_add(&offset)?,
        })
    }

    fn weight(&self, block: &PointerBlock) -> usize {
        self.weights.get(block).copied().unwrap_or(1)
    }

    fn intern_offset(&mut self, offset: &AffineOffset) -> u64 {
        let mut part = OffsetPart::Constant(offset.constant);
        let mut id = self.intern_offset_part(part);
        for (atom, coefficient) in &offset.terms {
            part = OffsetPart::Term(id, atom.clone(), *coefficient);
            id = self.intern_offset_part(part);
        }
        id
    }

    fn intern_offset_part(&mut self, part: OffsetPart) -> u64 {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(id) = self.offset_parts.get(&part) {
            return *id;
        }
        let id = u64::try_from(self.offset_parts.len()).expect("affine identity capacity");
        self.offset_parts.insert(part, id);
        id
    }

    /// Register the explicit roots and their load-address dependencies once,
    /// with an iterative traversal rather than a semantic nesting limit.
    fn register_blocks(&mut self, roots: impl IntoIterator<Item = PointerBlock>) {
        let is_load = |block: &PointerBlock| matches!(block, PointerBlock::Symbolic(variable) if crate::kernel::is_load_variable(variable));
        let mut pending: Vec<_> = roots.into_iter().filter(is_load).collect();
        let mut equalities = Vec::new();
        while let Some(block) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if self.loads.contains_key(&block) {
                continue;
            }
            let PointerBlock::Symbolic(variable) = &block else {
                continue;
            };
            // Only pointer-width reads can denote a load-backed pointer.
            // A smaller read may later be registered as a pointer-width read,
            // so it must not be permanently negative-cached here.
            if !crate::kernel::is_load_variable(variable)
                || crate::kernel::registered_load_bytes_for_variable(variable) != Some(8)
            {
                continue;
            }
            let Some((memory, address)) = crate::kernel::registered_load_for_variable(variable)
            else {
                continue;
            };
            let Some(address_offset) = AffineOffset::of(&address.offset) else {
                continue;
            };
            self.loads.insert(
                block.clone(),
                LoadApplication {
                    memory: memory.arena_id(),
                    address_block: address.block.clone(),
                    address_offset,
                },
            );
            let users = self.uses.get(&address.block).cloned().unwrap_or_default();
            self.uses
                .insert(address.block.clone(), users.with_value(block.clone()));
            let (representative, _) = self.find(&address.block);
            self.weights
                .insert(representative.clone(), self.weight(&representative) + 1);
            self.reindex_load(&block, &mut equalities);
            if is_load(&address.block) {
                pending.push(address.block);
            }
        }
        self.close(equalities);
    }

    fn reindex_load(&mut self, block: &PointerBlock, equalities: &mut Vec<(Pointer, Pointer)>) {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(old) = self.load_signatures.get(block).cloned() {
            if self.signatures.get(&old) == Some(block) {
                self.signatures.remove(&old);
            }
            self.load_signatures.remove(block);
        }
        let load = self.loads.get(block).expect("registered load").clone();
        let (address_block, delta) = self.find(&load.address_block);
        let Some(offset) = delta.checked_add(&load.address_offset) else {
            return;
        };
        let signature = LoadSignature {
            memory: load.memory,
            address_block,
            address_offset: self.intern_offset(&offset),
        };
        if let Some(other) = self.signatures.get(&signature) {
            if other != block {
                equalities.push((
                    Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    Pointer {
                        block: other.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                ));
            }
        } else {
            self.signatures.insert(signature.clone(), block.clone());
        }
        self.load_signatures.insert(block.clone(), signature);
    }

    fn close(&mut self, mut equalities: Vec<(Pointer, Pointer)>) -> bool {
        let mut changed = false;
        while let Some((left, right)) = equalities.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let (Some(left), Some(right)) = (self.canonical(&left), self.canonical(&right)) else {
                continue;
            };
            if left.representative == right.representative {
                continue;
            }
            let Some(left_from_right) = right.offset.checked_sub(&left.offset) else {
                continue;
            };
            let (moved, kept, delta) =
                if self.weight(&left.representative) <= self.weight(&right.representative) {
                    (left.representative, right.representative, left_from_right)
                } else {
                    let Some(delta) = left_from_right.checked_negate() else {
                        continue;
                    };
                    (right.representative, left.representative, delta)
                };
            changed |= self.relabel(moved, kept, delta, &mut equalities);
        }
        changed
    }

    fn relabel(
        &mut self,
        moved: PointerBlock,
        kept: PointerBlock,
        moved_from_kept: AffineOffset,
        equalities: &mut Vec<(Pointer, Pointer)>,
    ) -> bool {
        let mut deltas = vec![(moved.clone(), moved_from_kept.clone())];
        if let Some(members) = self.members.get(&moved) {
            for (member, delta) in members {
                let Some(delta) = delta.checked_add(&moved_from_kept) else {
                    return false;
                };
                deltas.push((member.clone(), delta));
            }
        }
        crate::instrumentation::record_deterministic_work(deltas.len());
        let mut kept_members = self.members.get(&kept).cloned().unwrap_or_default();
        self.weights
            .insert(kept.clone(), self.weight(&moved) + self.weight(&kept));
        self.weights.remove(&moved);
        let mut affected = Vec::new();
        for (member, delta) in deltas {
            if let Some(users) = self.uses.get(&member) {
                affected.extend(users.iter().cloned());
            }
            self.parent
                .insert(member.clone(), (kept.clone(), delta.clone()));
            kept_members.insert(member, delta);
        }
        self.members.remove(&moved);
        self.members.insert(kept, kept_members);
        for load in affected {
            self.reindex_load(&load, equalities);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbolic(id: u64) -> PointerBlock {
        PointerBlock::Symbolic(Variable(id))
    }

    fn at(block: PointerBlock, offset: i64) -> Pointer {
        Pointer {
            block,
            offset: PointerOffsetTerm::Constant(offset),
        }
    }

    fn index(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    #[test]
    fn offsets_spelled_differently_share_one_normal_form() {
        let nested = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index(7)),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
            Box::new(PointerOffsetTerm::Constant(4)),
        );
        let flat = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(7)),
                byte_width: 4,
            }),
        );
        assert_eq!(AffineOffset::of(&nested), AffineOffset::of(&flat));
        let other_index = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(8)),
                byte_width: 4,
            }),
        );
        assert_ne!(AffineOffset::of(&flat), AffineOffset::of(&other_index));
    }

    #[test]
    fn a_constant_index_folds_with_its_sign() {
        let minus_one = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Constant(u32::MAX)),
            byte_width: 8,
        };
        assert_eq!(
            AffineOffset::of(&minus_one),
            Some(AffineOffset::constant(-8))
        );
    }

    #[test]
    fn a_chain_and_a_displacement_are_proved_without_a_walk() {
        let mut classes = EqualityGraph::default();
        assert!(classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(classes.add_equality(&at(symbolic(2), 0), &at(symbolic(3), 16)));
        assert!(classes.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 16)));
        assert!(classes.are_equal(&at(symbolic(1), 8), &at(symbolic(3), 24)));
        assert!(!classes.are_equal(&at(symbolic(1), 8), &at(symbolic(3), 8)));
        assert!(!classes.are_equal(&at(symbolic(1), 0), &at(symbolic(4), 0)));
    }

    fn at_offset(block: PointerBlock, offset: PointerOffsetTerm) -> Pointer {
        Pointer { block, offset }
    }

    #[test]
    fn same_block_pointer_query_uses_exact_offset_classes() {
        let left_offset = PointerOffsetTerm::Variable(Variable(11_001));
        let right_offset = PointerOffsetTerm::Variable(Variable(11_002));
        let base = symbolic(11_003);
        let left = at_offset(base.clone(), left_offset.clone());
        let right = at_offset(base.clone(), right_offset.clone());
        let other_block = at_offset(symbolic(11_004), right_offset.clone());
        let trunk = EqualityGraph::default();
        assert!(!trunk.are_equal(&left, &right));
        let mut branch = trunk.clone();
        branch.add_offset_equality(&left_offset, &right_offset);
        assert!(branch.are_equal(&left, &right));
        assert!(!trunk.are_equal(&left, &right));
        assert!(!branch.are_equal(&left, &other_block));
    }

    #[test]
    fn same_block_pointer_query_uses_scaled_int32_congruence() {
        let base = symbolic(11_010);
        let offset = |id| {
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(index(id), 4),
                PointerOffsetTerm::Constant(8),
            )
        };
        let left = at_offset(base.clone(), offset(11_011));
        let right = at_offset(base.clone(), offset(11_012));
        let wrong_width = at_offset(
            base.clone(),
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(index(11_012), 8),
                PointerOffsetTerm::Constant(8),
            ),
        );
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_equal(&left, &right));
        graph.add_int32_equality(&index(11_011), &index(11_012));
        assert!(graph.are_equal(&left, &right));
        assert!(!graph.are_equal(&left, &wrong_width));
        assert!(!graph.are_equal(&left, &at_offset(symbolic(11_013), offset(11_012))));
    }

    #[test]
    fn same_block_pointer_query_does_not_turn_wrapping_index_into_exact_offset() {
        let base = symbolic(11_014);
        let max = Bitvector32Term::Constant(i32::MAX as u32);
        let wrapped = at_offset(
            base.clone(),
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(max.clone(), Bitvector32Term::Constant(1)),
                4,
            ),
        );
        let exact_sum = at_offset(
            base,
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(max, 4),
                PointerOffsetTerm::Constant(4),
            ),
        );
        assert!(!EqualityGraph::default().are_equal(&wrapped, &exact_sum));
    }

    #[test]
    fn same_block_pointer_queries_scale_with_registered_offset_classes() {
        for size in [16u64, 64, 256, 1024] {
            let base = symbolic(11_020);
            let mut graph = EqualityGraph::default();
            for id in 0..size {
                graph.add_int32_equality(&index(id), &index(id + 1));
            }
            let first = at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(0), 4));
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for id in 1..=size {
                    let other =
                        at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(id), 4));
                    assert!(graph.are_equal(&first, &other));
                }
            });
            assert!(work < 200 * size as usize, "size={size}, work={work}");
        }
    }

    #[test]
    fn a_symbolic_displacement_carries_through_the_class() {
        let mut classes = EqualityGraph::default();
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 4,
            },
        };
        classes.add_equality(&at(symbolic(1), 0), &element);
        let next = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index(9)),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(4)),
            ),
        };
        assert!(classes.are_equal(&at(symbolic(1), 4), &next));
        assert!(!classes.are_equal(&at(symbolic(1), 4), &element));
    }

    #[test]
    fn an_equality_inside_one_class_records_nothing() {
        let mut classes = EqualityGraph::default();
        classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0));
        assert!(!classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 8)));
        assert!(classes.are_equal(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(!classes.are_equal(&at(symbolic(1), 0), &at(symbolic(2), 8)));
    }

    #[test]
    fn pointer_class_members_restate_a_pointer_in_every_member() {
        let mut classes = EqualityGraph::default();
        classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 8));
        classes.add_equality(&at(symbolic(3), 4), &at(symbolic(2), 0));
        let blocks = classes.pointer_class_members(&symbolic(1));
        assert_eq!(blocks.len(), 3);
        for (member, delta) in blocks {
            let restated = Pointer {
                block: member,
                offset: PointerOffsetTerm::Constant(
                    i64::try_from(delta.constant).expect("small constant"),
                ),
            };
            assert!(delta.terms.is_empty());
            assert!(classes.are_equal(&at(symbolic(1), 0), &restated));
        }
    }

    #[test]
    fn pointer_spellings_name_the_same_address_in_each_member() {
        let mut classes = EqualityGraph::default();
        assert!(classes.pointer_spellings(&at(symbolic(1), 4)).is_empty());
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 8,
            },
        };
        classes.add_equality(&at(symbolic(1), 0), &element);
        classes.add_equality(&at(symbolic(3), 16), &at(symbolic(1), 0));
        let spellings = classes.pointer_spellings(&at(symbolic(1), 4));
        assert_eq!(spellings.len(), 2);
        for spelling in &spellings {
            assert_ne!(spelling.block, symbolic(1));
            assert!(classes.are_equal(spelling, &at(symbolic(1), 4)));
        }
        assert!(spellings.contains(&at(symbolic(3), 20)));
    }

    #[test]
    fn loads_at_equal_pointers_of_one_snapshot_are_one_value() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block(symbolic(51), 16),
        );
        // A later snapshot where the cell `p` addresses was written.
        let other_memory = crate::kernel::intern_c_memory(memory.memory().clone().store(
            at(symbolic(41), 0),
            CValue::Int32(Bitvector32Term::Constant(7)),
        ));
        let name = |memory: &crate::kernel::SharedCMemory, address: Pointer| {
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory, &address, 8, memory,
            ))
        };
        let through_p = name(&memory, at(symbolic(41), 0));
        let through_q = name(&memory, at(symbolic(42), 0));
        let through_p_later = name(&other_memory, at(symbolic(41), 0));
        let through_r = name(&memory, at(symbolic(43), 0));
        let mut classes = EqualityGraph::default();
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        classes.add_equality(&at(symbolic(41), 0), &at(symbolic(42), 0));
        assert!(classes.are_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_q, 0)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_p_later, 8)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_r.clone(), 8)));
        // A loaded pointer an equality puts in a class brings the loads
        // congruent to it along.
        classes.add_equality(&at(through_r.clone(), 0), &at(symbolic(60), 0));
        let through_r_again = name(&memory, at(symbolic(43), 0));
        assert!(classes.are_equal(&at(through_r_again, 4), &at(symbolic(60), 4)));
    }

    #[test]
    fn congruent_loads_merge_their_existing_explicit_classes() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block(symbolic(101), 16),
        );
        let p = at(symbolic(102), 0);
        let q = at(symbolic(103), 0);
        let load = |address: &Pointer| {
            at(
                PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                    &memory, address, 8, &memory,
                )),
                0,
            )
        };
        let lp = load(&p);
        let lq = load(&q);
        let x = at(symbolic(104), 0);
        let y = at(symbolic(105), 0);
        let mut classes = EqualityGraph::default();
        classes.add_equality(&p, &q);
        assert!(classes.are_equal(&lp, &lq));
        classes.add_equality(&lp, &x);
        classes.add_equality(&lq, &y);
        assert!(classes.are_equal(&lp, &lq));
        assert!(classes.are_equal(&x, &y));
    }

    #[test]
    fn cross_snapshot_load_equality_requires_a_supplied_conclusion() {
        // The store goes through a pointer structure cannot separate from the
        // cell; only a stated disequality does. The two reads therefore get
        // different names, and only the path's facts make them one value.
        let cell = Pointer {
            block: PointerBlock::Heap(95_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = at(symbolic(95_003), 0);
        let before = crate::kernel::CMemory::new().with_block(PointerBlock::Heap(95_001), 16);
        let after = before
            .clone()
            .store(other.clone(), CValue::Int32(Bitvector32Term::Constant(3)));
        let name = |memory: &crate::kernel::CMemory| {
            let memory = crate::kernel::intern_c_memory(memory.clone());
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory, &cell, 8, &memory,
            ))
        };
        let (read_before, read_after) = (name(&before), name(&after));
        assert_ne!(read_before, read_after);
        let mut classes = EqualityGraph::default();
        let left = at(read_before, 8);
        let right = at(read_after, 8);
        // Pointer comparison never searches memory history, even when a
        // separate frame derivation could prove the cell unchanged.
        assert!(!classes.are_equal(&left, &right));
        let separated = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(other, cell.clone()), false);
        let load = |pointer: &Pointer| {
            let PointerBlock::Symbolic(variable) = &pointer.block else {
                unreachable!()
            };
            let (memory, address) =
                crate::kernel::registered_load_origin_for_variable(variable).unwrap();
            Bitvector32Term::MemoryLoad(memory, Box::new(address))
        };
        assert!(crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
            &load(&left), &load(&right), &separated,
        ));
        assert!(!classes.are_equal(&left, &right));
        // A checked caller can contribute that conclusion explicitly.
        classes.add_equality(&left, &right);
        assert!(classes.are_equal(&left, &right));
    }

    #[test]
    fn a_branch_extends_its_own_copy() {
        let mut trunk = EqualityGraph::default();
        trunk.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0));
        let mut branch = trunk.clone();
        branch.add_equality(&at(symbolic(2), 0), &at(symbolic(3), 0));
        assert!(branch.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
        assert!(!trunk.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
    }

    /// Load congruence for one query visits only the classed loads of the
    /// queried load's own snapshot: the work is the same beside 16 or 256
    /// classed loads read from other snapshots.
    #[test]
    fn load_congruence_work_ignores_classed_loads_of_other_snapshots() {
        let name = |memory: &crate::kernel::SharedCMemory, address: Pointer| {
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory, &address, 8, memory,
            ))
        };
        let mut costs = Vec::new();
        for unrelated in [16u64, 64, 256] {
            let mut classes = EqualityGraph::default();
            for index in 0..unrelated {
                let memory = crate::kernel::intern_c_memory(
                    crate::kernel::CMemory::new()
                        .with_block(symbolic(70_000 + index), 16)
                        .store(
                            at(symbolic(70_000 + index), 0),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        ),
                );
                let loaded = name(&memory, at(symbolic(70_000 + index), 0));
                classes.add_equality(&at(loaded, 0), &at(symbolic(80_000 + index), 0));
            }
            let memory = crate::kernel::intern_c_memory(
                crate::kernel::CMemory::new().with_block(symbolic(90_000), 16),
            );
            classes.add_equality(&at(symbolic(90_001), 0), &at(symbolic(90_002), 0));
            let left = name(&memory, at(symbolic(90_001), 0));
            let right = name(&memory, at(symbolic(90_002), 0));
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                classes.are_equal(&at(left.clone(), 8), &at(right.clone(), 8))
            });
            assert!(equal);
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    fn named_load(memory: &SharedCMemory, address: &Pointer) -> Pointer {
        at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory, address, 8, memory,
            )),
            0,
        )
    }

    #[test]
    fn load_congruence_is_independent_of_equality_insertion_order() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(201), 16));
        let p = at(symbolic(202), 0);
        let q = at(symbolic(203), 16);
        let lp = named_load(&memory, &at(p.block.clone(), 8));
        let lq = named_load(&memory, &at(q.block.clone(), 24));
        let x = at(symbolic(204), 0);
        let y = at(symbolic(205), 0);
        let equations = [
            (p, q),
            (at(lp.block.clone(), 4), x.clone()),
            (at(lq.block.clone(), 12), y.clone()),
        ];
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut classes = EqualityGraph::default();
            for index in order {
                classes.are_equal(&lp, &lq); // registration before and between merges
                classes.add_equality(&equations[index].0, &equations[index].1);
            }
            assert!(classes.are_equal(&lp, &lq), "{order:?}");
            assert!(classes.are_equal(&at(x.block.clone(), 8), &y), "{order:?}");
            assert!(!classes.are_equal(&x, &y), "different load displacements");
            classes.add_equality(&at(symbolic(206), 0), &at(symbolic(207), 0));
            assert!(
                classes.are_equal(&lp, &lq),
                "extra facts must preserve equality"
            );
        }
    }

    #[test]
    fn nested_load_congruence_propagates_a_late_merge_without_a_depth_cutoff() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(301), 16));
        let p = at(symbolic(302), 0);
        let q = at(symbolic(303), 0);
        let mut left = p.clone();
        let mut right = q.clone();
        for _ in 0..12 {
            left = named_load(&memory, &left);
            right = named_load(&memory, &right);
        }
        let mut classes = EqualityGraph::default();
        assert!(!classes.are_equal(&left, &right));
        classes.add_equality(&p, &q);
        assert!(classes.are_equal(&left, &right));
        // A newly named parent after closure must see the existing congruence.
        let later_left = named_load(&memory, &at(left.block, 8));
        let later_right = named_load(&memory, &at(right.block, 8));
        assert!(classes.are_equal(&later_left, &later_right));
    }

    #[test]
    fn congruence_registration_and_merges_are_isolated_between_branches() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(401), 16));
        let p = at(symbolic(402), 0);
        let q = at(symbolic(403), 0);
        let lp = named_load(&memory, &p);
        let lq = named_load(&memory, &q);
        let x = at(symbolic(404), 0);
        let y = at(symbolic(405), 0);
        let mut trunk = EqualityGraph::default();
        trunk.add_equality(&lp, &x);
        trunk.add_equality(&lq, &y);
        let sibling = trunk.clone();
        let mut branch = trunk.clone();
        branch.add_equality(&p, &q);
        assert!(branch.are_equal(&x, &y));
        assert!(!trunk.are_equal(&x, &y));
        assert!(!sibling.are_equal(&x, &y));
        assert!(!EqualityGraph::default().are_equal(&lp, &lq));
    }

    #[test]
    fn same_snapshot_load_queries_ignore_unrelated_applications() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(501), 16));
        let p = at(symbolic(502), 0);
        let q = at(symbolic(503), 0);
        let left = named_load(&memory, &p);
        let right = named_load(&memory, &q);
        let mut costs = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut classes = EqualityGraph::default();
            for i in 0..size {
                let load = named_load(&memory, &at(symbolic(100_000 + i), 0));
                classes.add_equality(&load, &at(symbolic(200_000 + i), 0));
            }
            classes.add_equality(&p, &q);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                classes.are_equal(&left, &right)
            });
            assert!(equal);
            costs.push(work);
            let (equal, map_work) =
                crate::persistent::measure_persistent_work(|| classes.are_equal(&left, &right));
            assert!(equal);
            assert!(
                map_work < 32 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    #[test]
    fn late_merges_and_repeated_queries_have_near_linear_total_work() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(601), 16));
        for size in [16u64, 64, 256, 1024] {
            let left = at(symbolic(602), 0);
            let right = at(symbolic(603), 0);
            let mut classes = EqualityGraph::default();
            let mut pairs = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let a = named_load(&memory, &at(left.block.clone(), i as i64 * 8));
                    let b = named_load(&memory, &at(right.block.clone(), i as i64 * 8));
                    assert!(!classes.are_equal(&a, &b));
                    pairs.push((a, b));
                }
                classes.add_equality(&left, &right);
                for (a, b) in &pairs {
                    assert!(classes.are_equal(a, b));
                }
            });
            assert!(
                work <= 128 * size as usize,
                "size={size}, total work={work}"
            );
        }
    }

    #[test]
    fn branch_merges_do_not_reindex_the_large_shared_prefix() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(701), 16));
        let root = at(symbolic(702), 0);
        let mut costs = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut trunk = EqualityGraph::default();
            for i in 0..size {
                let load = named_load(&memory, &at(root.block.clone(), i as i64 * 8));
                trunk.add_equality(&load, &at(symbolic(300_000 + i), 0));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..16 {
                    let mut branch = trunk.clone();
                    let alias = at(symbolic(400_000 + i), 0);
                    branch.add_equality(&root, &alias);
                    assert!(branch.are_equal(&root, &alias));
                }
            });
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    #[test]
    fn restricted_context_and_fact_withdrawal_drop_derived_load_equalities() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(801), 16));
        let p = at(symbolic(802), 0);
        let q = at(symbolic(803), 0);
        let x = at(symbolic(804), 0);
        let y = at(symbolic(805), 0);
        let lp = named_load(&memory, &p);
        let lq = named_load(&memory, &q);
        let address = ConditionTerm::pointer_equal(p, q);
        let selected = [
            (ConditionTerm::pointer_equal(lp, x.clone()), true),
            (ConditionTerm::pointer_equal(lq, y.clone()), true),
        ];
        let mut context = PureFactContext::new().assume_condition(address.clone(), true);
        for (condition, value) in &selected {
            context = context.assume_condition(condition.clone(), *value);
        }
        assert!(context.has_indexed_pointer_equality_path(&x, &y));
        let restricted = context.restricted_to_facts(&selected, &[]);
        assert!(!restricted.has_indexed_pointer_equality_path(&x, &y));
        let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(address, true));
        assert!(!withdrawn.has_indexed_pointer_equality_path(&x, &y));
        assert!(context.has_indexed_pointer_equality_path(&x, &y));
    }

    #[test]
    fn separation_equality_query_uses_offset_classes_without_walking_aliases() {
        for size in [16u64, 64, 256, 1024] {
            let offset = |i| PointerOffsetTerm::Variable(Variable(500_000 + i));
            let mut context = PureFactContext::new();
            for i in 0..size {
                context = context.assume_condition(
                    ConditionTerm::pointer_offset_equal(offset(i), offset(i + 1)),
                    true,
                );
            }
            let left = at_offset(symbolic(499_999), offset(0));
            let right = at_offset(symbolic(499_999), offset(size));
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.pointers_proven_equal_ignoring_memory_separation(&left, &right)
            });
            assert!(equal);
            assert!(work < 64, "size={size}, work={work}");
        }
    }

    #[test]
    fn a_small_load_is_not_a_pointer_load_and_can_later_be_registered_as_one() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(901), 16));
        let p = at(symbolic(902), 0);
        let q = at(symbolic(903), 0);
        let small = at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory, &p, 4, &memory,
            )),
            0,
        );
        let pointer = named_load(&memory, &q);
        let mut classes = EqualityGraph::default();
        classes.add_equality(&p, &q);
        assert!(!classes.are_equal(&small, &pointer));
        let widened = named_load(&memory, &p);
        assert_eq!(small, widened);
        assert!(classes.are_equal(&widened, &pointer));
    }

    #[test]
    fn affine_spelling_order_does_not_depend_on_atom_interning_order() {
        let high = PointerOffsetTerm::Int32Scaled {
            value: Box::new(index(987_002)),
            byte_width: 4,
        };
        let low = PointerOffsetTerm::Int32Scaled {
            value: Box::new(index(987_001)),
            byte_width: 4,
        };
        let high_form = AffineOffset::of(&high).unwrap();
        let low_form = AffineOffset::of(&low).unwrap();
        let sum = high_form.checked_add(&low_form).unwrap();
        assert_eq!(
            sum.to_offset_term(),
            Some(PointerOffsetTerm::add(
                PointerOffsetTerm::add(PointerOffsetTerm::Constant(0), low),
                high,
            ))
        );
    }

    #[test]
    fn affine_input_normalization_is_linear_in_its_explicit_syntax() {
        for size in [16u64, 64, 256, 1024] {
            let mut input = PointerOffsetTerm::Constant(0);
            for i in 0..size {
                input = PointerOffsetTerm::Add(
                    Box::new(input),
                    Box::new(PointerOffsetTerm::Variable(Variable(900_000 + i))),
                );
            }
            let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
                AffineOffset::of(&input).unwrap()
            });
            assert_eq!(form.terms.len(), size as usize);
            assert_eq!(work, 2 * size as usize + 1);
        }
    }

    /// Relabelling work along a chain of `n` equalities is `O(n log n)`:
    /// union by size moves each block at most `log2 n` times. Joining two
    /// balanced halves repeatedly is the worst case for relabelling.
    #[test]
    fn relabelling_work_is_n_log_n_across_sizes() {
        for exponent in [6u32, 8, 10, 12] {
            let n = 1u64 << exponent;
            let (classes, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut classes = EqualityGraph::default();
                let mut width = 1;
                while width < n {
                    let mut start = 0;
                    while start + width < n {
                        classes
                            .add_equality(&at(symbolic(start), 0), &at(symbolic(start + width), 0));
                        start += 2 * width;
                    }
                    width *= 2;
                }
                classes
            });
            assert!(classes.are_equal(&at(symbolic(0), 0), &at(symbolic(n - 1), 0)));
            let bound = 16 * n * u64::from(exponent);
            assert!(
                work as u64 <= bound,
                "n = {n}: relabelled {work} blocks, above 16 n log2 n = {bound}"
            );
            // Balanced joins move a whole class each time, so the charge for
            // the moved members beyond the first is visible, not constant.
            assert!(work as u64 >= n / 2, "n = {n}: only {work} units charged");
        }
    }
}
