//! Equality classes of pointers, as a persistent union-find with offsets.
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
//! the smaller class, so a member's lookup is one map access and the total
//! relabelling along one path is `O(n log n)` in the blocks it merges. An
//! equality between two blocks already in one class adds nothing here: it
//! relates offsets, not bases, and stays with the offset facts.

use super::*;

/// One atom of an affine offset: a quantity the normal form does not
/// decompose, with the numeric reading the offset term gives it.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) enum OffsetAtom {
    /// A 64-bit offset variable.
    Variable(Variable),
    /// A 32-bit index, sign-extended.
    Int32(Bitvector32Term),
    /// A 64-bit index, signed or unsigned.
    Int64 {
        value: Bitvector32Term,
        unsigned: bool,
    },
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

    fn atom(atom: OffsetAtom, coefficient: i128) -> Self {
        let mut terms = std::collections::BTreeMap::new();
        if coefficient != 0 {
            terms.insert(atom, coefficient);
        }
        Self { constant: 0, terms }
    }

    /// The normal form of an offset term, or `None` when its arithmetic
    /// overflows the exact form.
    pub(in crate::kernel) fn of(offset: &PointerOffsetTerm) -> Option<Self> {
        match offset {
            PointerOffsetTerm::Constant(value) => Some(Self::constant(i128::from(*value))),
            PointerOffsetTerm::Variable(variable) => {
                Some(Self::atom(OffsetAtom::Variable(*variable), 1))
            }
            PointerOffsetTerm::Add(left, right) => Self::of(left)?.checked_add(&Self::of(right)?),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                let width = i128::from(*byte_width);
                match value.as_const() {
                    Some(value) => {
                        Some(Self::constant(i128::from(value as i32).checked_mul(width)?))
                    }
                    None => Some(Self::atom(
                        OffsetAtom::Int32(crate::kernel::canonical_term(value)),
                        width,
                    )),
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
                match constant {
                    Some(value) => Some(Self::constant(value.checked_mul(width)?)),
                    None => Some(Self::atom(
                        OffsetAtom::Int64 {
                            value: crate::kernel::canonical_term(value),
                            unsigned: *unsigned,
                        },
                        width,
                    )),
                }
            }
        }
    }

    pub(in crate::kernel) fn checked_add(&self, other: &Self) -> Option<Self> {
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
        for (atom, coefficient) in &self.terms {
            let coefficient = i64::try_from(*coefficient).ok()?;
            let addend = match atom {
                OffsetAtom::Variable(variable) if coefficient == 1 => {
                    PointerOffsetTerm::Variable(*variable)
                }
                OffsetAtom::Variable(_) => return None,
                OffsetAtom::Int32(value) => PointerOffsetTerm::Int32Scaled {
                    value: Box::new(value.clone()),
                    byte_width: coefficient,
                },
                OffsetAtom::Int64 { value, unsigned } => PointerOffsetTerm::Int64Scaled {
                    value: Box::new(value.clone()),
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

/// A pointer's normal form under the recorded equalities and load
/// congruence: its base is either a class representative, or, for a loaded
/// pointer no equality places in a class, the load it is the value of,
/// itself in normal form. Two pointers with one normal form are equal.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) struct NormalPointer {
    base: NormalBase,
    offset: AffineOffset,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum NormalBase {
    Class(PointerBlock),
    Load(SharedCMemory, Box<NormalPointer>),
}

thread_local! {
    /// Pairs of loaded pointers whose cross-snapshot equality is being
    /// decided on this thread.
    static FRAME_PAIRS_IN_PROGRESS: std::cell::RefCell<std::collections::BTreeSet<(Variable, Variable)>> =
        const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
}

/// How many nested loads a normal form looks through.
const LOAD_CONGRUENCE_DEPTH: usize = 4;

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct PointerClasses {
    /// For every block that is not its class's representative: the
    /// representative and `delta` with `base(block) = base(rep) + delta`.
    parent: crate::persistent::PersistentMap<PointerBlock, (PointerBlock, AffineOffset)>,
    /// For every representative with at least one other member: those
    /// members and their deltas.
    members: crate::persistent::PersistentMap<
        PointerBlock,
        crate::persistent::PersistentMap<PointerBlock, AffineOffset>,
    >,
    /// The classed blocks that are loaded pointers, by the snapshot their
    /// load read. Load congruence consults only the loads of the queried
    /// load's own snapshot. Blocks never leave a class, so this only grows.
    classed_loads: crate::persistent::PersistentMap<
        SharedCMemory,
        crate::persistent::PersistentSet<PointerBlock>,
    >,
}

impl PointerClasses {
    /// The representative of `block`'s class and `block`'s base relative to
    /// it. One map access: a union relabels every member it moves.
    pub(in crate::kernel) fn find(&self, block: &PointerBlock) -> (PointerBlock, AffineOffset) {
        match self.parent.get(block) {
            Some((representative, delta)) => (representative.clone(), delta.clone()),
            None => (block.clone(), AffineOffset::default()),
        }
    }

    /// The class-relative form of `pointer`, or `None` when its offset has no
    /// exact normal form.
    pub(in crate::kernel) fn canonical(&self, pointer: &Pointer) -> Option<CanonicalPointer> {
        let offset = AffineOffset::of(&pointer.offset)?;
        let (representative, delta) = self.find(&pointer.block);
        Some(CanonicalPointer {
            representative,
            offset: delta.checked_add(&offset)?,
        })
    }

    /// Whether the recorded equalities, with load congruence, prove the two
    /// pointers equal.
    pub(in crate::kernel) fn proves_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        if left == right {
            return true;
        }
        if let (Some(left), Some(right)) = (self.canonical(left), self.canonical(right))
            && left == right
        {
            return true;
        }
        match (
            self.normal(left, LOAD_CONGRUENCE_DEPTH),
            self.normal(right, LOAD_CONGRUENCE_DEPTH),
        ) {
            (Some(left), Some(right)) => left == right,
            _ => false,
        }
    }

    /// `proves_equal`, and also: two loaded pointers that read the same
    /// address at two snapshots are equal when the path's facts prove the
    /// cell unchanged between them. That question goes to the kernel's
    /// cross-snapshot load equality once per compared pair; it is never
    /// asked of loads nobody compares.
    pub(in crate::kernel) fn proves_equal_in(
        &self,
        left: &Pointer,
        right: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.proves_equal(left, right) {
            return true;
        }
        let (Some(left_normal), Some(right_normal)) = (
            self.normal(left, LOAD_CONGRUENCE_DEPTH),
            self.normal(right, LOAD_CONGRUENCE_DEPTH),
        ) else {
            return false;
        };
        let (
            NormalBase::Load(left_memory, left_address),
            NormalBase::Load(right_memory, right_address),
        ) = (&left_normal.base, &right_normal.base)
        else {
            return false;
        };
        if left_normal.offset != right_normal.offset
            || left_memory == right_memory
            || left_address != right_address
        {
            return false;
        }
        let (PointerBlock::Symbolic(left_variable), PointerBlock::Symbolic(right_variable)) =
            (&left.block, &right.block)
        else {
            return false;
        };
        let pair = if left_variable <= right_variable {
            (*left_variable, *right_variable)
        } else {
            (*right_variable, *left_variable)
        };
        // Frame reasoning may itself ask pointer questions; a pair already
        // being decided answers no rather than recursing.
        if !FRAME_PAIRS_IN_PROGRESS.with(|active| active.borrow_mut().insert(pair)) {
            return false;
        }
        crate::instrumentation::record_deterministic_work(1);
        let load = |variable: &Variable| {
            let (memory, address) = crate::kernel::registered_load_origin_for_variable(variable)
                .or_else(|| crate::kernel::registered_load_for_variable(variable))?;
            Some(Bitvector32Term::MemoryLoad(memory, Box::new(address)))
        };
        let equal = match (load(left_variable), load(right_variable)) {
            (Some(left_load), Some(right_load)) => {
                crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
                    &left_load,
                    &right_load,
                    assumptions,
                )
            }
            _ => false,
        };
        FRAME_PAIRS_IN_PROGRESS.with(|active| active.borrow_mut().remove(&pair));
        equal
    }

    /// The load a block is the identity of, when it is a loaded pointer's.
    fn loaded_block_load(block: &PointerBlock) -> Option<(SharedCMemory, Pointer)> {
        let PointerBlock::Symbolic(variable) = block else {
            return None;
        };
        if !crate::kernel::is_load_variable(variable) {
            return None;
        }
        crate::kernel::registered_load_for_variable(variable)
    }

    /// A pointer's normal form. A loaded pointer outside every class is the
    /// load it names: two loads of one snapshot at pointers with one normal
    /// form are one value (load congruence). When such a load is also the
    /// load a classed loaded pointer names, the pointer joins that class.
    pub(in crate::kernel) fn normal(
        &self,
        pointer: &Pointer,
        depth: usize,
    ) -> Option<NormalPointer> {
        let offset = AffineOffset::of(&pointer.offset)?;
        let (representative, delta) = self.find(&pointer.block);
        let class_form = |representative: PointerBlock, delta: AffineOffset| {
            Some(NormalPointer {
                base: NormalBase::Class(representative),
                offset: delta.checked_add(&offset)?,
            })
        };
        if depth == 0 || self.is_classed(&pointer.block) {
            return class_form(representative, delta);
        }
        let Some((memory, address)) = Self::loaded_block_load(&pointer.block) else {
            return class_form(representative, delta);
        };
        let Some(address) = self.normal(&address, depth - 1) else {
            return class_form(representative, delta);
        };
        crate::instrumentation::record_deterministic_work(1);
        let key = (memory, address);
        // A classed loaded pointer naming the same load puts this one in its
        // class. Only the classed loads of this snapshot are candidates.
        if let Some(candidates) = self.classed_loads.get(&key.0) {
            for member in candidates.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some((_, member_address)) = Self::loaded_block_load(member)
                    && self.normal(&member_address, depth - 1).as_ref() == Some(&key.1)
                {
                    let (member_representative, member_delta) = self.find(member);
                    return class_form(member_representative, member_delta);
                }
            }
        }
        Some(NormalPointer {
            base: NormalBase::Load(key.0, Box::new(key.1)),
            offset,
        })
    }

    fn class_size(&self, representative: &PointerBlock) -> usize {
        self.members
            .get(representative)
            .map_or(1, |members| members.len() + 1)
    }

    /// Every block in `block`'s class, including `block` itself, with the
    /// delta `d` such that `base(block) = base(member) + d`. A pointer
    /// `block + o` is therefore the pointer `member + (o + d)`. The work is
    /// the class's size.
    pub(in crate::kernel) fn class_blocks(
        &self,
        block: &PointerBlock,
    ) -> Vec<(PointerBlock, AffineOffset)> {
        let (representative, own) = self.find(block);
        let mut blocks = Vec::with_capacity(self.class_size(&representative));
        let mut push = |member: &PointerBlock, member_delta: &AffineOffset| {
            if let Some(delta) = own.checked_sub(member_delta) {
                blocks.push((member.clone(), delta));
            }
        };
        push(&representative, &AffineOffset::default());
        if let Some(members) = self.members.get(&representative) {
            for (member, delta) in members.iter() {
                push(member, delta);
            }
        }
        blocks
    }

    /// Whether `block` shares its class with another block. One lookup, so a
    /// caller decides whether an alias retry is possible before paying for
    /// the class.
    pub(in crate::kernel) fn is_classed(&self, block: &PointerBlock) -> bool {
        self.parent.contains_key(block) || self.members.contains_key(block)
    }

    /// `pointer` restated at every other block of its class, in class order.
    /// Empty when the block is alone in its class, so a caller that retries a
    /// lookup under these spellings pays nothing on the common path.
    pub(in crate::kernel) fn other_spellings(&self, pointer: &Pointer) -> Vec<Pointer> {
        if !self.parent.contains_key(&pointer.block) && !self.members.contains_key(&pointer.block) {
            return Vec::new();
        }
        self.class_blocks(&pointer.block)
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

    /// Records a true pointer equality. Returns whether two classes merged;
    /// an equality inside one class, or over an offset with no exact normal
    /// form, records nothing.
    pub(in crate::kernel) fn assume_equal(&mut self, left: &Pointer, right: &Pointer) -> bool {
        let (Some(left), Some(right)) = (self.canonical(left), self.canonical(right)) else {
            return false;
        };
        if left.representative == right.representative {
            return false;
        }
        // base(left.rep) + left.offset = base(right.rep) + right.offset, so
        // base(left.rep) = base(right.rep) + (right.offset - left.offset).
        let Some(left_from_right) = right.offset.checked_sub(&left.offset) else {
            return false;
        };
        let (moved, kept, moved_from_kept) =
            if self.class_size(&left.representative) <= self.class_size(&right.representative) {
                (left.representative, right.representative, left_from_right)
            } else {
                let Some(right_from_left) = left_from_right.checked_negate() else {
                    return false;
                };
                (right.representative, left.representative, right_from_left)
            };
        self.relabel(moved, kept, moved_from_kept)
    }

    /// Moves every member of `moved`'s class under `kept`, where
    /// `base(moved) = base(kept) + moved_from_kept`.
    fn relabel(
        &mut self,
        moved: PointerBlock,
        kept: PointerBlock,
        moved_from_kept: AffineOffset,
    ) -> bool {
        let mut relabelled = vec![(moved.clone(), AffineOffset::default())];
        if let Some(members) = self.members.get(&moved) {
            relabelled.extend(
                members
                    .iter()
                    .map(|(member, delta)| (member.clone(), delta.clone())),
            );
        }
        let mut deltas = Vec::with_capacity(relabelled.len());
        for (member, delta) in &relabelled {
            // base(member) = base(moved) + delta = base(kept) + delta + moved_from_kept.
            let Some(delta) = delta.checked_add(&moved_from_kept) else {
                return false;
            };
            deltas.push((member.clone(), delta));
        }
        // Moving one block is constant bookkeeping, like filing the fact in
        // any other index; what grows is the rest of a moved class, and that
        // is what union by size keeps to `log2 n` moves per block.
        crate::instrumentation::record_deterministic_work(deltas.len() - 1);
        for block in std::iter::once(&kept).chain(deltas.iter().map(|(member, _)| member)) {
            if let Some((memory, _)) = Self::loaded_block_load(block) {
                let loads = self.classed_loads.get(&memory).cloned().unwrap_or_default();
                if !loads.contains(block) {
                    self.classed_loads
                        .insert(memory, loads.with_value(block.clone()));
                }
            }
        }
        let mut kept_members = self.members.get(&kept).cloned().unwrap_or_default();
        for (member, delta) in deltas {
            self.parent
                .insert(member.clone(), (kept.clone(), delta.clone()));
            kept_members.insert(member, delta);
        }
        self.members.remove(&moved);
        self.members.insert(kept, kept_members);
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
        let mut classes = PointerClasses::default();
        assert!(classes.assume_equal(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(classes.assume_equal(&at(symbolic(2), 0), &at(symbolic(3), 16)));
        assert!(classes.proves_equal(&at(symbolic(1), 0), &at(symbolic(3), 16)));
        assert!(classes.proves_equal(&at(symbolic(1), 8), &at(symbolic(3), 24)));
        assert!(!classes.proves_equal(&at(symbolic(1), 8), &at(symbolic(3), 8)));
        assert!(!classes.proves_equal(&at(symbolic(1), 0), &at(symbolic(4), 0)));
    }

    #[test]
    fn a_symbolic_displacement_carries_through_the_class() {
        let mut classes = PointerClasses::default();
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 4,
            },
        };
        classes.assume_equal(&at(symbolic(1), 0), &element);
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
        assert!(classes.proves_equal(&at(symbolic(1), 4), &next));
        assert!(!classes.proves_equal(&at(symbolic(1), 4), &element));
    }

    #[test]
    fn an_equality_inside_one_class_records_nothing() {
        let mut classes = PointerClasses::default();
        classes.assume_equal(&at(symbolic(1), 0), &at(symbolic(2), 0));
        assert!(!classes.assume_equal(&at(symbolic(1), 0), &at(symbolic(2), 8)));
        assert!(classes.proves_equal(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(!classes.proves_equal(&at(symbolic(1), 0), &at(symbolic(2), 8)));
    }

    #[test]
    fn class_blocks_restate_a_pointer_in_every_member() {
        let mut classes = PointerClasses::default();
        classes.assume_equal(&at(symbolic(1), 0), &at(symbolic(2), 8));
        classes.assume_equal(&at(symbolic(3), 4), &at(symbolic(2), 0));
        let blocks = classes.class_blocks(&symbolic(1));
        assert_eq!(blocks.len(), 3);
        for (member, delta) in blocks {
            let restated = Pointer {
                block: member,
                offset: PointerOffsetTerm::Constant(
                    i64::try_from(delta.constant).expect("small constant"),
                ),
            };
            assert!(delta.terms.is_empty());
            assert!(classes.proves_equal(&at(symbolic(1), 0), &restated));
        }
    }

    #[test]
    fn other_spellings_name_the_same_address_in_each_member() {
        let mut classes = PointerClasses::default();
        assert!(classes.other_spellings(&at(symbolic(1), 4)).is_empty());
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 8,
            },
        };
        classes.assume_equal(&at(symbolic(1), 0), &element);
        classes.assume_equal(&at(symbolic(3), 16), &at(symbolic(1), 0));
        let spellings = classes.other_spellings(&at(symbolic(1), 4));
        assert_eq!(spellings.len(), 2);
        for spelling in &spellings {
            assert_ne!(spelling.block, symbolic(1));
            assert!(classes.proves_equal(spelling, &at(symbolic(1), 4)));
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
        let mut classes = PointerClasses::default();
        assert!(!classes.proves_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        classes.assume_equal(&at(symbolic(41), 0), &at(symbolic(42), 0));
        assert!(classes.proves_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        assert!(!classes.proves_equal(&at(through_p.clone(), 8), &at(through_q, 0)));
        assert!(!classes.proves_equal(&at(through_p.clone(), 8), &at(through_p_later, 8)));
        assert!(!classes.proves_equal(&at(through_p.clone(), 8), &at(through_r.clone(), 8)));
        // A loaded pointer an equality puts in a class brings the loads
        // congruent to it along.
        classes.assume_equal(&at(through_r.clone(), 0), &at(symbolic(60), 0));
        let through_r_again = name(&memory, at(symbolic(43), 0));
        assert!(classes.proves_equal(&at(through_r_again, 4), &at(symbolic(60), 4)));
    }

    #[test]
    fn one_stored_pointer_read_across_an_unrelated_store_is_one_value() {
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
        let classes = PointerClasses::default();
        let separated = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(other, cell.clone()), false);
        assert!(classes.proves_equal_in(
            &at(read_before.clone(), 8),
            &at(read_after.clone(), 8),
            &separated
        ));
        assert!(!classes.proves_equal_in(
            &at(read_before, 8),
            &at(read_after, 8),
            &PureFactContext::new()
        ));
    }

    #[test]
    fn a_branch_extends_its_own_copy() {
        let mut trunk = PointerClasses::default();
        trunk.assume_equal(&at(symbolic(1), 0), &at(symbolic(2), 0));
        let mut branch = trunk.clone();
        branch.assume_equal(&at(symbolic(2), 0), &at(symbolic(3), 0));
        assert!(branch.proves_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
        assert!(!trunk.proves_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
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
            let mut classes = PointerClasses::default();
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
                classes.assume_equal(&at(loaded, 0), &at(symbolic(80_000 + index), 0));
            }
            let memory = crate::kernel::intern_c_memory(
                crate::kernel::CMemory::new().with_block(symbolic(90_000), 16),
            );
            classes.assume_equal(&at(symbolic(90_001), 0), &at(symbolic(90_002), 0));
            let left = name(&memory, at(symbolic(90_001), 0));
            let right = name(&memory, at(symbolic(90_002), 0));
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                classes.proves_equal(&at(left.clone(), 8), &at(right.clone(), 8))
            });
            assert!(equal);
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    /// Relabelling work along a chain of `n` equalities is `O(n log n)`:
    /// union by size moves each block at most `log2 n` times. Joining two
    /// balanced halves repeatedly is the worst case for relabelling.
    #[test]
    fn relabelling_work_is_n_log_n_across_sizes() {
        for exponent in [6u32, 8, 10, 12] {
            let n = 1u64 << exponent;
            let (classes, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut classes = PointerClasses::default();
                let mut width = 1;
                while width < n {
                    let mut start = 0;
                    while start + width < n {
                        classes
                            .assume_equal(&at(symbolic(start), 0), &at(symbolic(start + width), 0));
                        start += 2 * width;
                    }
                    width *= 2;
                }
                classes
            });
            assert!(classes.proves_equal(&at(symbolic(0), 0), &at(symbolic(n - 1), 0)));
            let bound = n * u64::from(exponent);
            assert!(
                work as u64 <= bound,
                "n = {n}: relabelled {work} blocks, above n log2 n = {bound}"
            );
            // Balanced joins move a whole class each time, so the charge for
            // the moved members beyond the first is visible, not constant.
            assert!(work as u64 >= n / 2, "n = {n}: only {work} units charged");
        }
    }
}
