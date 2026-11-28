//! [`AddressOffset`]: a shared offset handle compared by its written syntax.
//!
//! Offset handles are interned by their exact node, so two handles can differ
//! only in an annotation of a retained index (a producer slot, an object
//! class) yet describe the same written offset. Addresses, conditions and
//! offset keys compare offsets by written syntax instead: the tree shape,
//! constants, variables, byte widths and interpretations, and each index by
//! its numeric identity ([`SharedMachineIntegerTerm`]'s id). [`AddressOffset`]
//! is that view of a handle. Its equality, hash and order are those of the
//! deleted native offset tree it replaced, and it reads its nodes through
//! [`OffsetTree`], so readers do not depend on which representation they hold.
//!
//! Each handle keeps the index carrier it was built from (or, for a node
//! rebuilt from kernel terms, the one explicit output names), so the index
//! identity an offset reports never changes while the offset is alive. A
//! syntax fingerprint and the folded constant are cached per node: equality
//! is O(1) unless two distinct handles have one fingerprint, and comparing
//! walks only the part two offsets do not share. `Hash` deliberately keeps
//! the deleted native tree's hash values (see its impl).
use super::*;
use std::cmp::Ordering;

#[cfg(test)]
thread_local! {
    /// Nodes the fingerprint and order walks visit. They charge no work, as
    /// the native tree's derived traits charged none, so tests count here.
    pub(super) static WRITTEN_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn visit() {
    WRITTEN_VISITS.with(|visits| visits.set(visits.get() + 1));
}
#[cfg(not(test))]
fn visit() {}

impl SharedAddressOffset {
    /// The index carrier of a scaled node, as written: the carrier this node
    /// was built from, or, for a node built from kernel terms, the one
    /// explicit output names ([`KernelAddressOffset::index_key`]).
    fn written_index(&self) -> Result<&SharedMachineIntegerTerm, &'static str> {
        let value = self.node().index().ok_or("offset node has no index")?;
        // The native tree read its index for free; so does this.
        self.0
            .index
            .get_or_init(|| {
                crate::instrumentation::without_charging(|| KernelAddressOffset::index_key(value))
            })
            .as_ref()
            .map_err(|error| *error)
    }

    /// The written syntax fingerprint, for equality's fast path. Each node
    /// hashes once, from its children's cached fingerprints, so a deep tree
    /// is visited only on its first request.
    fn written_hash(&self) -> Result<u64, &'static str> {
        if let Some(hash) = self.0.syntax_hash.get() {
            return *hash;
        }
        let mut pending = vec![(self, false)];
        while let Some((root, ready)) = pending.pop() {
            if root.0.syntax_hash.get().is_some() {
                continue;
            }
            if let KernelAddressOffset::Add([left, right]) = root.node()
                && !ready
            {
                pending.extend([(root, true), (right, false), (left, false)]);
                continue;
            }
            visit();
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            let hash = match root.node() {
                KernelAddressOffset::Constant(value) => {
                    (0u8, value).hash(&mut hasher);
                    Ok(hasher.finish())
                }
                KernelAddressOffset::Variable(variable) => {
                    (1u8, variable).hash(&mut hasher);
                    Ok(hasher.finish())
                }
                KernelAddressOffset::Add([left, right]) => {
                    let left = *left.0.syntax_hash.get().expect("left hashed first");
                    let right = *right.0.syntax_hash.get().expect("right hashed first");
                    left.and_then(|left| {
                        (2u8, left, right?).hash(&mut hasher);
                        Ok(hasher.finish())
                    })
                }
                KernelAddressOffset::Int32Scaled { byte_width, .. } => {
                    root.written_index().map(|index| {
                        (3u8, index.id(), byte_width).hash(&mut hasher);
                        hasher.finish()
                    })
                }
                KernelAddressOffset::Int64Scaled {
                    byte_width,
                    unsigned,
                    ..
                } => root.written_index().map(|index| {
                    (4u8, index.id(), byte_width, unsigned).hash(&mut hasher);
                    hasher.finish()
                }),
            };
            let _ = root.0.syntax_hash.set(hash);
        }
        *self.0.syntax_hash.get().expect("hashed root")
    }

    /// The written structural order: by variant (constant, variable, sum,
    /// 32-bit and 64-bit scaled index), then constants by value, variables by
    /// identity, a sum by its left then its right operand, and a scaled index
    /// by its written index identity, byte width and interpretation. It stops
    /// at the first ordered pair and skips shared subtrees.
    fn written_cmp(&self, other: &Self) -> Ordering {
        fn rank(node: &KernelAddressOffset) -> u8 {
            match node {
                KernelAddressOffset::Constant(_) => 0,
                KernelAddressOffset::Variable(_) => 1,
                KernelAddressOffset::Add(_) => 2,
                KernelAddressOffset::Int32Scaled { .. } => 3,
                KernelAddressOffset::Int64Scaled { .. } => 4,
            }
        }
        let index = |root: &Self| root.written_index().expect("written offset").id();
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left == right {
                continue;
            }
            visit();
            let order = match (left.node(), right.node()) {
                (KernelAddressOffset::Constant(a), KernelAddressOffset::Constant(b)) => a.cmp(b),
                (KernelAddressOffset::Variable(a), KernelAddressOffset::Variable(b)) => a.cmp(b),
                (KernelAddressOffset::Add([a, b]), KernelAddressOffset::Add([c, d])) => {
                    // Left operand first: pop order is the reverse of push order.
                    pending.push((b, d));
                    pending.push((a, c));
                    Ordering::Equal
                }
                (
                    KernelAddressOffset::Int32Scaled { byte_width: w, .. },
                    KernelAddressOffset::Int32Scaled { byte_width: x, .. },
                ) => index(left).cmp(&index(right)).then(w.cmp(x)),
                (
                    KernelAddressOffset::Int64Scaled {
                        byte_width: w,
                        unsigned: u,
                        ..
                    },
                    KernelAddressOffset::Int64Scaled {
                        byte_width: x,
                        unsigned: v,
                        ..
                    },
                ) => index(left).cmp(&index(right)).then(w.cmp(x)).then(u.cmp(v)),
                (a, b) => rank(a).cmp(&rank(b)),
            };
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    /// The constant byte displacement the written offset folds to, read as
    /// the native offset tree read it: a sum of constants, or a scaled index
    /// whose written carrier is a constant. Cached per node.
    pub(in crate::kernel::primitives) fn written_constant(&self) -> Option<i64> {
        *self.0.syntax_constant.get_or_init(|| match self.node() {
            KernelAddressOffset::Constant(value) => Some(*value),
            KernelAddressOffset::Variable(_) => None,
            KernelAddressOffset::Add([left, right]) => left
                .written_constant()?
                .checked_add(right.written_constant()?),
            KernelAddressOffset::Int32Scaled { byte_width, .. } => {
                let index = self.written_index().ok()?;
                let value = index.operand_view().word32_constant()? as i32 as i64;
                value.checked_mul(*byte_width)
            }
            KernelAddressOffset::Int64Scaled {
                byte_width,
                unsigned,
                ..
            } => {
                let index = self.written_index().ok()?;
                let value = if *unsigned {
                    i64::try_from(index.operand_view().uint64_constant()?).ok()?
                } else {
                    index.operand_view().int64_constant()?
                };
                value.checked_mul(*byte_width)
            }
        })
    }
}

/// An offset handle compared by its written syntax (module documentation).
#[repr(transparent)]
#[derive(Clone)]
pub struct AddressOffset(SharedAddressOffset);

impl AddressOffset {
    /// A constant byte displacement ([`OffsetTree::constant`]), for callers
    /// outside the crate, which cannot name the trait.
    pub fn constant(value: i64) -> Self {
        <Self as OffsetTree>::constant(value)
    }

    /// The written view of a handle, or why one of its indices has no
    /// explicit output.
    pub(crate) fn try_from_shared(root: SharedAddressOffset) -> Result<Self, &'static str> {
        root.written_hash()?;
        Ok(Self(root))
    }

    /// Whether a handle has a written view ([`Self::try_from_shared`]).
    pub(crate) fn check_written(root: &SharedAddressOffset) -> Result<(), &'static str> {
        root.written_hash().map(|_| ())
    }

    /// A handle stored beside an address's block, whose written view is
    /// checked where the address is read as written
    /// ([`crate::kernel::Address::try_from_shared`]).
    pub(in crate::kernel::primitives::kernel_term) fn from_shared_unchecked(
        root: SharedAddressOffset,
    ) -> Self {
        Self(root)
    }

    pub(crate) fn shared(&self) -> &SharedAddressOffset {
        &self.0
    }

    pub(crate) fn into_shared(self) -> SharedAddressOffset {
        self.0
    }

    fn uncharged(node: KernelAddressOffset, index: Option<SharedMachineIntegerTerm>) -> Self {
        Self(
            node.into_shared_with_index(index, false)
                .expect("native offset types"),
        )
    }

    pub(crate) fn try_from_ref(root: &SharedAddressOffset) -> Result<&Self, &'static str> {
        Self::check_written(root)?;
        Ok(Self::from_ref(root))
    }

    fn from_ref(root: &SharedAddressOffset) -> &Self {
        // SAFETY: `AddressOffset` is a `repr(transparent)` wrapper of
        // `SharedAddressOffset`, so the two references have one layout. A
        // child of a written offset is written: its fingerprint is computed first.
        unsafe { &*(root as *const SharedAddressOffset as *const Self) }
    }

    fn index(&self) -> &SharedMachineIntegerTerm {
        self.0.written_index().expect("written offset index")
    }

    /// A small address index can carry arbitrarily deep *retained* operands.
    /// Its offset structure itself must stay bounded for source publication.
    pub(crate) fn is_shallow(&self) -> bool {
        match self.view() {
            OffsetView::Add(left, right) => {
                !matches!(left.view(), OffsetView::Add(..))
                    && !matches!(right.view(), OffsetView::Add(..))
            }
            _ => true,
        }
    }

    /// Preserve the written index node, including a zero scale; the smart
    /// `scale_int32` constructor may separately fold literal displacements.
    pub(crate) fn scaled_int32_node(value: OldMachineTerm, byte_width: i64) -> Self {
        Self::int32_scaled(
            SharedMachineIntegerTerm::index(MachineIntegerType::Int32, value),
            byte_width,
        )
    }

    pub(crate) fn scaled_int64_node(
        value: OldMachineTerm,
        byte_width: i64,
        unsigned: bool,
    ) -> Self {
        Self::int64_scaled(
            SharedMachineIntegerTerm::index(MachineIntegerType::Int64, value),
            byte_width,
            unsigned,
        )
    }

    /// The smart scaled index, which folds a literal index into a constant
    /// displacement.
    pub(crate) fn scale_int32(value: OldMachineTerm, byte_width: i64) -> Self {
        match value.as_const() {
            Some(value) => Self::constant((value as i32 as i64) * byte_width),
            None => Self::scaled_int32_node(value, byte_width),
        }
    }

    /// The smart 64-bit scaled index. Like [`Self::scale_int32`], it folds a
    /// literal index, and it recovers a widened `int32` index's exact scale.
    pub(crate) fn scale_int64(value: OldMachineTerm, byte_width: i64, unsigned: bool) -> Self {
        // A widened int32 index times a u32 stride fits in signed int64.
        // Recover its exact pointer scale without interpreting a modular
        // int32 product as an address displacement.
        if !unsigned {
            if let cast_term!(Int64From32, index) = &value
                && u32::try_from(byte_width).is_ok()
            {
                return Self::scale_int32(index.as_ref().clone(), byte_width);
            }
            if let OldMachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Multiply,
                left,
                right,
            } = &value
            {
                for (index, stride) in [(left, right), (right, left)] {
                    if let (cast_term!(Int64From32, index), int64_constant!(stride)) =
                        (index.as_ref(), stride.as_ref())
                        && let Ok(stride) = u32::try_from(constant_i64(*stride))
                        && let Some(width) = i64::from(stride).checked_mul(byte_width)
                        && u32::try_from(width).is_ok()
                    {
                        return Self::scale_int32(index.as_ref().clone(), width);
                    }
                }
            }
        }
        let constant = if unsigned {
            value.uint64_as_const().and_then(|value| {
                i64::try_from(value)
                    .ok()
                    .and_then(|value| value.checked_mul(byte_width))
            })
        } else {
            value
                .int64_as_const()
                .and_then(|value| value.checked_mul(byte_width))
        };
        match constant {
            Some(value) => Self::constant(value),
            None => Self::scaled_int64_node(value, byte_width, unsigned),
        }
    }

    /// Maps scaled index values without changing the offset expression.
    pub(crate) fn map_scaled_operands(
        &self,
        mut map: impl FnMut(&SharedMachineIntegerTerm) -> SharedMachineIntegerTerm,
    ) -> Self {
        enum Task<'a> {
            Visit(&'a AddressOffset),
            Add,
        }
        let mut pending = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Visit(offset) => match offset.view() {
                    OffsetView::Add(left, right) => {
                        pending.push(Task::Add);
                        pending.push(Task::Visit(right));
                        pending.push(Task::Visit(left));
                    }
                    OffsetView::Int32Scaled { byte_width, .. } => {
                        values.push(Self::int32_scaled(map(offset.index()), byte_width));
                    }
                    OffsetView::Int64Scaled {
                        byte_width,
                        unsigned,
                        ..
                    } => {
                        values.push(Self::int64_scaled(
                            map(offset.index()),
                            byte_width,
                            unsigned,
                        ));
                    }
                    OffsetView::Constant(_) | OffsetView::Variable(_) => {
                        values.push(offset.clone())
                    }
                },
                Task::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    values.push(Self::raw_add(left, right));
                }
            }
        }
        values.pop().expect("one mapped offset")
    }

    /// Retained index operands, in the same order as the legacy value walker.
    pub(crate) fn scaled_operands(&self) -> Vec<&SharedMachineIntegerTerm> {
        let mut values = Vec::new();
        let mut pending = vec![self];
        while let Some(offset) = pending.pop() {
            match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => {}
                OffsetView::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. } => {
                    values.push(offset.index())
                }
            }
        }
        values
    }

    pub(crate) fn for_each_scaled_operand(&self, mut visit: impl FnMut(&SharedMachineIntegerTerm)) {
        self.any_scaled_operand(|value| {
            visit(value);
            false
        });
    }

    pub(crate) fn any_scaled_operand(
        &self,
        mut test: impl FnMut(&SharedMachineIntegerTerm) -> bool,
    ) -> bool {
        let mut pending = vec![self];
        while let Some(offset) = pending.pop() {
            match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => {}
                OffsetView::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. } => {
                    if test(offset.index()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Native scalar payloads for legacy rendering and test output. This can
    /// expand shared arithmetic; checking uses `for_each_scaled_operand`.
    pub(crate) fn native_scaled_values_for_output(&self) -> Vec<&OldMachineTerm> {
        self.scaled_operands()
            .into_iter()
            .map(SharedMachineIntegerTerm::structural_value)
            .collect()
    }

    /// This offset as `sum(sext(index) * stride) + constant`, when every
    /// leaf is a constant or a scaled `int32` index: the scaled leaves and
    /// the constant. The sum is exact, with no wrap, so it describes the
    /// offset's integer value.
    pub(in crate::kernel) fn int32_scaled_linear_form(
        &self,
    ) -> Option<(Vec<(&SharedMachineIntegerTerm, i64)>, i64)> {
        // Each leaf's magnitude stays below `2^31 * 2^24`, so a sum of at
        // most this many of them, and their constant, fits in an `i64`.
        const MAX_LEAVES: usize = 64;
        const MAX_STRIDE: i64 = 1 << 24;
        const MAX_CONSTANT: i64 = 1 << 48;
        let mut scaled = Vec::new();
        let mut constant = 0i64;
        let mut pending = vec![self];
        let mut leaves = 0usize;
        while let Some(term) = pending.pop() {
            leaves += 1;
            if leaves > MAX_LEAVES {
                return None;
            }
            match term.view() {
                OffsetView::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                OffsetView::Constant(value) if value.unsigned_abs() < MAX_CONSTANT as u64 => {
                    constant += value;
                }
                OffsetView::Int32Scaled { byte_width, .. }
                    if byte_width.unsigned_abs() <= MAX_STRIDE as u64 =>
                {
                    scaled.push((term.index(), byte_width));
                }
                _ => return None,
            }
        }
        Some((scaled, constant))
    }

    /// The constant this offset folds to, as the native offset tree folds it.
    pub(in crate::kernel) fn as_const(&self) -> Option<i64> {
        self.0.written_constant()
    }

    /// The folding sum: two constants fold, a zero addend drops, and a
    /// trailing constant joins a sum's trailing constant.
    pub(crate) fn add(left: Self, right: Self) -> Self {
        if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
            return Self::constant(left + right);
        }
        if left.as_const() == Some(0) {
            return right;
        }
        if right.as_const() == Some(0) {
            return left;
        }
        // Keep a chain of constant byte displacements in one canonical
        // shape. Nested member access commonly forms `(base + outer) +
        // inner`, while aggregate copying starts from `base + total`;
        // treating those as distinct pointers would mint unrelated
        // symbolic loads for the same field.
        if let (OffsetView::Add(base, trailing), OffsetView::Constant(right)) =
            (left.view(), right.view())
            && let Some(trailing) = trailing.as_const()
        {
            return Self::add(base.clone(), Self::constant(trailing + right));
        }
        Self::raw_add(left, right)
    }
}

impl PartialEq for AddressOffset {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
            || (self.0.written_hash() == other.0.written_hash()
                && self.0.written_cmp(&other.0).is_eq())
    }
}
impl Eq for AddressOffset {}
/// Feeds the hasher exactly what the native offset tree's derived `Hash` fed
/// it: each node's discriminant (as an `isize`), then its fields, a sum's left
/// operand before its right, an index by its identity. Content hashes built
/// from addresses (treap priorities, cached map hashes) therefore keep their
/// values, and with them the shapes and charged work they decide. Like the
/// derived hash, it visits every node; the cached syntax hash serves only
/// equality.
impl Hash for AddressOffset {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut pending = vec![self];
        while let Some(offset) = pending.pop() {
            match offset.0.node() {
                KernelAddressOffset::Constant(value) => {
                    0isize.hash(state);
                    value.hash(state);
                }
                KernelAddressOffset::Variable(variable) => {
                    1isize.hash(state);
                    variable.hash(state);
                }
                KernelAddressOffset::Add([left, right]) => {
                    2isize.hash(state);
                    pending.push(Self::from_ref(right));
                    pending.push(Self::from_ref(left));
                }
                KernelAddressOffset::Int32Scaled { byte_width, .. } => {
                    3isize.hash(state);
                    offset.index().hash(state);
                    byte_width.hash(state);
                }
                KernelAddressOffset::Int64Scaled {
                    byte_width,
                    unsigned,
                    ..
                } => {
                    4isize.hash(state);
                    offset.index().hash(state);
                    byte_width.hash(state);
                    unsigned.hash(state);
                }
            }
        }
    }
}
impl PartialOrd for AddressOffset {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AddressOffset {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.written_cmp(&other.0)
    }
}

/// The native offset tree's derived format.
impl std::fmt::Debug for AddressOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.view() {
            OffsetView::Constant(value) => f.debug_tuple("Constant").field(&value).finish(),
            OffsetView::Variable(value) => f.debug_tuple("Variable").field(&value).finish(),
            OffsetView::Add(left, right) => f.debug_tuple("Add").field(left).field(right).finish(),
            OffsetView::Int32Scaled { index, byte_width } => f
                .debug_struct("Int32Scaled")
                .field("value", &index)
                .field("byte_width", &byte_width)
                .finish(),
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned,
            } => f
                .debug_struct("Int64Scaled")
                .field("value", &index)
                .field("byte_width", &byte_width)
                .field("unsigned", &unsigned)
                .finish(),
        }
    }
}

/// Reads and builds exactly the nodes of the wrapped handle; a scaled node
/// reports its written index carrier.
impl OffsetTree for AddressOffset {
    fn view(&self) -> OffsetView<'_, Self> {
        match self.0.node() {
            KernelAddressOffset::Constant(value) => OffsetView::Constant(*value),
            KernelAddressOffset::Variable(variable) => OffsetView::Variable(*variable),
            KernelAddressOffset::Add([left, right]) => {
                OffsetView::Add(Self::from_ref(left), Self::from_ref(right))
            }
            KernelAddressOffset::Int32Scaled { byte_width, .. } => OffsetView::Int32Scaled {
                index: self.index().clone(),
                byte_width: *byte_width,
            },
            KernelAddressOffset::Int64Scaled {
                byte_width,
                unsigned,
                ..
            } => OffsetView::Int64Scaled {
                index: self.index().clone(),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }
    }

    // Native offset nodes cost nothing to build, so these record no work.
    // The leaf and sum constructors touch no thread-local state either: a
    // key's destructor builds placeholder constants.
    fn constant(value: i64) -> Self {
        Self::uncharged(KernelAddressOffset::Constant(value), None)
    }

    fn variable(variable: Variable) -> Self {
        Self::uncharged(KernelAddressOffset::Variable(variable), None)
    }

    fn raw_add(left: Self, right: Self) -> Self {
        Self::uncharged(KernelAddressOffset::Add([left.0, right.0]), None)
    }

    fn int32_scaled(index: SharedMachineIntegerTerm, byte_width: i64) -> Self {
        crate::instrumentation::without_charging(|| {
            let value = KernelTerm::retain_address_index(&index);
            let node = KernelAddressOffset::Int32Scaled { value, byte_width };
            Self::uncharged(node, Some(index))
        })
    }

    fn int64_scaled(index: SharedMachineIntegerTerm, byte_width: i64, unsigned: bool) -> Self {
        crate::instrumentation::without_charging(|| {
            let value = KernelTerm::retain_address_index(&index);
            let node = KernelAddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned,
            };
            Self::uncharged(node, Some(index))
        })
    }

    fn into_add(self) -> Result<(Self, Self), Self> {
        match self.0.into_add() {
            Ok((left, right)) => Ok((Self(left), Self(right))),
            Err(other) => Err(Self(other)),
        }
    }
}
