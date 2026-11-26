//! Prepared offset nodes. Construction preserves written shape, scale and
//! interpretation; it neither normalizes offsets nor consults facts.
use super::*;
mod operations;
mod written;
pub use written::AddressOffset;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum KernelAddressOffset {
    Constant(i64),
    Variable(Variable),
    Add([SharedAddressOffset; 2]),
    Int32Scaled {
        value: KernelTerm,
        byte_width: i64,
    },
    Int64Scaled {
        value: KernelTerm,
        byte_width: i64,
        unsigned: bool,
    },
}

/// Shared internal address component. Numeric children are common KernelTerm
/// handles; offsets are not independently spellable Click values.
#[derive(Clone)]
pub struct SharedAddressOffset(Arc<OffsetData>);
struct OffsetData {
    id: OffsetIdentity,
    node: KernelAddressOffset,
    constant: Option<i64>,
    /// A scaled node's written index carrier ([`AddressOffset`]): the one it
    /// was built from, else the one explicit output names, held so its
    /// identity never changes while the node is alive.
    index: std::sync::OnceLock<Result<SharedMachineIntegerTerm, &'static str>>,
    /// The written syntax fingerprint ([`AddressOffset`]'s equality fast path).
    syntax_hash: std::sync::OnceLock<Result<u64, &'static str>>,
    /// The written constant fold ([`AddressOffset::as_const`]).
    syntax_constant: std::sync::OnceLock<Option<i64>>,
}
impl OffsetData {
    fn new(id: OffsetIdentity, node: KernelAddressOffset, constant: Option<i64>) -> Self {
        Self {
            id,
            node,
            constant,
            index: Default::default(),
            syntax_hash: Default::default(),
            syntax_constant: Default::default(),
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
enum OffsetIdentity {
    Constant(i64),
    Interned(u64),
}
impl std::fmt::Debug for SharedAddressOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedAddressOffset")
            .field(&self.0.id)
            .finish()
    }
}
impl PartialEq for SharedAddressOffset {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for SharedAddressOffset {}
impl Hash for SharedAddressOffset {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}
/// The structural order of the written offset ([`AddressOffset`]), so a
/// handle can key an ordered map in place of a written offset without
/// changing its iteration or range order: by variant (constant, variable,
/// sum, 32-bit and 64-bit scaled index), then constants by value, variables
/// by identity, a sum by its left then its right operand, and a scaled index
/// by its retained machine index ([`SharedMachineIntegerTerm`]'s order), byte
/// width and interpretation.
///
/// Two handles can be structurally equal yet different handles: an index's
/// retained carrier may keep annotations written equality ignores.
/// Those fall back to handle identity, so `Ordering::Equal` holds exactly
/// when the handles are equal, as `Ord` requires of `Eq`.
///
/// The walk is iterative and stops at the first shared or ordered pair, so
/// comparing two handles that share a subtree does not walk it.
impl Ord for SharedAddressOffset {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        fn rank(node: &KernelAddressOffset) -> u8 {
            match node {
                KernelAddressOffset::Constant(_) => 0,
                KernelAddressOffset::Variable(_) => 1,
                KernelAddressOffset::Add(_) => 2,
                KernelAddressOffset::Int32Scaled { .. } => 3,
                KernelAddressOffset::Int64Scaled { .. } => 4,
            }
        }
        if self == other {
            return Ordering::Equal;
        }
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if left == right {
                continue;
            }
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
                    KernelAddressOffset::Int32Scaled {
                        value: a,
                        byte_width: w,
                    },
                    KernelAddressOffset::Int32Scaled {
                        value: b,
                        byte_width: x,
                    },
                ) => Self::exact_index(a)
                    .cmp(&Self::exact_index(b))
                    .then(w.cmp(x)),
                (
                    KernelAddressOffset::Int64Scaled {
                        value: a,
                        byte_width: w,
                        unsigned: u,
                    },
                    KernelAddressOffset::Int64Scaled {
                        value: b,
                        byte_width: x,
                        unsigned: v,
                    },
                ) => Self::exact_index(a)
                    .cmp(&Self::exact_index(b))
                    .then(w.cmp(x))
                    .then(u.cmp(v)),
                (a, b) => rank(a).cmp(&rank(b)),
            };
            if order != Ordering::Equal {
                return order;
            }
        }
        self.0.id.cmp(&other.0.id)
    }
}
impl PartialOrd for SharedAddressOffset {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
/// One node of an offset tree, read the same way from either view of a
/// handle ([`AddressOffset`] or [`SharedAddressOffset`]). Children are the
/// same view as the parent, and a scaled index is its retained machine index.
pub(crate) enum OffsetView<'a, T> {
    Constant(i64),
    Variable(Variable),
    Add(&'a T, &'a T),
    Int32Scaled {
        index: SharedMachineIntegerTerm,
        byte_width: i64,
    },
    Int64Scaled {
        index: SharedMachineIntegerTerm,
        byte_width: i64,
        unsigned: bool,
    },
}

/// An offset tree that can be read node by node through [`OffsetView`] and
/// built node by node. Each constructor builds exactly the node it names, as
/// written: none folds constants or consults facts, so a tree built through
/// these constructors as an [`AddressOffset`] wraps the handle built through
/// them as a [`SharedAddressOffset`]. The folding sum is each view's own
/// `add`, which fold alike.
pub(crate) trait OffsetTree: Sized {
    fn view(&self) -> OffsetView<'_, Self>;
    /// A constant byte displacement. It equals only a constant node of the
    /// same value, never a sum or scaled index that folds to that value.
    fn constant(value: i64) -> Self;
    /// A symbolic offset variable.
    fn variable(variable: Variable) -> Self;
    /// The sum node of two offsets. Unlike the folding `add`, it keeps zero
    /// and constant addends as written.
    fn raw_add(left: Self, right: Self) -> Self;
    /// A signed 32-bit index scaled by `byte_width`. A constant index stays
    /// an index; it is not folded into a constant offset.
    fn int32_scaled(index: SharedMachineIntegerTerm, byte_width: i64) -> Self;
    /// A 64-bit index scaled by `byte_width`, read as unsigned when
    /// `unsigned` holds. Like [`OffsetTree::int32_scaled`], it never folds.
    fn int64_scaled(index: SharedMachineIntegerTerm, byte_width: i64, unsigned: bool) -> Self;
    /// The two operands of a sum node, taken by value, or the offset itself
    /// when it is not a sum. It clones the two child handles.
    fn into_add(self) -> Result<(Self, Self), Self>;
}

/// Each constructor builds and interns exactly the node it names, charging
/// its construction; [`AddressOffset`]'s constructors build the same handle
/// without charge.
impl OffsetTree for SharedAddressOffset {
    fn view(&self) -> OffsetView<'_, Self> {
        match self.node() {
            KernelAddressOffset::Constant(value) => OffsetView::Constant(*value),
            KernelAddressOffset::Variable(variable) => OffsetView::Variable(*variable),
            KernelAddressOffset::Add([left, right]) => OffsetView::Add(left, right),
            KernelAddressOffset::Int32Scaled { value, byte_width } => OffsetView::Int32Scaled {
                index: Self::exact_index(value),
                byte_width: *byte_width,
            },
            KernelAddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => OffsetView::Int64Scaled {
                index: Self::exact_index(value),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }
    }

    fn constant(value: i64) -> Self {
        KernelAddressOffset::Constant(value).into_shared().unwrap()
    }

    fn variable(variable: Variable) -> Self {
        KernelAddressOffset::Variable(variable)
            .into_shared()
            .unwrap()
    }

    fn raw_add(left: Self, right: Self) -> Self {
        KernelAddressOffset::Add([left, right])
            .into_shared()
            .unwrap()
    }

    fn int32_scaled(index: SharedMachineIntegerTerm, byte_width: i64) -> Self {
        KernelAddressOffset::Int32Scaled {
            value: KernelTerm::retain_address_index(&index),
            byte_width,
        }
        .into_shared_with_index(Some(index), true)
        .expect("native offset types")
    }

    fn int64_scaled(index: SharedMachineIntegerTerm, byte_width: i64, unsigned: bool) -> Self {
        KernelAddressOffset::Int64Scaled {
            value: KernelTerm::retain_address_index(&index),
            byte_width,
            unsigned,
        }
        .into_shared_with_index(Some(index), true)
        .expect("native offset types")
    }

    fn into_add(self) -> Result<(Self, Self), Self> {
        match self.node() {
            KernelAddressOffset::Add([left, right]) => Ok((left.clone(), right.clone())),
            _ => Err(self),
        }
    }
}

#[derive(Default)]
struct OffsetInterner {
    nodes: HashMap<KernelAddressOffset, Weak<OffsetData>>,
    cleanup: VecDeque<KernelAddressOffset>,
    next_id: u64,
}

impl SharedAddressOffset {
    pub(crate) fn node(&self) -> &KernelAddressOffset {
        &self.0.node
    }
    /// The handle of `node`. A scaled node keeps `index`, the carrier it is
    /// built from, unless a live handle of the node already holds one.
    fn intern(
        node: KernelAddressOffset,
        index: Option<SharedMachineIntegerTerm>,
        charge: bool,
    ) -> Self {
        let handle = Self::intern_node(node, charge);
        if let Some(index) = index {
            let _ = handle.0.index.set(Ok(index));
        }
        handle
    }

    fn intern_node(node: KernelAddressOffset, charge: bool) -> Self {
        static INTERNER: std::sync::OnceLock<Mutex<OffsetInterner>> = std::sync::OnceLock::new();
        let mut interner = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("offset interner");
        if let Some(value) = interner.nodes.get(&node).and_then(Weak::upgrade) {
            return Self(value);
        }
        // Only insertion grows the arena. A live hit needs no garbage upkeep.
        if charge {
            crate::instrumentation::record_deterministic_work(8);
        }
        // As with the common term arena, bounded upkeep never scans the arena.
        for _ in 0..interner.cleanup.len().min(8) {
            let key = interner.cleanup.pop_front().unwrap();
            if interner
                .nodes
                .get(&key)
                .is_some_and(|value| value.strong_count() == 0)
            {
                interner.nodes.remove(&key);
            } else {
                interner.cleanup.push_back(key);
            }
        }
        let id = interner.next_id;
        interner.next_id = id.checked_add(1).expect("offset identity exhausted");
        let constant = node.constant_value();
        let value = Arc::new(OffsetData::new(
            OffsetIdentity::Interned(id),
            node.clone(),
            constant,
        ));
        interner.nodes.insert(node.clone(), Arc::downgrade(&value));
        interner.cleanup.push_back(node);
        Self(value)
    }
}

impl KernelAddressOffset {
    pub(crate) fn offset_children(&self) -> &[SharedAddressOffset] {
        match self {
            Self::Add(children) => children,
            _ => &[],
        }
    }

    pub(crate) fn index(&self) -> Option<&KernelTerm> {
        match self {
            Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => Some(value),
            _ => None,
        }
    }

    pub(crate) fn into_shared(self) -> Result<SharedAddressOffset, &'static str> {
        self.into_shared_with_index(None, true)
    }

    /// [`Self::into_shared`], for a scaled node built from the index carrier
    /// `index` (see [`AddressOffset`]). Without `charge`, it records no
    /// deterministic work: [`AddressOffset`] builds nodes as the native
    /// offset tree did, for free.
    fn into_shared_with_index(
        self,
        index: Option<SharedMachineIntegerTerm>,
        charge: bool,
    ) -> Result<SharedAddressOffset, &'static str> {
        // Constant displacements already have scalar identities. Their value
        // supplies equality directly, without interner insertion or upkeep.
        if let Self::Constant(value) = &self {
            if charge {
                crate::instrumentation::record_deterministic_work(1);
            }
            let id = OffsetIdentity::Constant(*value);
            let constant = Some(*value);
            return Ok(SharedAddressOffset(Arc::new(OffsetData::new(
                id, self, constant,
            ))));
        }
        // One selected node; a new arena entry pays its bounded upkeep inside
        // intern. Reusing a live node performs no insertion or cleanup.
        if charge {
            crate::instrumentation::record_deterministic_work(1);
        }
        match &self {
            Self::Int32Scaled { value, .. }
                if !matches!(
                    value.ty(),
                    KernelType::Program(ProgramType::Int32 | ProgramType::UInt32)
                ) =>
            {
                return Err("32-bit offset index has the wrong type");
            }
            // The interpretation flag is independent of the retained index carrier.
            Self::Int64Scaled { value, .. }
                if !matches!(
                    value.ty(),
                    KernelType::Program(ProgramType::Int64 | ProgramType::UInt64)
                ) =>
            {
                return Err("64-bit offset index has the wrong type");
            }
            _ => {}
        }
        Ok(SharedAddressOffset::intern(self, index, charge))
    }

    /// The native offset index contract, shared by explicit output and storage keys.
    pub(in crate::kernel) fn index_key(
        value: &KernelTerm,
    ) -> Result<SharedMachineIntegerTerm, &'static str> {
        let KernelType::Program(ty) = value.ty() else {
            return Err("expected machine offset index");
        };
        let format =
            MachineIntegerType::from_program_type(*ty).ok_or("expected machine offset index")?;
        if let Some(index) = value.retained_address_index(format) {
            return Ok(index.clone());
        }
        if let Some(native) = value.retained_machine_input() {
            return Ok(SharedMachineIntegerTerm::index(format, native.clone()));
        }
        if let Some(value) = SharedMachineIntegerTerm::from_shared(format, value.clone()) {
            return Ok(value);
        }
        // Preserve the existing selected native reader for an opaque index.
        KernelTermExport::machine(value)
            .map(|native| SharedMachineIntegerTerm::index(format, native))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The derived-trait reference for written offsets: the variants, field
    /// order and derived `Eq`, `Hash`, `Ord` and `Debug` that [`AddressOffset`]
    /// must reproduce exactly (an index compares by its identity). Content
    /// hashes and ordered keys built from offsets depend on these values.
    #[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
    enum Reference {
        Constant(i64),
        Variable(Variable),
        Add(Box<Reference>, Box<Reference>),
        Int32Scaled {
            value: SharedMachineIntegerTerm,
            byte_width: i64,
        },
        Int64Scaled {
            value: SharedMachineIntegerTerm,
            byte_width: i64,
            unsigned: bool,
        },
    }

    impl Reference {
        fn written(&self) -> AddressOffset {
            match self {
                Self::Constant(value) => AddressOffset::constant(*value),
                Self::Variable(variable) => AddressOffset::variable(*variable),
                Self::Add(left, right) => AddressOffset::raw_add(left.written(), right.written()),
                Self::Int32Scaled { value, byte_width } => {
                    AddressOffset::int32_scaled(value.clone(), *byte_width)
                }
                Self::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => AddressOffset::int64_scaled(value.clone(), *byte_width, *unsigned),
            }
        }

        fn of(offset: &AddressOffset) -> Self {
            match offset.view() {
                OffsetView::Constant(value) => Self::Constant(value),
                OffsetView::Variable(variable) => Self::Variable(variable),
                OffsetView::Add(left, right) => {
                    Self::Add(Box::new(Self::of(left)), Box::new(Self::of(right)))
                }
                OffsetView::Int32Scaled { index, byte_width } => Self::Int32Scaled {
                    value: index,
                    byte_width,
                },
                OffsetView::Int64Scaled {
                    index,
                    byte_width,
                    unsigned,
                } => Self::Int64Scaled {
                    value: index,
                    byte_width,
                    unsigned,
                },
            }
        }
    }

    #[test]
    fn offset_payload_round_trips_shape_scale_and_interpretation() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut values = vec![
            AddressOffset::constant(i64::MIN),
            AddressOffset::constant(i64::MAX),
            AddressOffset::variable(Variable(994001)),
        ];
        for width in [0, -8, 4] {
            values.push(AddressOffset::scaled_int32_node(
                OldMachineTerm::Variable(Variable(994002)),
                width,
            ));
            for unsigned in [false, true] {
                values.push(AddressOffset::scaled_int64_node(
                    OldMachineTerm::Variable(Variable(994003)),
                    width,
                    unsigned,
                ));
            }
        }
        for value in values {
            let source = AddressOffset::raw_add(AddressOffset::constant(0), value);
            let root = source.shared().clone();
            assert_eq!(
                AddressOffset::try_from_shared(root.clone()).unwrap(),
                source
            );
            assert_eq!(
                SharedAddressOffset::raw_add(
                    SharedAddressOffset::constant(0),
                    root.node().offset_children()[1].clone()
                ),
                root
            );
            assert_eq!(root.node().offset_children().len(), 2);
        }
        let signed = AddressOffset::scaled_int64_node(
            OldMachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            false,
        );
        let unsigned = AddressOffset::scaled_int64_node(
            OldMachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            true,
        );
        assert_ne!(signed.shared(), unsigned.shared());
        assert_ne!(signed, unsigned);
    }

    #[test]
    fn offset_payload_preserves_the_index_carrier_independently_of_interpretation() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let value =
                SharedMachineIntegerTerm::index(format, OldMachineTerm::Variable(Variable(994006)));
            let source = if format.format().bits() == 32 {
                AddressOffset::int32_scaled(value.clone(), 4)
            } else {
                AddressOffset::int64_scaled(value.clone(), 8, false)
            };
            let root = source.shared().clone();
            let output = AddressOffset::try_from_shared(root.clone()).unwrap();
            assert_eq!(source, output);
            let index = root.node().index().unwrap();
            assert_eq!(index.ty(), &KernelType::Program(format.program_type()));
            assert_eq!(index, value.shared_operand().unwrap());
        }
    }

    /// Reference offsets of every node kind, including the cell store's
    /// range shapes and scaled indices under sums.
    fn ordering_cases() -> Vec<Reference> {
        let constant = Reference::Constant;
        let add = |a: Reference, b: Reference| Reference::Add(Box::new(a), Box::new(b));
        let variable = |id| Reference::Variable(Variable(id));
        let mut values = vec![
            constant(i64::MIN),
            constant(-8),
            constant(0),
            constant(4),
            constant(i64::MAX),
            variable(994101),
            variable(994102),
        ];
        // The cell store's range shapes: a stem plus constants either side.
        for stem in [variable(994101), variable(994102)] {
            for k in [-4, 0, 4, 8] {
                values.push(add(stem.clone(), constant(k)));
            }
        }
        values.push(add(add(variable(994101), constant(4)), constant(4)));
        values.push(add(variable(994101), add(constant(4), constant(4))));
        values.push(add(constant(0), variable(994101)));
        for id in [994103, 994104] {
            for width in [1, 4, -8] {
                let index = |format| {
                    SharedMachineIntegerTerm::index(format, OldMachineTerm::Variable(Variable(id)))
                };
                values.push(Reference::Int32Scaled {
                    value: index(MachineIntegerType::Int32),
                    byte_width: width,
                });
                for unsigned in [false, true] {
                    values.push(Reference::Int64Scaled {
                        value: index(MachineIntegerType::Int64),
                        byte_width: width,
                        unsigned,
                    });
                }
            }
        }
        let scaled = values.len();
        for index in 0..scaled {
            if matches!(values[index], Reference::Int32Scaled { .. }) {
                values.push(add(variable(994101), values[index].clone()));
            }
        }
        values
    }

    /// A handle orders exactly as the written offset it wraps, so it can key
    /// an ordered map (and a cell-store range scan) in place of a written
    /// offset without changing its order.
    #[test]
    fn shared_offsets_order_as_their_written_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = ordering_cases();
        let roots: Vec<_> = values
            .iter()
            .map(|value| value.written().into_shared())
            .collect();
        for (a, left) in values.iter().zip(&roots) {
            for (b, right) in values.iter().zip(&roots) {
                assert_eq!(left.cmp(right), a.cmp(b), "{a:?} vs {b:?}");
                assert_eq!(left == right, a == b, "{a:?} vs {b:?}");
            }
        }
        let mut sorted = values.clone();
        sorted.sort();
        let mut sorted_roots = roots.clone();
        sorted_roots.sort();
        let output: Vec<_> = sorted_roots
            .into_iter()
            .map(|root| Reference::of(&AddressOffset::try_from_shared(root).unwrap()))
            .collect();
        assert_eq!(output, sorted);
    }

    /// Handles that differ only in an index annotation written equality
    /// ignores are ordered apart, consistently with handle equality.
    #[test]
    fn annotation_distinct_offsets_order_consistently_with_handle_equality() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let roots: Vec<_> = [CScalarClass::Int, CScalarClass::Char]
            .into_iter()
            .map(|class| {
                AddressOffset::scaled_int64_node(
                    OldMachineTerm::IntegerAddress(
                        Box::new(OldAddress::symbolic(Variable(994105))),
                        crate::kernel::AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    ),
                    1,
                    true,
                )
                .into_shared()
            })
            .collect();
        assert_ne!(roots[0], roots[1]);
        assert_ne!(roots[0].cmp(&roots[1]), std::cmp::Ordering::Equal);
        assert_eq!(roots[0].cmp(&roots[1]), roots[1].cmp(&roots[0]).reverse());
    }

    fn hash_of(offset: &impl Hash) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        offset.hash(&mut hasher);
        hasher.finish()
    }

    /// A written offset compares, orders, hashes and prints exactly as the
    /// reference value it was built from, and keeps doing so after the
    /// reference values are gone: its index identities do not drift.
    #[test]
    fn written_offsets_compare_order_hash_and_print_as_the_reference() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = ordering_cases();
        let written: Vec<_> = values.iter().map(Reference::written).collect();
        let expected: Vec<Vec<_>> = values
            .iter()
            .map(|a| values.iter().map(|b| (a.cmp(b), a == b)).collect())
            .collect();
        for (a, left) in values.iter().zip(&written) {
            assert_eq!(format!("{a:?}"), format!("{left:?}"));
            assert_eq!(&Reference::of(left), a);
            assert_eq!(hash_of(left), hash_of(a), "{a:?}");
        }
        drop(values);
        for _ in 0..2 {
            for (i, left) in written.iter().enumerate() {
                for (j, right) in written.iter().enumerate() {
                    let (order, equal) = expected[i][j];
                    assert_eq!(left.cmp(right), order, "{left:?} vs {right:?}");
                    assert_eq!(left == right, equal, "{left:?} vs {right:?}");
                    if equal {
                        assert_eq!(hash_of(left), hash_of(right));
                    }
                }
            }
        }
    }

    /// Handles that differ only in an index annotation written equality
    /// ignores are one written offset: equal, hashed alike and unordered.
    #[test]
    fn annotation_distinct_handles_are_one_written_offset() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let written: Vec<_> = [CScalarClass::Int, CScalarClass::Char]
            .into_iter()
            .map(|class| {
                AddressOffset::raw_add(
                    AddressOffset::variable(Variable(994106)),
                    AddressOffset::scaled_int64_node(
                        OldMachineTerm::IntegerAddress(
                            Box::new(OldAddress::symbolic(Variable(994107))),
                            crate::kernel::AddressObjectClass::new(Some(CAccessClass::Scalar(
                                class,
                            ))),
                        ),
                        1,
                        true,
                    ),
                )
            })
            .collect();
        assert_ne!(written[0].shared(), written[1].shared());
        assert_eq!(written[0], written[1]);
        assert_eq!(hash_of(&written[0]), hash_of(&written[1]));
        assert_eq!(written[0].cmp(&written[1]), std::cmp::Ordering::Equal);
        let other = AddressOffset::raw_add(
            AddressOffset::variable(Variable(994106)),
            AddressOffset::constant(0),
        );
        assert_eq!(
            written[0].cmp(&other),
            Reference::of(&written[0]).cmp(&Reference::of(&other))
        );
    }

    /// The written constant fold and the folding sum.
    #[test]
    fn written_offsets_fold_constants_and_trailing_displacements() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = AddressOffset::variable(Variable(994108));
        let scaled = AddressOffset::scaled_int32_node(OldMachineTerm::constant(3), 4);
        assert_eq!(scaled.as_const(), Some(12));
        assert!(matches!(scaled.view(), OffsetView::Int32Scaled { .. }));
        let wide = AddressOffset::scaled_int64_node(
            OldMachineTerm::Constant {
                format: MachineIntegerType::UInt64,
                bits: u64::MAX as u128,
            },
            1,
            true,
        );
        assert_eq!(wide.as_const(), None);
        assert_eq!(variable.as_const(), None);
        assert_eq!(
            AddressOffset::raw_add(AddressOffset::constant(4), scaled.clone()).as_const(),
            Some(16)
        );
        assert_eq!(
            AddressOffset::add(scaled.clone(), AddressOffset::constant(4)),
            AddressOffset::constant(16)
        );
        assert_eq!(
            AddressOffset::add(AddressOffset::constant(0), variable.clone()),
            variable
        );
        assert_eq!(
            AddressOffset::add(variable.clone(), scaled.clone()),
            AddressOffset::raw_add(variable.clone(), scaled)
        );
        let sum = AddressOffset::raw_add(variable.clone(), AddressOffset::constant(4));
        assert_eq!(
            AddressOffset::add(sum, AddressOffset::constant(4)),
            AddressOffset::raw_add(variable, AddressOffset::constant(8))
        );
        assert_eq!(
            AddressOffset::scale_int32(OldMachineTerm::constant(u32::MAX), 8),
            AddressOffset::constant(-8)
        );
        let index = OldMachineTerm::Variable(Variable(994109));
        assert_eq!(
            AddressOffset::scale_int32(index.clone(), 8),
            AddressOffset::scaled_int32_node(index, 8)
        );
    }

    #[test]
    fn offset_payload_keeps_exact_opaque_index_annotations() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let mut roots = Vec::new();
        let mut written = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let source = AddressOffset::scaled_int64_node(
                OldMachineTerm::IntegerAddress(
                    Box::new(OldAddress::symbolic(Variable(994004))),
                    crate::kernel::AddressObjectClass::new(expected.clone()),
                ),
                1,
                true,
            );
            let root = source.shared().clone();
            let output = AddressOffset::try_from_shared(root.clone()).unwrap();
            assert_eq!(source, output);
            let OffsetView::Int64Scaled { index, .. } = output.view() else {
                panic!("scaled index")
            };
            let OldMachineTerm::IntegerAddress(_, annotation) = index.structural_value() else {
                panic!("exact address input")
            };
            assert_eq!(annotation.class(), expected);
            roots.push(root);
            written.push(source);
        }
        assert_eq!(written[0], written[1]);
        assert_ne!(roots[0], roots[1]);
    }

    /// Each [`OffsetTree`] constructor, and each view's folding `add`, builds
    /// as an [`AddressOffset`] exactly the handle the same call builds as a
    /// [`SharedAddressOffset`], so a caller written against the trait builds
    /// the same offset whichever view it holds.
    #[test]
    fn offset_constructors_build_the_same_handle_in_both_views() {
        let _session = crate::kernel::VerificationSession::enter();
        let index = |format, id| {
            SharedMachineIntegerTerm::index(format, OldMachineTerm::Variable(Variable(id)))
        };
        let indices = [
            index(MachineIntegerType::Int32, 994201),
            index(MachineIntegerType::UInt32, 994202),
            SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::constant(3),
            ),
            SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::constant(u32::MAX),
            ),
        ];
        let mut values = Vec::new();
        for value in [i64::MIN, -4, 0, 4, i64::MAX] {
            let written = AddressOffset::constant(value);
            assert_eq!(written.shared(), &SharedAddressOffset::constant(value));
            values.push(written);
        }
        for id in [994203, 994205] {
            let written = AddressOffset::variable(Variable(id));
            assert_eq!(
                written.shared(),
                &SharedAddressOffset::variable(Variable(id))
            );
            values.push(written);
        }
        values.push(AddressOffset::scaled_int64_node(
            OldMachineTerm::Variable(Variable(994204)),
            8,
            true,
        ));
        let wide_indices = [
            index(MachineIntegerType::UInt64, 994206),
            SharedMachineIntegerTerm::intern(
                MachineIntegerType::UInt64,
                OldMachineTerm::Constant {
                    format: MachineIntegerType::UInt64,
                    bits: u64::MAX as u128,
                },
            ),
        ];
        for index in &wide_indices {
            for width in [1, -8] {
                for unsigned in [false, true] {
                    let written = AddressOffset::int64_scaled(index.clone(), width, unsigned);
                    assert_eq!(
                        written.shared(),
                        &SharedAddressOffset::int64_scaled(index.clone(), width, unsigned)
                    );
                    values.push(written);
                }
            }
        }
        for index in &indices {
            for width in [0, 1, 4, -8] {
                let written = AddressOffset::int32_scaled(index.clone(), width);
                assert_eq!(
                    written.shared(),
                    &SharedAddressOffset::int32_scaled(index.clone(), width)
                );
                values.push(written);
            }
        }
        fn extreme(offset: &AddressOffset) -> bool {
            match offset.view() {
                OffsetView::Constant(value) => value.unsigned_abs() > 1 << 40,
                OffsetView::Add(left, right) => extreme(left) || extreme(right),
                _ => false,
            }
        }
        let leaves = values.len();
        for left in 0..leaves {
            values.push(AddressOffset::raw_add(
                values[left].clone(),
                AddressOffset::constant(4),
            ));
        }
        for left in &values {
            for right in &values {
                let (shared_left, shared_right) = (left.shared(), right.shared());
                assert_eq!(
                    AddressOffset::raw_add(left.clone(), right.clone()).shared(),
                    &SharedAddressOffset::raw_add(shared_left.clone(), shared_right.clone()),
                    "{left:?} + {right:?}"
                );
                // Both folds add constants unchecked, so extreme constants
                // stay out of the folding sum.
                if extreme(left) || extreme(right) {
                    continue;
                }
                assert_eq!(
                    AddressOffset::add(left.clone(), right.clone()).shared(),
                    &SharedAddressOffset::add(shared_left.clone(), shared_right.clone()),
                    "{left:?} + {right:?}"
                );
            }
        }
    }

    /// `into_add` yields a sum's two operands as written, in order, from
    /// either view, and returns any other node unchanged.
    #[test]
    fn into_add_splits_only_a_sum_node() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = AddressOffset::variable(Variable(994301));
        let zero = AddressOffset::constant(0);
        let sum = AddressOffset::raw_add(variable.clone(), zero.clone());
        assert_eq!(sum.clone().into_add(), Ok((variable.clone(), zero.clone())));
        let (left, right) = sum.shared().clone().into_add().unwrap();
        assert_eq!((&left, &right), (variable.shared(), zero.shared()));
        let scaled = AddressOffset::int32_scaled(
            SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::constant(3),
            ),
            4,
        );
        for leaf in [variable, zero, scaled] {
            assert_eq!(leaf.clone().into_add(), Err(leaf.clone()));
            assert_eq!(leaf.shared().clone().into_add(), Err(leaf.shared().clone()));
        }
    }

    #[test]
    fn offset_payload_rejects_mixed_sorts_without_normalizing_children() {
        let offset = KernelAddressOffset::Constant(0).into_shared().unwrap();
        let integer = KernelTerm::integer_literal(0.into());
        assert!(
            KernelAddressOffset::Int32Scaled {
                value: integer,
                byte_width: 0
            }
            .into_shared()
            .is_err()
        );
        let wide = KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(994005));
        assert!(
            KernelAddressOffset::Int32Scaled {
                value: wide,
                byte_width: 1
            }
            .into_shared()
            .is_err()
        );
        let sum = KernelAddressOffset::Add([offset.clone(), offset.clone()])
            .into_shared()
            .unwrap();
        assert_ne!(sum, offset);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/offsets.rs");
}
