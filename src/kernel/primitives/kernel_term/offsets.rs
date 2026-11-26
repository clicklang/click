//! Prepared offset nodes. Construction preserves written shape, scale and
//! interpretation; it neither normalizes offsets nor consults facts.
use super::*;
mod operations;

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
/// The structural order of [`OldAddressOffset`]'s derived `Ord`, so a handle
/// can key an ordered map in place of an old offset without changing its
/// iteration or range order: by variant (constant, variable, sum, 32-bit and
/// 64-bit scaled index), then constants by value, variables by identity, a
/// sum by its left then its right operand, and a scaled index by its retained
/// machine index ([`SharedMachineIntegerTerm`]'s order), byte width and
/// interpretation. An imported offset therefore compares exactly as the old
/// value it came from.
///
/// Two handles can be structurally equal yet different handles: an index's
/// retained carrier may keep annotations the old value's equality ignores.
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
/// One node of an offset tree, read the same way from either representation
/// ([`OldAddressOffset`] or [`SharedAddressOffset`]). A reader written against
/// [`OffsetTree::view`] works unchanged when an old offset is replaced by its
/// shared handle: children are the same representation as the parent, and a
/// scaled index is its retained machine index, which import keeps, so both
/// representations of one offset give the same index.
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
/// these constructors from old offsets imports to the handle built through
/// them from shared ones. The folding sum is each representation's own
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
    /// when it is not a sum. The old representation moves its boxed
    /// operands out; the shared one clones its two child handles.
    fn into_add(self) -> Result<(Self, Self), Self>;
}

impl OffsetTree for OldAddressOffset {
    fn view(&self) -> OffsetView<'_, Self> {
        match self {
            Self::Constant(value) => OffsetView::Constant(*value),
            Self::Variable(variable) => OffsetView::Variable(*variable),
            Self::Add(left, right) => OffsetView::Add(left, right),
            Self::Int32Scaled { value, byte_width } => OffsetView::Int32Scaled {
                index: value.clone(),
                byte_width: *byte_width,
            },
            Self::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => OffsetView::Int64Scaled {
                index: value.clone(),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }
    }

    fn constant(value: i64) -> Self {
        Self::Constant(value)
    }

    fn variable(variable: Variable) -> Self {
        Self::Variable(variable)
    }

    fn raw_add(left: Self, right: Self) -> Self {
        Self::Add(Box::new(left), Box::new(right))
    }

    fn int32_scaled(index: SharedMachineIntegerTerm, byte_width: i64) -> Self {
        Self::Int32Scaled {
            value: index,
            byte_width,
        }
    }

    fn int64_scaled(index: SharedMachineIntegerTerm, byte_width: i64, unsigned: bool) -> Self {
        Self::Int64Scaled {
            value: index,
            byte_width,
            unsigned,
        }
    }

    fn into_add(self) -> Result<(Self, Self), Self> {
        match self {
            Self::Add(left, right) => Ok((*left, *right)),
            other => Err(other),
        }
    }
}

/// Each constructor builds the node [`KernelAddressOffset::try_import`] builds
/// from the same old node, so a constructed handle is the imported one, and an
/// index of the wrong machine type is refused here as import refuses it.
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
        .into_shared()
        .expect("native offset types")
    }

    fn int64_scaled(index: SharedMachineIntegerTerm, byte_width: i64, unsigned: bool) -> Self {
        KernelAddressOffset::Int64Scaled {
            value: KernelTerm::retain_address_index(&index),
            byte_width,
            unsigned,
        }
        .into_shared()
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
    fn intern(node: KernelAddressOffset) -> Self {
        static INTERNER: std::sync::OnceLock<Mutex<OffsetInterner>> = std::sync::OnceLock::new();
        let mut interner = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("offset interner");
        if let Some(value) = interner.nodes.get(&node).and_then(Weak::upgrade) {
            return Self(value);
        }
        // Only insertion grows the arena. A live hit needs no garbage upkeep.
        crate::instrumentation::record_deterministic_work(8);
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
        let value = Arc::new(OffsetData {
            id: OffsetIdentity::Interned(id),
            constant: node.constant_value(),
            node: node.clone(),
        });
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
        // Constant displacements already have scalar identities. Their value
        // supplies equality directly, without interner insertion or upkeep.
        if let Self::Constant(value) = &self {
            crate::instrumentation::record_deterministic_work(1);
            return Ok(SharedAddressOffset(Arc::new(OffsetData {
                id: OffsetIdentity::Constant(*value),
                constant: Some(*value),
                node: self,
            })));
        }
        // One selected node; a new arena entry pays its bounded upkeep inside
        // intern. Reusing a live node performs no insertion or cleanup.
        crate::instrumentation::record_deterministic_work(1);
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
        Ok(SharedAddressOffset::intern(self))
    }

    pub(crate) fn import(offset: &OldAddressOffset) -> SharedAddressOffset {
        Self::try_import(offset).expect("native offset types")
    }

    pub(crate) fn try_import(
        offset: &OldAddressOffset,
    ) -> Result<SharedAddressOffset, &'static str> {
        enum Task<'a> {
            Enter(&'a OldAddressOffset),
            Add,
        }
        let mut pending = vec![Task::Enter(offset)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            let node = match task {
                Task::Enter(OldAddressOffset::Constant(value)) => Self::Constant(*value),
                Task::Enter(OldAddressOffset::Variable(value)) => Self::Variable(*value),
                Task::Enter(OldAddressOffset::Add(left, right)) => {
                    pending.extend([Task::Add, Task::Enter(right), Task::Enter(left)]);
                    continue;
                }
                Task::Enter(OldAddressOffset::Int32Scaled { value, byte_width }) => {
                    Self::Int32Scaled {
                        value: KernelTerm::retain_address_index(value),
                        byte_width: *byte_width,
                    }
                }
                Task::Enter(OldAddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                }) => Self::Int64Scaled {
                    value: KernelTerm::retain_address_index(value),
                    byte_width: *byte_width,
                    unsigned: *unsigned,
                },
                Task::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    Self::Add([left, right])
                }
            };
            values.push(node.into_shared()?);
        }
        Ok(values.pop().expect("offset root"))
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

    /// Explicit native output. Completed offset children are moved, never
    /// cached and cloned at every prefix. Shared numeric indices stay shared.
    pub(crate) fn export(root: &SharedAddressOffset) -> Result<OldAddressOffset, &'static str> {
        enum Task<'a> {
            Enter(&'a SharedAddressOffset),
            Add,
        }
        let mut pending = vec![Task::Enter(root)];
        let mut values = Vec::new();
        let index = Self::index_key;
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let value = match task {
                Task::Enter(root) => match root.node() {
                    Self::Constant(value) => OldAddressOffset::Constant(*value),
                    Self::Variable(value) => OldAddressOffset::Variable(*value),
                    Self::Add([left, right]) => {
                        pending.extend([Task::Add, Task::Enter(right), Task::Enter(left)]);
                        continue;
                    }
                    Self::Int32Scaled { value, byte_width } => OldAddressOffset::Int32Scaled {
                        value: index(value)?,
                        byte_width: *byte_width,
                    },
                    Self::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => OldAddressOffset::Int64Scaled {
                        value: index(value)?,
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    },
                },
                Task::Add => {
                    let right = values.pop().ok_or("missing right offset")?;
                    let left = values.pop().ok_or("missing left offset")?;
                    OldAddressOffset::Add(Box::new(left), Box::new(right))
                }
            };
            values.push(value);
        }
        values.pop().ok_or("missing offset root")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_payload_round_trips_shape_scale_and_interpretation() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut values = vec![
            OldAddressOffset::Constant(i64::MIN),
            OldAddressOffset::Constant(i64::MAX),
            OldAddressOffset::Variable(Variable(994001)),
        ];
        for width in [0, -8, 4] {
            values.push(OldAddressOffset::scaled_int32_node(
                OldMachineTerm::Variable(Variable(994002)),
                width,
            ));
            for unsigned in [false, true] {
                values.push(OldAddressOffset::scaled_int64_node(
                    OldMachineTerm::Variable(Variable(994003)),
                    width,
                    unsigned,
                ));
            }
        }
        for value in values {
            let source =
                OldAddressOffset::Add(Box::new(OldAddressOffset::Constant(0)), Box::new(value));
            let root = KernelAddressOffset::import(&source);
            assert_eq!(KernelAddressOffset::export(&root).unwrap(), source);
            assert_eq!(KernelAddressOffset::import(&source), root);
            assert_eq!(root.node().offset_children().len(), 2);
        }
        let signed = OldAddressOffset::scaled_int64_node(
            OldMachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            false,
        );
        let unsigned = OldAddressOffset::scaled_int64_node(
            OldMachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            true,
        );
        assert_ne!(
            KernelAddressOffset::import(&signed),
            KernelAddressOffset::import(&unsigned)
        );
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
                OldAddressOffset::Int32Scaled {
                    value: value.clone(),
                    byte_width: 4,
                }
            } else {
                OldAddressOffset::Int64Scaled {
                    value: value.clone(),
                    byte_width: 8,
                    unsigned: false,
                }
            };
            let root = KernelAddressOffset::import(&source);
            let output = KernelAddressOffset::export(&root).unwrap();
            assert_eq!(source, output);
            let index = root.node().index().unwrap();
            assert_eq!(index.ty(), &KernelType::Program(format.program_type()));
            assert_eq!(index, value.shared_operand().unwrap());
        }
    }

    /// An imported offset orders exactly as the old value it came from, so
    /// a handle can key an ordered map (and a cell-store range scan) in place
    /// of an old offset without changing its order.
    #[test]
    fn imported_offsets_order_as_their_old_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let constant = OldAddressOffset::Constant;
        let add = |a: OldAddressOffset, b: OldAddressOffset| {
            OldAddressOffset::Add(Box::new(a), Box::new(b))
        };
        let variable = |id| OldAddressOffset::Variable(Variable(id));
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
                values.push(OldAddressOffset::scaled_int32_node(
                    OldMachineTerm::Variable(Variable(id)),
                    width,
                ));
                for unsigned in [false, true] {
                    values.push(OldAddressOffset::scaled_int64_node(
                        OldMachineTerm::Variable(Variable(id)),
                        width,
                        unsigned,
                    ));
                }
            }
        }
        let scaled = values.len();
        for index in 0..scaled {
            if matches!(values[index], OldAddressOffset::Int32Scaled { .. }) {
                values.push(add(variable(994101), values[index].clone()));
            }
        }
        let roots: Vec<_> = values.iter().map(KernelAddressOffset::import).collect();
        for (a, left) in values.iter().zip(&roots) {
            for (b, right) in values.iter().zip(&roots) {
                assert_eq!(left.cmp(right), a.cmp(b), "{a:?} vs {b:?}");
                assert_eq!(left == right, a == b, "{a:?} vs {b:?}");
            }
        }
        let mut sorted_old = values.clone();
        sorted_old.sort();
        let mut sorted_roots = roots.clone();
        sorted_roots.sort();
        let exported: Vec<_> = sorted_roots
            .iter()
            .map(|root| KernelAddressOffset::export(root).unwrap())
            .collect();
        assert_eq!(exported, sorted_old);
    }

    /// Handles that differ only in an index annotation the old equality
    /// ignores are ordered apart, consistently with handle equality.
    #[test]
    fn annotation_distinct_offsets_order_consistently_with_handle_equality() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let roots: Vec<_> = [CScalarClass::Int, CScalarClass::Char]
            .into_iter()
            .map(|class| {
                KernelAddressOffset::import(&OldAddressOffset::scaled_int64_node(
                    OldMachineTerm::IntegerAddress(
                        Box::new(OldAddress::symbolic(Variable(994105))),
                        crate::kernel::AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    ),
                    1,
                    true,
                ))
            })
            .collect();
        assert_ne!(roots[0], roots[1]);
        assert_ne!(roots[0].cmp(&roots[1]), std::cmp::Ordering::Equal);
        assert_eq!(roots[0].cmp(&roots[1]), roots[1].cmp(&roots[0]).reverse());
    }

    #[test]
    fn offset_payload_keeps_exact_opaque_index_annotations() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let mut roots = Vec::new();
        let mut natives = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let source = OldAddressOffset::scaled_int64_node(
                OldMachineTerm::IntegerAddress(
                    Box::new(OldAddress::symbolic(Variable(994004))),
                    crate::kernel::AddressObjectClass::new(expected.clone()),
                ),
                1,
                true,
            );
            let root = KernelAddressOffset::import(&source);
            let output = KernelAddressOffset::export(&root).unwrap();
            assert_eq!(source, output);
            let OldAddressOffset::Int64Scaled { value, .. } = output else {
                panic!("scaled index")
            };
            let OldMachineTerm::IntegerAddress(_, annotation) = value.structural_value() else {
                panic!("exact address input")
            };
            assert_eq!(annotation.class(), expected);
            roots.push(root);
            natives.push(source);
        }
        assert_eq!(natives[0], natives[1]);
        assert_ne!(roots[0], roots[1]);
    }

    /// Each [`OffsetTree`] constructor, and each representation's folding
    /// `add`, builds on the old side exactly the value whose import the same
    /// call builds on the shared side, so a caller written against the trait
    /// builds the same offset whichever representation it holds.
    #[test]
    fn offset_constructors_build_the_imported_handle() {
        let _session = crate::kernel::VerificationSession::enter();
        let import = KernelAddressOffset::import;
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
            let old = OldAddressOffset::constant(value);
            assert_eq!(import(&old), SharedAddressOffset::constant(value));
            values.push(old);
        }
        for id in [994203, 994205] {
            let old = OldAddressOffset::variable(Variable(id));
            assert_eq!(import(&old), SharedAddressOffset::variable(Variable(id)));
            values.push(old);
        }
        values.push(OldAddressOffset::scaled_int64_node(
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
                    let old = OldAddressOffset::int64_scaled(index.clone(), width, unsigned);
                    assert_eq!(
                        import(&old),
                        SharedAddressOffset::int64_scaled(index.clone(), width, unsigned)
                    );
                    values.push(old);
                }
            }
        }
        for index in &indices {
            for width in [0, 1, 4, -8] {
                let old = OldAddressOffset::int32_scaled(index.clone(), width);
                assert_eq!(
                    import(&old),
                    SharedAddressOffset::int32_scaled(index.clone(), width)
                );
                values.push(old);
            }
        }
        fn extreme(offset: &OldAddressOffset) -> bool {
            match offset.view() {
                OffsetView::Constant(value) => value.unsigned_abs() > 1 << 40,
                OffsetView::Add(left, right) => extreme(left) || extreme(right),
                _ => false,
            }
        }
        let leaves = values.len();
        for left in 0..leaves {
            values.push(OldAddressOffset::raw_add(
                values[left].clone(),
                OldAddressOffset::constant(4),
            ));
        }
        for left in &values {
            for right in &values {
                let (shared_left, shared_right) = (import(left), import(right));
                assert_eq!(
                    import(&OldAddressOffset::raw_add(left.clone(), right.clone())),
                    SharedAddressOffset::raw_add(shared_left.clone(), shared_right.clone()),
                    "{left:?} + {right:?}"
                );
                // Both folds add constants unchecked, so extreme constants
                // stay out of the folding sum.
                if extreme(left) || extreme(right) {
                    continue;
                }
                assert_eq!(
                    import(&OldAddressOffset::add(left.clone(), right.clone())),
                    SharedAddressOffset::add(shared_left, shared_right),
                    "{left:?} + {right:?}"
                );
            }
        }
    }

    /// `into_add` yields a sum's two operands as written, in order, from
    /// either representation, and returns any other node unchanged.
    #[test]
    fn into_add_splits_only_a_sum_node() {
        let _session = crate::kernel::VerificationSession::enter();
        let import = KernelAddressOffset::import;
        let variable = OldAddressOffset::variable(Variable(994301));
        let zero = OldAddressOffset::constant(0);
        let sum = OldAddressOffset::raw_add(variable.clone(), zero.clone());
        assert_eq!(sum.clone().into_add(), Ok((variable.clone(), zero.clone())));
        let (left, right) = import(&sum).into_add().unwrap();
        assert_eq!((left, right), (import(&variable), import(&zero)));
        let scaled = OldAddressOffset::int32_scaled(
            SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::constant(3),
            ),
            4,
        );
        for leaf in [variable, zero, scaled] {
            assert_eq!(leaf.clone().into_add(), Err(leaf.clone()));
            assert_eq!(import(&leaf).into_add(), Err(import(&leaf)));
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
