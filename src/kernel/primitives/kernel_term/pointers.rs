//! Complete pointer payloads. Expression-bearing fields use common children;
//! proof/access metadata is retained without affecting numeric address identity.
use super::addresses::SharedAddress;
use super::*;
mod rewrite;
mod written;
pub(crate) use rewrite::{PointerRewrite, PointerRewriteError};
pub(in crate::kernel) use written::ArrayObject;
use written::MachineComponent;
pub use written::{Pointer, SubobjectBounds};

/// A pointer's bounds as the kernel reads them: the start address and the
/// width term. The written view is [`SubobjectBounds`].
#[derive(Clone, Debug)]
pub(crate) struct KernelSubobjectBounds {
    pub(crate) start: SharedAddress,
    width: MachineComponent,
}
impl KernelSubobjectBounds {
    pub(crate) fn new(start: SharedAddress, width: KernelTerm) -> Self {
        Self {
            start,
            width: MachineComponent::kernel(MachineIntegerType::Int32, width),
        }
    }
    /// The width term. A written width is imported when first read.
    pub(crate) fn width(&self) -> &KernelTerm {
        self.width.kernel_term()
    }
}
#[derive(Clone, Debug, Default)]
pub(crate) struct KernelPointerQualifiers {
    pub(crate) object_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) object_type_evidence: Option<ObjectTypeEvidence>,
}
/// A pointer's array object; [`ArrayObject`] is its written view.
#[derive(Clone, Debug)]
pub(crate) enum KernelArrayObject {
    Allocation,
    Opaque(Option<SharedAddress>),
    Member(Arc<KernelMemberArray>),
}
/// A member subobject (`design/pointer-subobject-bounds.md`).
#[derive(Clone, Debug)]
pub(crate) struct KernelMemberArray {
    pub(crate) bounds: Option<KernelSubobjectBounds>,
    pub(crate) within: Option<SharedAddress>,
}
impl KernelArrayObject {
    /// As [`ArrayObject::from_parts`].
    pub(crate) fn from_parts(
        known: bool,
        bounds: Option<KernelSubobjectBounds>,
        owner: Option<SharedAddress>,
    ) -> Self {
        if !known {
            debug_assert!(bounds.is_none(), "an opaque array object has no bounds");
            return Self::Opaque(owner);
        }
        match (bounds, owner) {
            (None, None) => Self::Allocation,
            (bounds, within) => Self::Member(Arc::new(KernelMemberArray { bounds, within })),
        }
    }
    pub(crate) fn is_known(&self) -> bool {
        !matches!(self, Self::Opaque(_))
    }
    pub(crate) fn bounds(&self) -> Option<&KernelSubobjectBounds> {
        match self {
            Self::Member(member) => member.bounds.as_ref(),
            Self::Allocation | Self::Opaque(_) => None,
        }
    }
    pub(crate) fn owner(&self) -> Option<&SharedAddress> {
        match self {
            Self::Allocation => None,
            Self::Opaque(owner) => owner.as_ref(),
            Self::Member(member) => member.within.as_ref(),
        }
    }
    /// The owner where it is part of identity: an opaque array object's name.
    pub(crate) fn opaque_owner(&self) -> Option<&SharedAddress> {
        match self {
            Self::Opaque(owner) => owner.as_ref(),
            Self::Allocation | Self::Member(_) => None,
        }
    }
    pub(crate) fn with_owner(&self, owner: Option<SharedAddress>) -> Self {
        Self::from_parts(self.is_known(), self.bounds().cloned(), owner)
    }
    #[cfg(test)]
    pub(crate) fn with_bounds(&self, bounds: Option<KernelSubobjectBounds>) -> Self {
        Self::from_parts(true, bounds, self.owner().cloned())
    }
    /// Exact payload equality: retained children by identity.
    pub(crate) fn same_payload(&self, other: &Self) -> bool {
        self.is_known() == other.is_known()
            && self.owner() == other.owner()
            && match (self.bounds(), other.bounds()) {
                (None, None) => true,
                (Some(a), Some(b)) => a.start == b.start && a.width() == b.width(),
                _ => false,
            }
    }
}
/// A wide pointer's metadata (`design/rust-slice-values.md`, MiniRust's
/// `PointerMeta`): the component a pointer to an unsized type carries beside
/// its thin part. A thin pointer has none. A `dyn` vtable would be a second
/// kind; only the element count of a pointer to `[T]` or `str` exists.
#[derive(Clone, Debug)]
pub(crate) enum KernelPointerMetadata {
    /// The element count, a `UInt64` (`usize`) term.
    ElementCount(MachineComponent),
}
impl KernelPointerMetadata {
    pub(crate) fn element_count(term: KernelTerm) -> Self {
        assert_eq!(
            term.ty(),
            &KernelType::Program(ProgramType::UInt64),
            "a wide pointer's element count is a usize term"
        );
        Self::ElementCount(MachineComponent::kernel(MachineIntegerType::UInt64, term))
    }
    /// The element count term. Every metadata kind today is a count.
    pub(crate) fn count(&self) -> &KernelTerm {
        match self {
            Self::ElementCount(count) => count.kernel_term(),
        }
    }
    /// Exact payload equality: retained children by identity.
    fn same_payload(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::ElementCount(a), Self::ElementCount(b)) => a.kernel_term() == b.kernel_term(),
        }
    }
}

/// A wide pointer's metadata as one field of a derived pointer key. It
/// compares as an `Option` (thin first) and hashes nothing when thin, so a
/// thin pointer's key keeps the hash stream it had before metadata existed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PointerMetadataKey<K>(pub(crate) Option<K>);
impl<K: Hash> Hash for PointerMetadataKey<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(key) = &self.0 {
            true.hash(state);
            key.hash(state);
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct KernelPointer {
    pub(crate) address: SharedAddress,
    pub(crate) provenance: SharedAddress,
    pub(crate) array: KernelArrayObject,
    pub(crate) program_type: ProgramType,
    pub(crate) qualifiers: Option<Arc<KernelPointerQualifiers>>,
    /// `None` for a thin pointer. Shared so a thin pointer pays one word.
    pub(crate) metadata: Option<Arc<KernelPointerMetadata>>,
}
impl KernelPointer {
    fn same_metadata_payload(&self, other: &Self) -> bool {
        match (&self.metadata, &other.metadata) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b) || a.same_payload(b),
            _ => false,
        }
    }
}

/// Exact producer handle. Logical equality is a separate checker operation;
/// it must not discard qualifiers or proof evidence from this payload.
#[derive(Clone)]
pub struct SharedPointer(Arc<KernelPointer>);
impl std::fmt::Debug for SharedPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedPointer")
            .field(&Arc::as_ptr(&self.0))
            .finish()
    }
}
impl PartialEq for SharedPointer {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for SharedPointer {}
impl Hash for SharedPointer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}
impl SharedPointer {
    pub(crate) fn new(value: KernelPointer) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(Arc::new(value))
    }
    pub(crate) fn node(&self) -> &KernelPointer {
        &self.0
    }
    pub(in crate::kernel) fn retained_nonaddress_metadata(&self) -> RetainedPointerMetadata<'_> {
        let value = self.node();
        let qualifiers = value.qualifiers.as_deref();
        RetainedPointerMetadata {
            program_type: value.program_type,
            bounds_known: value.array.is_known(),
            declared_class: qualifiers.and_then(|q| q.object_class.as_ref()),
            evidence: qualifiers.and_then(|q| q.object_type_evidence.as_ref()),
        }
    }
    /// Rebind only the declaration's type. Expression children and evidence
    /// remain shared, including default qualifier shape.
    pub(crate) fn with_binding_type(&self, program_type: ProgramType) -> Self {
        let old = self.node();
        if old.program_type == program_type {
            return self.clone();
        }
        written::check_retyping(old.program_type, program_type);
        let mut value = old.clone();
        value.program_type = program_type;
        Self::new(value)
    }
    /// Whether an existing source binding retains this complete payload.
    /// This is deliberately separate from pointer equality: no address aliases,
    /// ignored qualifiers, or equivalent-but-different evidence select a name.
    /// Children use their retained identities and premises are never re-walked.
    pub(crate) fn same_source_payload(&self, other: &Self) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if self == other {
            return true;
        }
        let (a, b) = (self.node(), other.node());
        if a.address != b.address
            || a.provenance != b.provenance
            || !a.array.same_payload(&b.array)
            || a.program_type != b.program_type
            || !a.same_metadata_payload(b)
        {
            return false;
        }
        let (a, b) = match (&a.qualifiers, &b.qualifiers) {
            (None, None) => return true,
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };
        let evidence_matches = match (&a.object_type_evidence, &b.object_type_evidence) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                a.class == b.class
                    && a.checked == b.checked
                    && a.premise_fingerprint == b.premise_fingerprint
                    && a.premises.ptr_eq(&b.premises)
            }
            _ => false,
        };
        a.object_class == b.object_class && evidence_matches
    }
    /// A wide pointer's element count (`s.len()`), read from the value
    /// itself: no fact, state or class is consulted. `None` when thin.
    pub(crate) fn len(&self) -> Option<&KernelTerm> {
        self.node()
            .metadata
            .as_deref()
            .map(KernelPointerMetadata::count)
    }

    /// The wide pointer with this thin part and element count
    /// (`slice::from_raw_parts(p, n)` as a value).
    #[allow(dead_code)] // Built by step 2b's front ends (`design/rust-slice-values.md`). The thin part keeps its
    /// address, provenance, array object, type and qualifiers.
    pub(crate) fn with_element_count(&self, count: KernelTerm) -> Self {
        assert!(
            self.node().metadata.is_none(),
            "internal error: a wide pointer is built from a thin pointer"
        );
        let mut value = self.node().clone();
        value.program_type = written::widened_type(value.program_type);
        value.metadata = Some(Arc::new(KernelPointerMetadata::element_count(count)));
        Self::new(value)
    }

    /// The thin part (`s.as_ptr()`): the same address, provenance and array
    /// object with no metadata. A thin pointer is its own thin part.
    #[allow(dead_code)] // Read by step 2b's `s.as_ptr()` (`design/rust-slice-values.md`).
    pub(crate) fn as_ptr(&self) -> Self {
        if self.node().metadata.is_none() {
            return self.clone();
        }
        let mut value = self.node().clone();
        value.program_type = written::thin_part_type(value.program_type);
        value.metadata = None;
        Self::new(value)
    }

    /// Same address roles as Pointer::pointers. Widths remain separate
    /// numeric payloads; each reader retains its existing metadata policy.
    pub(crate) fn addresses(&self) -> impl Iterator<Item = &SharedAddress> {
        let value = self.node();
        std::iter::once(&value.address)
            .chain(std::iter::once(&value.provenance))
            .chain(value.array.owner())
            .chain(value.array.bounds().map(|bounds| &bounds.start))
    }
}

impl KernelTerm {
    pub(crate) fn shared_pointer_value(value: SharedPointer) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::Pointer(value),
        )
    }

    pub(crate) fn shared_pointer_call(call: KernelTerm, value: SharedPointer) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::PointerCall { call, value },
        )
    }

    pub(crate) fn shared_pointer_arithmetic(
        operation: MachineBinaryOp,
        byte_width: u32,
        operands: [KernelTerm; 2],
        value: SharedPointer,
    ) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::PointerArithmetic {
                operation,
                byte_width,
                operands,
                value,
            },
        )
    }

    pub(crate) fn pointer_payload(&self) -> Option<&SharedPointer> {
        match self.node() {
            KernelTermNode::Pointer(value)
            | KernelTermNode::PointerRead { value, .. }
            | KernelTermNode::PointerArithmetic { value, .. }
            | KernelTermNode::PointerCall { value, .. } => Some(value),
            KernelTermNode::ObservedPointer(value) => value.source().pointer_payload(),
            _ => None,
        }
    }

    /// Explicit native compatibility view; common handoffs retain only the root.
    pub(crate) fn old_pointer_value(&self) -> Option<&ProgramValue> {
        let PureFunctionArgument::Value(value) = self.old_pointer_argument()? else {
            return None;
        };
        Some(value)
    }

    pub(crate) fn old_pointer_argument(&self) -> Option<&PureFunctionArgument> {
        if let KernelTermNode::ObservedPointer(value) = self.node() {
            return value.source().old_pointer_argument();
        }
        if let KernelTermNode::ArrayReference {
            point,
            pointer,
            element_type,
        } = self.node()
        {
            return Some(self.0.argument_leaf.get_or_init(|| {
                Box::new(PureFunctionArgument::ArrayRef {
                    point: point.clone(),
                    pointer: pointer.old_pointer_value().expect("array pointer").clone(),
                    element_type: *element_type,
                })
            }));
        }
        let value = self.pointer_payload()?;
        Some(self.0.argument_leaf.get_or_init(|| {
            Box::new(PureFunctionArgument::Value(ProgramValue::Pointer(
                value.export().expect("retained pointer result"),
            )))
        }))
    }

    pub(crate) fn shared_array_reference(
        point: ProgramPoint,
        pointer: KernelTerm,
        element_type: ProgramType,
    ) -> Self {
        // A null array views no memory, so the state it was formed at would
        // only tell otherwise equal arguments apart. It is formed at no state.
        // Read the retained address in place; no native copy is made.
        let null = pointer.pointer_payload().is_some_and(|value| {
            let address = &value.node().address;
            matches!(address.atom(), AddressBase::Concrete(name) if name == "null")
                && matches!(address.offset().node(), KernelAddressOffset::Constant(0))
        });
        let point = if null {
            ProgramPoint::of_memory(&crate::kernel::SymbolicMemory::new())
        } else {
            point
        };
        Self::intern(
            KernelType::ArrayRef(element_type),
            KernelTermNode::ArrayReference {
                point,
                pointer,
                element_type,
            },
        )
    }

    /// Keep the producer structure when existing object-argument checking
    /// refines only its complete pointer payload.
    pub(crate) fn refined_pointer_argument(&self, pointer: &Pointer) -> Self {
        if let KernelTermNode::ArrayReference {
            point,
            pointer: source,
            element_type,
        } = self.node()
        {
            return Self::shared_array_reference(
                point.clone(),
                source.refined_pointer_argument(pointer),
                *element_type,
            );
        }
        self.with_pointer_payload(pointer.shared().clone())
    }

    pub(crate) fn with_pointer_payload(&self, value: SharedPointer) -> Self {
        if let Some(old) = self.pointer_payload() {
            if old.same_source_payload(&value) {
                return self.clone();
            }
            // A changed address or type is a newly formed value, not the
            // original call/read/arithmetic expression with another result.
            if old.node().address != value.node().address
                || old.node().program_type != value.node().program_type
            {
                return Self::shared_pointer_value(value);
            }
        }
        match self.node() {
            KernelTermNode::PointerCall { call, .. } => {
                Self::shared_pointer_call(call.clone(), value)
            }
            KernelTermNode::PointerRead { point, address, .. } => {
                Self::shared_pointer_read(value, point.clone(), address.clone())
            }
            KernelTermNode::PointerArithmetic {
                operation,
                byte_width,
                operands,
                ..
            } => Self::shared_pointer_arithmetic(*operation, *byte_width, operands.clone(), value),
            _ => Self::shared_pointer_value(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::written::PointerMetadata;
    use super::*;
    use crate::kernel::effective_type::{CAccessClass, CScalarClass};
    pub(super) fn complete_source() -> Pointer {
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let mut pointer = Pointer::from_parts(
            Address::symbolic(Variable(1000001)),
            Address::symbolic(Variable(1000002)),
            ArrayObject::from_parts(
                true,
                Some(SubobjectBounds::new(
                    Address::symbolic(Variable(1000004)),
                    OldMachineTerm::Variable(Variable(1000005)),
                )),
                Some(Address::symbolic(Variable(1000003))),
            ),
            ProgramType::VoidPointer,
        );
        let qualifiers = pointer.qualifiers_mut();
        qualifiers.object_class = Some(class.clone());
        qualifiers.object_type_evidence =
            Some(ObjectTypeEvidence::parameter(class, 3, 1000006, false));
        pointer
    }
    /// [`complete_source`] at an element pointer type, the thin part a
    /// slice is built from (`int32*`, widened to `[int32]`).
    pub(super) fn element_source() -> Pointer {
        complete_source().with_type(ProgramType::Int32Pointer)
    }
    /// A written pointer is its kernel handle: the kernel reads the same
    /// payload, and exporting it back shares the handle.
    #[test]
    fn complete_payload_is_the_written_pointers_handle() {
        let source = complete_source();
        let shared = source.shared().clone();
        let output = shared.export().unwrap();
        assert_eq!(output.shared(), source.shared());
        assert_eq!(source, output);
        assert!(shared.node().array.owner().is_some());
        let bounds = shared.node().array.bounds().unwrap();
        assert_eq!(
            bounds.width(),
            &KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Old(&OldMachineTerm::Variable(Variable(1000005))),
            )
        );
        let qualifiers = shared.node().qualifiers.as_ref().unwrap();
        assert_eq!(
            qualifiers.object_class,
            Some(CAccessClass::Scalar(CScalarClass::Int))
        );
        assert!(!qualifiers.object_type_evidence.as_ref().unwrap().checked);
        assert_eq!(shared.clone(), shared);
    }
    /// A kernel-built handle with a kernel width exports its written width.
    #[test]
    fn kernel_bounds_export_their_written_width() {
        let source = complete_source();
        let value = source.shared().node();
        let start = value.array.bounds().unwrap().start.clone();
        let width = KernelTerm::retained_machine_operand(
            MachineIntegerType::Int32,
            MachineOperandView::Old(&OldMachineTerm::constant(4)),
        );
        let built = SharedPointer::new(KernelPointer {
            array: KernelArrayObject::from_parts(
                true,
                Some(KernelSubobjectBounds::new(start, width)),
                None,
            ),
            ..value.clone()
        });
        let written = built.export().unwrap();
        assert_eq!(written.shared(), &built);
        assert_eq!(
            written.bounds().unwrap().width(),
            &OldMachineTerm::constant(4)
        );
        assert_eq!(
            written,
            source.with_bounds(Some(SubobjectBounds::constant(
                Address::symbolic(Variable(1000004)),
                4
            )))
        );
    }
    #[test]
    fn logical_equality_does_not_coalesce_distinct_complete_payloads() {
        let a = complete_source();
        let mut b = a.clone();
        let q = b.qualifiers_mut();
        q.object_class = Some(CAccessClass::Scalar(CScalarClass::Char));
        q.object_type_evidence = None;
        b = b.with_bounds_owner(None); // Ignored by logical equality when bounds_known.
        assert_eq!(a, b);
        let left = a.shared().clone();
        let right = b.shared().clone();
        assert_ne!(left, right);
        assert_eq!(
            a.qualifiers().unwrap().object_class,
            Some(CAccessClass::Scalar(CScalarClass::Int))
        );
        assert!(b.qualifiers().unwrap().object_class.is_some());
        assert!(left.node().array.owner().is_some());
        assert!(right.node().array.owner().is_none());
    }
    #[test]
    fn source_payload_names_do_not_inherit_logical_equality_omissions() {
        let source = complete_source();
        let retained = source.shared().clone();
        assert!(retained.same_source_payload(source.shared()));
        let mut variants = Vec::new();
        variants.push(source.clone().with_bounds_owner(None));
        let mut changed = source.clone();
        changed.qualifiers_mut().object_class = None;
        variants.push(changed);
        let mut changed = source.clone();
        changed
            .qualifiers_mut()
            .object_type_evidence
            .as_mut()
            .unwrap()
            .checked = true;
        variants.push(changed);
        for different in variants {
            assert_eq!(
                source, different,
                "these distinctions are not logical pointer identity"
            );
            assert!(!retained.same_source_payload(different.shared()));
        }
        // Changing a copy never changes the handle it was copied from.
        assert!(retained.same_source_payload(source.shared()));
        assert!(
            retained
                .node()
                .qualifiers
                .as_ref()
                .unwrap()
                .object_class
                .is_some()
        );
    }

    fn count(id: u64) -> OldMachineTerm {
        OldMachineTerm::Variable(Variable(id))
    }
    fn hash_of(value: &impl Hash) -> u64 {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }

    /// Fact-set treap priorities are content hashes, so a thin pointer's
    /// hash stream, order and equality are the identity tuple's as before
    /// metadata existed.
    #[test]
    fn thin_pointer_identity_stream_is_unchanged() {
        let thin = complete_source();
        let array = thin.array_object();
        let tuple = (
            thin.address(),
            thin.provenance(),
            array.is_known(),
            array.opaque_owner(),
            array.bounds(),
        );
        assert_eq!(hash_of(&thin), hash_of(&tuple));
        assert!(thin.metadata().is_none() && thin.len().is_none());
        assert!(!format!("{thin:?}").contains("metadata"));
        let other = thin
            .clone()
            .with_address(Address::symbolic(Variable(1000101)));
        let other_tuple = (
            other.address(),
            other.provenance(),
            array.is_known(),
            array.opaque_owner(),
            array.bounds(),
        );
        assert_eq!(thin.cmp(&other), tuple.cmp(&other_tuple));
        assert_eq!(thin.as_ptr(), thin);
        assert!(thin.as_ptr().shared() == thin.shared());
    }

    #[test]
    fn wide_pointer_identity_adds_the_element_count() {
        let thin = element_source();
        let wide = |id| thin.clone().with_element_count(count(id));
        let (a, same, b) = (wide(1000102), wide(1000102), wide(1000103));
        assert_eq!(a, same);
        assert_eq!(hash_of(&a), hash_of(&same));
        assert_ne!(a, b);
        assert_ne!(a, thin);
        assert_ne!(hash_of(&a), hash_of(&thin));
        assert_ne!(hash_of(&a), hash_of(&b));
        assert_eq!(thin.cmp(&a), std::cmp::Ordering::Less);
        assert_eq!(a.cmp(&b), count(1000102).cmp(&count(1000103)));
        // The provenance is unchanged; only the metadata tells them apart.
        assert!(a.same_provenance_as(&b) && !a.same_metadata_as(&b));
        assert!(format!("{a:?}").contains("metadata"));
    }

    /// `s.as_ptr()` and `s.len()` are components of the value: read from it
    /// without any fact, and the thin part is the pointer it was built from.
    #[test]
    fn wide_pointer_components_read_in_place() {
        let _session = crate::kernel::VerificationSession::enter();
        let thin = element_source();
        let wide = thin.clone().with_element_count(count(1000104));
        assert_eq!(wide.len(), Some(&count(1000104)));
        assert_eq!(
            wide.metadata(),
            Some(PointerMetadata::ElementCount(&count(1000104)))
        );
        assert_eq!(wide.as_ptr(), thin);
        assert_eq!(wide.address(), thin.address());
        assert_eq!(wide.provenance(), thin.provenance());
        assert_eq!(wide.array_object(), thin.array_object());
        assert!(wide.qualifiers().is_some());
        // Kernel construction from the thin handle and a usize term.
        let n = KernelTerm::retained_machine_operand(
            MachineIntegerType::UInt64,
            MachineOperandView::Old(&count(1000104)),
        );
        let built = thin.shared().with_element_count(n.clone());
        assert_eq!(built.len(), Some(&n));
        assert_eq!(wide.shared().len(), Some(&n));
        assert!(built.as_ptr().len().is_none());
        assert!(built.as_ptr().same_source_payload(thin.shared()));
        let exported = built.export().unwrap();
        assert_eq!(exported, wide);
        assert!(built.same_source_payload(wide.shared()));
        let other = thin
            .shared()
            .with_element_count(KernelTerm::retained_machine_operand(
                MachineIntegerType::UInt64,
                MachineOperandView::Old(&count(1000105)),
            ));
        assert!(!built.same_source_payload(&other));
        assert!(!built.same_source_payload(thin.shared()));
    }

    #[test]
    #[should_panic(expected = "a wide pointer is built from a thin pointer")]
    fn a_wide_pointer_is_not_widened_again() {
        let wide = element_source().with_element_count(count(1000106));
        let _ = wide.with_element_count(count(1000107));
    }

    #[test]
    #[should_panic(expected = "has no form for a wide pointer's metadata yet")]
    fn thin_only_operations_refuse_a_wide_pointer() {
        let wide = element_source().with_element_count(count(1000108));
        complete_source().expect_thin("a thin consumer");
        wide.expect_thin("a thin consumer");
    }

    /// Substitution and variable collection reach the count term, through
    /// the written view and the kernel rewrite alike.
    #[test]
    fn substitution_and_collection_reach_the_element_count() {
        let _session = crate::kernel::VerificationSession::enter();
        let (from, to) = (Variable(1000110), Variable(1000111));
        let wide = element_source().with_element_count(count(from.0));
        let substituted = wide.map_pointers(Address::clone, |term| {
            crate::kernel::reasoning::substitute_bitvector_variable(
                term,
                from,
                &OldMachineTerm::Variable(to),
            )
        });
        assert_eq!(substituted.len(), Some(&count(to.0)));
        assert_eq!(substituted.as_ptr(), wide.as_ptr());
        let mut thin_calls = 0;
        let thin = complete_source().map_pointers(Address::clone, |term| {
            thin_calls += 1;
            term.clone()
        });
        assert_eq!((thin_calls, thin), (0, complete_source()));
        assert!(
            wide.try_map_pointers(|address| Some(address.clone()), |_| None)
                .is_none(),
            "a refused count refuses the value"
        );
        // Respelling physical addresses keeps the provenance; the count is
        // respelled by the caller's machine-term map, as the scalars beside
        // the value are (canonical reads, an address-equality rewrite), and
        // a thin pointer never calls it.
        assert_eq!(
            wide.map_addresses(Address::clone, OldMachineTerm::clone),
            wide
        );
        let respelled = wide.map_addresses(Address::clone, |_| count(to.0));
        assert_eq!(respelled.len(), Some(&count(to.0)));
        assert_eq!(respelled.as_ptr(), wide.as_ptr());
        assert_eq!(respelled.program_type(), wide.program_type());
        let mut thin_respellings = 0;
        complete_source().map_addresses(Address::clone, |term| {
            thin_respellings += 1;
            term.clone()
        });
        assert_eq!(thin_respellings, 0);
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::collect_program_value_bitvector_variables(
            &ProgramValue::Pointer(wide.clone()),
            &mut variables,
        );
        assert!(variables.contains(&from), "{variables:?}");
        struct Numeric(KernelTerm, KernelTerm);
        impl PointerRewrite for Numeric {
            type Error = ();
            fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, ()> {
                Ok(if value == &self.0 {
                    self.1.clone()
                } else {
                    value.clone()
                })
            }
        }
        let kernel = |id: u64| {
            KernelTerm::retained_machine_operand(
                MachineIntegerType::UInt64,
                MachineOperandView::Old(&count(id)),
            )
        };
        let rewritten = wide
            .shared()
            .try_rewrite(&mut Numeric(kernel(from.0), kernel(to.0)))
            .unwrap();
        assert_eq!(rewritten.len(), Some(&kernel(to.0)));
        assert_eq!(rewritten.export().unwrap(), substituted);
        let unchanged = wide
            .shared()
            .try_rewrite(&mut Numeric(kernel(to.0), kernel(from.0)))
            .unwrap();
        assert_eq!(
            &unchanged,
            wide.shared(),
            "an unchanged count keeps the handle"
        );
    }

    #[test]
    fn absent_and_present_default_qualifiers_stay_distinct() {
        let source = complete_source();
        let absent = Pointer::from_parts(
            source.address().clone(),
            source.provenance().clone(),
            source.array_object().clone(),
            source.program_type(),
        );
        let mut present = absent.clone();
        present.qualifiers_mut();
        assert!(absent.qualifiers().is_none());
        assert!(present.qualifiers().is_some());
        assert!(!absent.shared().same_source_payload(present.shared()));
        assert_eq!(absent, present);
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/pointers.rs");
}

impl KernelTermImport {
    pub(crate) fn pointer_call(
        &mut self,
        application: &SharedPureApplication,
        retained: Vec<Option<KernelTerm>>,
        value: SharedPointer,
    ) -> KernelTerm {
        let arguments = application
            .arguments()
            .iter()
            .zip(retained)
            .enumerate()
            .map(|(index, (_, retained))| {
                retained.unwrap_or_else(|| {
                    if let Some(root) = application.common_argument(index) {
                        root
                    } else {
                        KernelTerm::written_call_argument(application, index)
                    }
                })
            })
            .collect();
        let call = KernelTerm::checked_call(
            KernelType::Program(value.node().program_type),
            application.name().into(),
            arguments,
        );
        KernelTerm::shared_pointer_call(call, value)
    }
}
