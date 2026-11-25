//! Complete pointer payloads. Expression-bearing fields use common children;
//! proof/access metadata is retained without affecting numeric address identity.
use super::addresses::SharedAddress;
use super::*;
mod rewrite;
pub(crate) use rewrite::{PointerRewrite, PointerRewriteError};

#[derive(Clone, Debug)]
pub(crate) struct KernelSubobjectBounds {
    pub(crate) start: SharedAddress,
    pub(crate) width: KernelTerm,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct KernelPointerQualifiers {
    pub(crate) object_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) object_type_evidence: Option<ObjectTypeEvidence>,
}
/// [`ArrayObject`] with common children.
#[derive(Clone, Debug)]
pub(crate) enum KernelArrayObject {
    Allocation,
    Opaque(Option<SharedAddress>),
    Member(Arc<KernelMemberArray>),
}
/// [`MemberArray`] with common children.
#[derive(Clone, Debug)]
pub(crate) struct KernelMemberArray {
    pub(crate) bounds: Option<KernelSubobjectBounds>,
    pub(crate) within: Option<SharedAddress>,
}
impl KernelArrayObject {
    pub(in crate::kernel) fn export(&self) -> Result<ArrayObject, &'static str> {
        let owner = |owner: &SharedAddress| owner.export().map(Arc::new);
        Ok(match self {
            Self::Allocation => ArrayObject::Allocation,
            Self::Opaque(name) => ArrayObject::Opaque(name.as_ref().map(owner).transpose()?),
            Self::Member(member) => ArrayObject::Member(Arc::new(MemberArray {
                bounds: member
                    .bounds
                    .as_ref()
                    .map(|bounds| -> Result<_, &'static str> {
                        Ok(SubobjectBounds {
                            start: bounds.start.export()?,
                            width: KernelTermExport::machine(&bounds.width)?,
                        })
                    })
                    .transpose()?,
                within: member.within.as_ref().map(owner).transpose()?,
            })),
        })
    }
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
                (Some(a), Some(b)) => a.start == b.start && a.width == b.width,
                _ => false,
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
}

/// Exact producer handle. Logical equality is a separate checker operation;
/// it must not discard qualifiers or proof evidence from this payload.
///
/// Handles are interned by their complete payload ([`same_source_payload`]):
/// building the same address, provenance, array object, type and qualifiers
/// twice yields one handle, so handle identity is payload identity and two
/// kernel terms over equal payloads are one term.
///
/// [`same_source_payload`]: SharedPointer::same_source_payload
#[derive(Clone)]
pub struct SharedPointer(Arc<KernelPointer>);

/// A payload as an interner key: equality is [`SharedPointer::same_source_payload`]
/// on the payloads, and the hash covers a subset of what that compares.
struct PayloadKey(KernelPointer);
impl PartialEq for PayloadKey {
    fn eq(&self, other: &Self) -> bool {
        same_payload(&self.0, &other.0)
    }
}
impl Eq for PayloadKey {}
impl Hash for PayloadKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let value = &self.0;
        value.address.hash(state);
        value.provenance.hash(state);
        value.array.is_known().hash(state);
        value.array.owner().hash(state);
        if let Some(bounds) = value.array.bounds() {
            bounds.start.hash(state);
            bounds.width.hash(state);
        }
        value.program_type.hash(state);
        if let Some(qualifiers) = &value.qualifiers {
            qualifiers.object_class.hash(state);
            if let Some(evidence) = &qualifiers.object_type_evidence {
                evidence.class.hash(state);
                evidence.checked.hash(state);
                evidence.premise_fingerprint.hash(state);
            }
        }
    }
}
#[derive(Default)]
struct PointerInterner {
    nodes: HashMap<PayloadKey, Weak<KernelPointer>>,
    cleanup: VecDeque<KernelPointer>,
}

/// Payload equality: retained children by identity, qualifiers and
/// evidence included. Premises are compared by map identity, never walked.
fn same_payload(a: &KernelPointer, b: &KernelPointer) -> bool {
    if a.address != b.address
        || a.provenance != b.provenance
        || !a.array.same_payload(&b.array)
        || a.program_type != b.program_type
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
        static INTERNER: std::sync::OnceLock<std::sync::Mutex<PointerInterner>> =
            std::sync::OnceLock::new();
        crate::instrumentation::record_deterministic_work(1);
        let key = PayloadKey(value);
        let mut interner = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("pointer interner");
        if let Some(live) = interner.nodes.get(&key).and_then(Weak::upgrade) {
            return Self(live);
        }
        // As for offsets, bounded upkeep runs only on insertion and never
        // scans the arena.
        for _ in 0..interner.cleanup.len().min(8) {
            let stale = PayloadKey(interner.cleanup.pop_front().unwrap());
            if interner
                .nodes
                .get(&stale)
                .is_some_and(|value| value.strong_count() == 0)
            {
                interner.nodes.remove(&stale);
            } else {
                interner.cleanup.push_back(stale.0);
            }
        }
        let value = Arc::new(key.0.clone());
        interner.cleanup.push_back(key.0.clone());
        interner.nodes.insert(key, Arc::downgrade(&value));
        Self(value)
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
        self == other || same_payload(self.node(), other.node())
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
    pub(crate) fn import(value: &Pointer) -> Self {
        Self::import_addresses(value, SharedAddress::import)
    }
    pub(crate) fn import_produced(value: &Pointer) -> Self {
        Self::import_addresses(value, SharedAddress::import_produced)
    }
    fn import_addresses(value: &Pointer, address: fn(&Address) -> SharedAddress) -> Self {
        Self::new(KernelPointer {
            address: address(&value.address),
            provenance: address(&value.provenance),
            array: match value.array_object() {
                ArrayObject::Allocation => KernelArrayObject::Allocation,
                ArrayObject::Opaque(owner) => {
                    KernelArrayObject::Opaque(owner.as_deref().map(address))
                }
                ArrayObject::Member(member) => {
                    KernelArrayObject::Member(Arc::new(KernelMemberArray {
                        bounds: member.bounds.as_ref().map(|bounds| KernelSubobjectBounds {
                            start: address(&bounds.start),
                            width: KernelTerm::retained_machine_operand(
                                MachineIntegerType::Int32,
                                MachineOperandView::Legacy(&bounds.width),
                            ),
                        }),
                        within: member.within.as_deref().map(address),
                    }))
                }
            },
            program_type: value.program_type,
            qualifiers: value.qualifiers.as_ref().map(|q| {
                Arc::new(KernelPointerQualifiers {
                    object_class: q.object_class.clone(),
                    object_type_evidence: q.object_type_evidence.clone(),
                })
            }),
        })
    }
    pub(crate) fn export(&self) -> Result<Pointer, &'static str> {
        let value = self.node();
        Ok(Pointer {
            address: value.address.export()?,
            provenance: Arc::new(value.provenance.export()?),
            array: value.array.export()?,
            program_type: value.program_type,
            qualifiers: value.qualifiers.as_ref().map(|q| {
                Arc::new(PointerQualifiers {
                    object_class: q.object_class.clone(),
                    object_type_evidence: q.object_type_evidence.clone(),
                })
            }),
        })
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
    pub(crate) fn pointer_native(&self) -> Option<&ProgramValue> {
        let PureFunctionArgument::Value(value) = self.pointer_argument_native()? else {
            return None;
        };
        Some(value)
    }

    pub(crate) fn pointer_argument_native(&self) -> Option<&PureFunctionArgument> {
        if let KernelTermNode::ObservedPointer(value) = self.node() {
            return value.source().pointer_argument_native();
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
                    pointer: pointer.pointer_native().expect("array pointer").clone(),
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
            let address = value.node().address.node();
            address.base.native_atom() == &Address::null().base
                && matches!(address.offset.node(), KernelAddressOffset::Constant(0))
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
        self.with_pointer_payload(SharedPointer::import_produced(pointer))
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
    use super::*;
    use crate::kernel::effective_type::{CAccessClass, CScalarClass};
    pub(super) fn complete_source() -> Pointer {
        let class = CAccessClass::Scalar(CScalarClass::Int);
        Pointer {
            address: Address::symbolic(Variable(1000001)),
            provenance: Arc::new(Address::symbolic(Variable(1000002))),
            array: ArrayObject::from_parts(
                true,
                Some(SubobjectBounds {
                    start: Address::symbolic(Variable(1000004)),
                    width: MachineTerm::Variable(Variable(1000005)),
                }),
                Some(Arc::new(Address::symbolic(Variable(1000003)))),
            ),
            program_type: ProgramType::VoidPointer,
            qualifiers: Some(Arc::new(PointerQualifiers {
                object_class: Some(class.clone()),
                object_type_evidence: Some(ObjectTypeEvidence::parameter(class, 3, 1000006, false)),
            })),
        }
    }
    #[test]
    fn complete_payload_preserves_addresses_qualifiers_and_unchecked_evidence() {
        let source = complete_source();
        let shared = SharedPointer::import(&source);
        let output = shared.export().unwrap();
        assert_eq!(source, output);
        // Logical equality omits these; compare the exact payload separately.
        assert_eq!(output.bounds_owner(), source.bounds_owner());
        let before = source.qualifiers.as_ref().unwrap();
        let after = output.qualifiers.as_ref().unwrap();
        assert_eq!(before.object_class, after.object_class);
        assert_eq!(before.object_type_evidence, after.object_type_evidence);
        assert!(!after.object_type_evidence.as_ref().unwrap().checked);
        assert!(
            before
                .object_type_evidence
                .as_ref()
                .unwrap()
                .premises
                .ptr_eq(&after.object_type_evidence.as_ref().unwrap().premises)
        );
        assert_eq!(shared.clone(), shared);
    }
    #[test]
    fn equal_complete_payloads_share_one_handle_and_one_term() {
        let source = complete_source();
        let first = SharedPointer::import(&source);
        let second = SharedPointer::import(&source.clone());
        assert_eq!(first, second);
        assert!(Arc::ptr_eq(&first.0, &second.0));
        assert_eq!(
            KernelTerm::shared_pointer_value(first.clone()),
            KernelTerm::shared_pointer_value(second)
        );
        // A different type keeps its own handle, as do different qualifiers.
        let retyped = first.with_binding_type(ProgramType::Int32Pointer);
        assert_ne!(retyped, first);
        let mut unqualified = source;
        unqualified.qualifiers = None;
        assert_ne!(SharedPointer::import(&unqualified), first);
    }
    #[test]
    fn logical_equality_does_not_coalesce_distinct_complete_payloads() {
        let a = complete_source();
        let mut b = a.clone();
        let q = Arc::make_mut(b.qualifiers.as_mut().unwrap());
        q.object_class = Some(CAccessClass::Scalar(CScalarClass::Char));
        q.object_type_evidence = None;
        b = b.with_bounds_owner(None); // Ignored by logical equality when bounds_known.
        assert_eq!(a, b);
        let left = SharedPointer::import(&a);
        let right = SharedPointer::import(&b);
        assert_ne!(left, right);
        assert_eq!(
            left.export().unwrap().qualifiers.unwrap().object_class,
            Some(CAccessClass::Scalar(CScalarClass::Int))
        );
        assert!(
            right
                .export()
                .unwrap()
                .qualifiers
                .unwrap()
                .object_class
                .is_some()
        );
        assert!(left.node().array.owner().is_some());
        assert!(right.node().array.owner().is_none());
    }
    #[test]
    fn source_payload_names_do_not_inherit_logical_equality_omissions() {
        let source = complete_source();
        let retained = SharedPointer::import(&source);
        assert!(retained.same_source_payload(&SharedPointer::import(&source)));
        let mut variants = Vec::new();
        variants.push(source.clone().with_bounds_owner(None));
        let mut changed = source.clone();
        Arc::make_mut(changed.qualifiers.as_mut().unwrap()).object_class = None;
        variants.push(changed);
        let mut changed = source.clone();
        Arc::make_mut(changed.qualifiers.as_mut().unwrap())
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
            assert!(!retained.same_source_payload(&SharedPointer::import(&different)));
        }
    }

    #[test]
    fn absent_and_present_default_qualifiers_round_trip_exactly() {
        let mut source = complete_source();
        for qualifiers in [None, Some(Arc::new(PointerQualifiers::default()))] {
            source.qualifiers = qualifiers;
            let output = SharedPointer::import(&source).export().unwrap();
            assert_eq!(output.qualifiers.is_some(), source.qualifiers.is_some());
        }
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
