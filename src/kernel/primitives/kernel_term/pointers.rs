//! Complete pointer payloads. Expression-bearing fields use common children;
//! proof/access metadata is retained without affecting numeric address identity.
use super::addresses::SharedPointerAddress;
use super::*;
mod rewrite;
pub(crate) use rewrite::{PointerRewrite, PointerRewriteError};

#[derive(Clone, Debug)]
pub(crate) struct KernelSubobjectExtent {
    pub(crate) start: SharedPointerAddress,
    pub(crate) width: KernelTerm,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct KernelPointerQualifiers {
    pub(crate) volatile: bool,
    pub(crate) constant: bool,
    pub(crate) extent: Option<KernelSubobjectExtent>,
    pub(crate) extent_known: bool,
    pub(crate) object_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) object_type_evidence: Option<ObjectTypeEvidence>,
    pub(in crate::kernel) local_reference: Option<crate::kernel::loans::LocalScalarReference>,
}
#[derive(Clone, Debug)]
pub(crate) struct KernelPointerValue {
    pub(crate) address: SharedPointerAddress,
    pub(crate) designation: SharedPointerAddress,
    pub(crate) opaque_extent: Option<SharedPointerAddress>,
    pub(crate) program_type: ProgramType,
    pub(crate) qualifiers: Option<Arc<KernelPointerQualifiers>>,
}

/// Exact producer handle. Logical equality is a separate checker operation;
/// it must not discard qualifiers or proof evidence from this payload.
#[derive(Clone)]
pub struct SharedPointerValue(Arc<KernelPointerValue>);
impl std::fmt::Debug for SharedPointerValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedPointerValue")
            .field(&Arc::as_ptr(&self.0))
            .finish()
    }
}
impl PartialEq for SharedPointerValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for SharedPointerValue {}
impl Hash for SharedPointerValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}
impl SharedPointerValue {
    pub(crate) fn new(value: KernelPointerValue) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(Arc::new(value))
    }
    pub(crate) fn node(&self) -> &KernelPointerValue {
        &self.0
    }
    pub(in crate::kernel) fn retained_nonaddress_metadata(&self) -> RetainedPointerMetadata<'_> {
        let value = self.node();
        let qualifiers = value.qualifiers.as_deref();
        RetainedPointerMetadata {
            program_type: value.program_type,
            volatile: qualifiers.is_some_and(|q| q.volatile),
            constant: qualifiers.is_some_and(|q| q.constant),
            extent_known: qualifiers.is_some_and(|q| q.extent_known),
            declared_class: qualifiers.and_then(|q| q.object_class.as_ref()),
            evidence: qualifiers.and_then(|q| q.object_type_evidence.as_ref()),
            local_reference: qualifiers.and_then(|q| q.local_reference.as_ref()),
        }
    }
    /// Rebind only the declaration's type and cv qualifiers. Expression
    /// children and evidence remain shared, including default qualifier shape.
    pub(crate) fn with_binding_type_and_qualifiers(
        &self,
        program_type: ProgramType,
        volatile: bool,
        constant: bool,
    ) -> Self {
        let old = self.node();
        let old_volatile = old.qualifiers.as_ref().is_some_and(|q| q.volatile);
        let old_constant = old.qualifiers.as_ref().is_some_and(|q| q.constant);
        if old.program_type == program_type && old_volatile == volatile && old_constant == constant
        {
            return self.clone();
        }
        let mut value = old.clone();
        value.program_type = program_type;
        if old_volatile != volatile || old_constant != constant {
            let qualifiers = Arc::make_mut(value.qualifiers.get_or_insert_with(Default::default));
            qualifiers.volatile = volatile;
            qualifiers.constant = constant;
        }
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
            || a.designation != b.designation
            || a.opaque_extent != b.opaque_extent
            || a.program_type != b.program_type
        {
            return false;
        }
        let (a, b) = match (&a.qualifiers, &b.qualifiers) {
            (None, None) => return true,
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };
        let extent_matches = match (&a.extent, &b.extent) {
            (None, None) => true,
            (Some(a), Some(b)) => a.start == b.start && a.width == b.width,
            _ => false,
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
        a.volatile == b.volatile
            && a.constant == b.constant
            && a.extent_known == b.extent_known
            && a.object_class == b.object_class
            && a.local_reference == b.local_reference
            && extent_matches
            && evidence_matches
    }
    /// Same address roles as PointerValue::pointers. Widths remain separate
    /// numeric payloads; each reader retains its existing metadata policy.
    pub(crate) fn addresses(&self) -> impl Iterator<Item = &SharedPointerAddress> {
        let value = self.node();
        std::iter::once(&value.address)
            .chain(std::iter::once(&value.designation))
            .chain(value.opaque_extent.as_ref())
            .chain(
                value
                    .qualifiers
                    .as_ref()
                    .and_then(|q| q.extent.as_ref())
                    .map(|extent| &extent.start),
            )
    }
    pub(crate) fn import(value: &PointerValue) -> Self {
        Self::import_addresses(value, SharedPointerAddress::import)
    }
    pub(crate) fn import_produced(value: &PointerValue) -> Self {
        Self::import_addresses(value, SharedPointerAddress::import_produced)
    }
    fn import_addresses(
        value: &PointerValue,
        address: fn(&Pointer) -> SharedPointerAddress,
    ) -> Self {
        Self::new(KernelPointerValue {
            address: address(&value.pointer),
            designation: address(&value.designation),
            opaque_extent: value.opaque_extent.as_ref().map(|pointer| address(pointer)),
            program_type: value.program_type,
            qualifiers: value.qualifiers.as_ref().map(|q| {
                Arc::new(KernelPointerQualifiers {
                    volatile: q.volatile,
                    constant: q.constant,
                    extent: q.extent.as_ref().map(|extent| KernelSubobjectExtent {
                        start: address(&extent.start),
                        width: KernelTerm::retained_machine_operand(
                            MachineIntegerType::Int32,
                            MachineOperandView::Legacy(&extent.width),
                        ),
                    }),
                    extent_known: q.extent_known,
                    object_class: q.object_class.clone(),
                    object_type_evidence: q.object_type_evidence.clone(),
                    local_reference: q.local_reference,
                })
            }),
        })
    }
    pub(crate) fn export(&self) -> Result<PointerValue, &'static str> {
        let value = self.node();
        Ok(PointerValue {
            pointer: value.address.export()?,
            designation: Arc::new(value.designation.export()?),
            opaque_extent: value
                .opaque_extent
                .as_ref()
                .map(|address| address.export().map(Arc::new))
                .transpose()?,
            program_type: value.program_type,
            qualifiers: value
                .qualifiers
                .as_ref()
                .map(|q| -> Result<_, &'static str> {
                    Ok(Arc::new(PointerQualifiers {
                        volatile: q.volatile,
                        constant: q.constant,
                        extent: q
                            .extent
                            .as_ref()
                            .map(|extent| -> Result<_, &'static str> {
                                Ok(SubobjectExtent {
                                    start: extent.start.export()?,
                                    width: KernelTermExport::machine(&extent.width)?,
                                })
                            })
                            .transpose()?,
                        extent_known: q.extent_known,
                        object_class: q.object_class.clone(),
                        object_type_evidence: q.object_type_evidence.clone(),
                        local_reference: q.local_reference,
                    }))
                })
                .transpose()?,
        })
    }
}

impl KernelTerm {
    pub(crate) fn shared_pointer_value(value: SharedPointerValue) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::PointerValue(value),
        )
    }

    pub(crate) fn shared_pointer_call(call: KernelTerm, value: SharedPointerValue) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::PointerCall { call, value },
        )
    }

    pub(crate) fn shared_pointer_arithmetic(
        operation: MachineBinaryOp,
        byte_width: u32,
        operands: [KernelTerm; 2],
        value: SharedPointerValue,
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

    pub(crate) fn pointer_payload(&self) -> Option<&SharedPointerValue> {
        match self.node() {
            KernelTermNode::PointerValue(value)
            | KernelTermNode::PointerRead { value, .. }
            | KernelTermNode::PointerArithmetic { value, .. }
            | KernelTermNode::PointerCall { value, .. } => Some(value),
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
        if let KernelTermNode::ArrayReference {
            memory,
            pointer,
            element_type,
        } = self.node()
        {
            return Some(self.0.argument_leaf.get_or_init(|| {
                Box::new(PureFunctionArgument::ArrayRef {
                    memory: memory.memory().clone(),
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
        memory: SharedMemory,
        pointer: KernelTerm,
        element_type: ProgramType,
    ) -> Self {
        Self::intern(
            KernelType::ArrayRef(element_type),
            KernelTermNode::ArrayReference {
                memory,
                pointer,
                element_type,
            },
        )
    }

    /// Keep the producer structure when existing object-argument checking
    /// refines only its complete pointer payload.
    pub(crate) fn refined_pointer_argument(&self, pointer: &PointerValue) -> Self {
        if let KernelTermNode::ArrayReference {
            memory,
            pointer: source,
            element_type,
        } = self.node()
        {
            return Self::shared_array_reference(
                memory.clone(),
                source.refined_pointer_argument(pointer),
                *element_type,
            );
        }
        self.with_pointer_payload(SharedPointerValue::import_produced(pointer))
    }

    pub(crate) fn with_pointer_payload(&self, value: SharedPointerValue) -> Self {
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
            KernelTermNode::PointerRead {
                memory, address, ..
            } => Self::shared_pointer_read(value, memory.clone(), address.clone()),
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
    pub(super) fn complete_source() -> PointerValue {
        let class = CAccessClass::Scalar(CScalarClass::Int);
        PointerValue {
            pointer: Pointer::symbolic(Variable(1000001)),
            designation: Arc::new(Pointer::symbolic(Variable(1000002))),
            opaque_extent: Some(Arc::new(Pointer::symbolic(Variable(1000003)))),
            program_type: ProgramType::VoidPointer,
            qualifiers: Some(Arc::new(PointerQualifiers {
                volatile: true,
                constant: true,
                extent: Some(SubobjectExtent {
                    start: Pointer::symbolic(Variable(1000004)),
                    width: MachineTerm::Variable(Variable(1000005)),
                }),
                extent_known: true,
                object_class: Some(class.clone()),
                object_type_evidence: Some(ObjectTypeEvidence::parameter(class, 3, 1000006, false)),
                local_reference: Some(
                    crate::kernel::loans::LocalScalarReference::fresh_for_payload_test(),
                ),
            })),
        }
    }
    #[test]
    fn complete_payload_preserves_addresses_qualifiers_and_unchecked_evidence() {
        let source = complete_source();
        let shared = SharedPointerValue::import(&source);
        let output = shared.export().unwrap();
        assert_eq!(source, output);
        // Logical equality omits these; compare the exact payload separately.
        assert_eq!(output.opaque_extent, source.opaque_extent);
        let before = source.qualifiers.as_ref().unwrap();
        let after = output.qualifiers.as_ref().unwrap();
        assert_eq!(before.constant, after.constant);
        assert_eq!(before.local_reference, after.local_reference);
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
    fn logical_equality_does_not_coalesce_distinct_complete_payloads() {
        let a = complete_source();
        let mut b = a.clone();
        let q = Arc::make_mut(b.qualifiers.as_mut().unwrap());
        q.constant = false;
        q.object_class = Some(CAccessClass::Scalar(CScalarClass::Char));
        q.object_type_evidence = None;
        b.opaque_extent = None; // Ignored by logical equality when extent_known.
        assert_eq!(a, b);
        let left = SharedPointerValue::import(&a);
        let right = SharedPointerValue::import(&b);
        assert_ne!(left, right);
        assert!(left.export().unwrap().qualifiers.unwrap().constant);
        assert!(!right.export().unwrap().qualifiers.unwrap().constant);
        assert!(left.node().opaque_extent.is_some());
        assert!(right.node().opaque_extent.is_none());
    }
    #[test]
    fn source_payload_names_do_not_inherit_logical_equality_omissions() {
        let source = complete_source();
        let retained = SharedPointerValue::import(&source);
        assert!(retained.same_source_payload(&SharedPointerValue::import(&source)));
        let mut variants = vec![source.clone().with_pointee_constant(false)];
        let mut changed = source.clone();
        changed.opaque_extent = None;
        variants.push(changed);
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
            assert!(!retained.same_source_payload(&SharedPointerValue::import(&different)));
        }
    }

    #[test]
    fn absent_and_present_default_qualifiers_round_trip_exactly() {
        let mut source = complete_source();
        for qualifiers in [None, Some(Arc::new(PointerQualifiers::default()))] {
            source.qualifiers = qualifiers;
            let output = SharedPointerValue::import(&source).export().unwrap();
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
        value: SharedPointerValue,
    ) -> KernelTerm {
        let arguments = application
            .arguments()
            .iter()
            .zip(retained)
            .enumerate()
            .map(|(index, (argument, retained))| {
                retained.unwrap_or_else(|| {
                    if let Some(root) = application.common_argument(index) {
                        root
                    } else {
                        KernelTerm::legacy_at(
                            argument.clone(),
                            LegacyIdentity::ExactApplicationArgument {
                                application: application.clone(),
                                payload: application.payload_id(),
                                index,
                            },
                        )
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
