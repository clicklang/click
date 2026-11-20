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
    pub(crate) volatile: bool,
    pub(crate) constant: bool,
    pub(crate) bounds: Option<KernelSubobjectBounds>,
    pub(crate) bounds_known: bool,
    pub(crate) object_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) object_type_evidence: Option<ObjectTypeEvidence>,
}
#[derive(Clone, Debug)]
pub(crate) struct KernelPointer {
    pub(crate) address: SharedAddress,
    pub(crate) provenance: SharedAddress,
    pub(crate) bounds_owner: Option<SharedAddress>,
    pub(crate) program_type: ProgramType,
    pub(crate) qualifiers: Option<Arc<KernelPointerQualifiers>>,
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
            volatile: qualifiers.is_some_and(|q| q.volatile),
            constant: qualifiers.is_some_and(|q| q.constant),
            bounds_known: qualifiers.is_some_and(|q| q.bounds_known),
            declared_class: qualifiers.and_then(|q| q.object_class.as_ref()),
            evidence: qualifiers.and_then(|q| q.object_type_evidence.as_ref()),
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
            || a.provenance != b.provenance
            || a.bounds_owner != b.bounds_owner
            || a.program_type != b.program_type
        {
            return false;
        }
        let (a, b) = match (&a.qualifiers, &b.qualifiers) {
            (None, None) => return true,
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };
        let bounds_match = match (&a.bounds, &b.bounds) {
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
            && a.bounds_known == b.bounds_known
            && a.object_class == b.object_class
            && bounds_match
            && evidence_matches
    }
    /// Same address roles as Pointer::pointers. Widths remain separate
    /// numeric payloads; each reader retains its existing metadata policy.
    pub(crate) fn addresses(&self) -> impl Iterator<Item = &SharedAddress> {
        let value = self.node();
        std::iter::once(&value.address)
            .chain(std::iter::once(&value.provenance))
            .chain(value.bounds_owner.as_ref())
            .chain(
                value
                    .qualifiers
                    .as_ref()
                    .and_then(|q| q.bounds.as_ref())
                    .map(|bounds| &bounds.start),
            )
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
            bounds_owner: value.bounds_owner.as_ref().map(|pointer| address(pointer)),
            program_type: value.program_type,
            qualifiers: value.qualifiers.as_ref().map(|q| {
                Arc::new(KernelPointerQualifiers {
                    volatile: q.volatile,
                    constant: q.constant,
                    bounds: q.bounds.as_ref().map(|bounds| KernelSubobjectBounds {
                        start: address(&bounds.start),
                        width: KernelTerm::retained_machine_operand(
                            MachineIntegerType::Int32,
                            MachineOperandView::Legacy(&bounds.width),
                        ),
                    }),
                    bounds_known: q.bounds_known,
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
            bounds_owner: value
                .bounds_owner
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
                        bounds: q
                            .bounds
                            .as_ref()
                            .map(|bounds| -> Result<_, &'static str> {
                                Ok(SubobjectBounds {
                                    start: bounds.start.export()?,
                                    width: KernelTermExport::machine(&bounds.width)?,
                                })
                            })
                            .transpose()?,
                        bounds_known: q.bounds_known,
                        object_class: q.object_class.clone(),
                        object_type_evidence: q.object_type_evidence.clone(),
                    }))
                })
                .transpose()?,
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
            bounds_owner: Some(Arc::new(Address::symbolic(Variable(1000003)))),
            program_type: ProgramType::VoidPointer,
            qualifiers: Some(Arc::new(PointerQualifiers {
                volatile: true,
                constant: true,
                bounds: Some(SubobjectBounds {
                    start: Address::symbolic(Variable(1000004)),
                    width: MachineTerm::Variable(Variable(1000005)),
                }),
                bounds_known: true,
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
        assert_eq!(output.bounds_owner, source.bounds_owner);
        let before = source.qualifiers.as_ref().unwrap();
        let after = output.qualifiers.as_ref().unwrap();
        assert_eq!(before.constant, after.constant);
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
        b.bounds_owner = None; // Ignored by logical equality when bounds_known.
        assert_eq!(a, b);
        let left = SharedPointer::import(&a);
        let right = SharedPointer::import(&b);
        assert_ne!(left, right);
        assert!(left.export().unwrap().qualifiers.unwrap().constant);
        assert!(!right.export().unwrap().qualifiers.unwrap().constant);
        assert!(left.node().bounds_owner.is_some());
        assert!(right.node().bounds_owner.is_none());
    }
    #[test]
    fn source_payload_names_do_not_inherit_logical_equality_omissions() {
        let source = complete_source();
        let retained = SharedPointer::import(&source);
        assert!(retained.same_source_payload(&SharedPointer::import(&source)));
        let mut variants = vec![source.clone().with_pointee_constant(false)];
        let mut changed = source.clone();
        changed.bounds_owner = None;
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
