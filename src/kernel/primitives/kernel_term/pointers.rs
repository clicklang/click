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
#[derive(Clone, Debug)]
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
pub(crate) struct SharedPointerValue(Arc<KernelPointerValue>);
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
        Self::new(KernelPointerValue {
            address: SharedPointerAddress::import(&value.pointer),
            designation: SharedPointerAddress::import(&value.designation),
            opaque_extent: value
                .opaque_extent
                .as_ref()
                .map(|address| SharedPointerAddress::import(address)),
            program_type: value.program_type,
            qualifiers: value.qualifiers.as_ref().map(|q| {
                Arc::new(KernelPointerQualifiers {
                    volatile: q.volatile,
                    constant: q.constant,
                    extent: q.extent.as_ref().map(|extent| KernelSubobjectExtent {
                        start: SharedPointerAddress::import(&extent.start),
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
