//! Numeric address observations retain prepared addresses and exact annotations.
use super::*;

use crate::kernel::execution_value::storage_keys::{PointerStorageKey, pointer_for_root};

#[derive(Clone, Debug)]
pub struct KernelObservedPointer {
    source: KernelTerm,
    identity: PointerObservationIdentity,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum PointerObservationIdentity {
    Pointer(PointerStorageKey),
    Array {
        pointer: PointerStorageKey,
        point: ProgramPoint,
    },
}

impl KernelObservedPointer {
    pub fn source(&self) -> &KernelTerm {
        &self.source
    }
}
impl PartialEq for KernelObservedPointer {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for KernelObservedPointer {}
impl Hash for KernelObservedPointer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

impl KernelTerm {
    pub(in crate::kernel::primitives) fn observe_pointer_argument(source: &KernelTerm) -> Self {
        let identity = match source.node() {
            KernelTermNode::ArrayReference { point, pointer, .. } => {
                PointerObservationIdentity::Array {
                    pointer: pointer_for_root(pointer),
                    point: point.clone(),
                }
            }
            _ => PointerObservationIdentity::Pointer(pointer_for_root(source)),
        };
        Self::intern(
            source.ty().clone(),
            KernelTermNode::ObservedPointer(KernelObservedPointer {
                source: source.clone(),
                identity,
            }),
        )
    }

    pub(crate) fn shared_pointer_address_observation(
        format: MachineIntegerType,
        address: SharedAddress,
        object_class: AddressObjectClass,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::IntegerAddress {
                address,
                object_class: object_class.class(),
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pointer_argument_observations_keep_retained_sources() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = OldPointer::new(
            Address::symbolic(Variable(1024002)),
            ProgramType::Int32Pointer,
        );
        let source = |class| {
            KernelTerm::shared_pointer_value(SharedPointer::import(
                &pointer
                    .clone()
                    .with_declared_object_class(Some(CAccessClass::Scalar(class))),
            ))
        };
        let first = source(CScalarClass::Int);
        let second = source(CScalarClass::Char);
        assert_ne!(first, second);
        let key = KernelTerm::observe_pointer_argument(&first);
        assert_eq!(key, KernelTerm::observe_pointer_argument(&second));
        let KernelTermNode::ObservedPointer(value) = key.node() else {
            panic!("pointer observation");
        };
        assert_eq!(value.source(), &first);
        assert!(!first.has_cached_native_argument());
        assert!(!second.has_cached_native_argument());

        let a = crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new());
        let b = crate::kernel::ProgramPoint::of_memory(
            &SymbolicMemory::new().with_block("local:opaque-array", 4),
        );
        let array =
            |point| KernelTerm::shared_array_reference(point, first.clone(), ProgramType::Int32);
        let first_array = array(a);
        let second_array = array(b);
        assert_ne!(
            KernelTerm::observe_pointer_argument(&first_array),
            KernelTerm::observe_pointer_argument(&second_array),
        );
        assert!(!first_array.has_cached_native_argument());
        assert!(!second_array.has_cached_native_argument());
    }

    #[test]
    fn address_observation_identity_keeps_exact_object_annotations() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(1024001));
        let mut roots = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let native = MachineTerm::IntegerAddress(
                Box::new(address.clone()),
                AddressObjectClass::new(expected.clone()),
            );
            let root = KernelTermImport::default().machine(MachineIntegerType::UInt64, &native);
            let MachineTerm::IntegerAddress(_, actual) = KernelTermExport::machine(&root).unwrap()
            else {
                panic!("address");
            };
            assert_eq!(actual.class(), expected);
            roots.push(root);
        }
        assert_ne!(roots[0], roots[1], "exact producer payload differs");
        assert_eq!(
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::UInt64, roots[0].clone()),
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::UInt64, roots[1].clone()),
            "numeric observations ignore object annotations"
        );
        assert_eq!(
            KernelTermExport::machine(&roots[0]).unwrap(),
            KernelTermExport::machine(&roots[1]).unwrap(),
            "native numeric equality ignores annotations"
        );
    }
}
