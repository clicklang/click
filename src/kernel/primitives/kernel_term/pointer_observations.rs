//! Numeric address observations retain prepared addresses and exact annotations.
use super::*;

impl KernelTerm {
    pub(crate) fn shared_pointer_address_observation(
        format: MachineIntegerType,
        address: SharedAddress,
        object_class: AddressObjectClass,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::PointerAddress {
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
    fn address_observation_identity_keeps_exact_object_annotations() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(1024001));
        let mut roots = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let native = MachineTerm::PointerAddress(
                Box::new(address.clone()),
                AddressObjectClass::new(expected.clone()),
            );
            let root = KernelTermImport::default().machine(MachineIntegerType::UInt64, &native);
            let MachineTerm::PointerAddress(_, actual) = KernelTermExport::machine(&root).unwrap()
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
