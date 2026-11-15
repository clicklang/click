//! Logical constructors retain children and apply only the native root rules.
use super::*;

impl KernelTerm {
    pub(crate) fn boolean_if([guard, yes, no]: [Self; 3]) -> Self {
        let view = BooleanOperandView::Shared;
        match view(&guard).constant() {
            Some(true) => yes,
            Some(false) => no,
            None if view(&yes).syntax_equal(view(&no)) => yes,
            None if view(&yes).constant() == Some(true) && view(&no).constant() == Some(false) => {
                guard
            }
            None => Self::boolean_if_raw([guard, yes, no]),
        }
    }
    pub(crate) fn boolean_equal([left, right]: [Self; 2]) -> Self {
        if BooleanOperandView::Shared(&left).syntax_equal(BooleanOperandView::Shared(&right)) {
            Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(true))
        } else {
            Self::boolean_equal_raw([left, right])
        }
    }
    pub(crate) fn boolean_cast(destination: MachineIntegerType, operand: Self) -> Self {
        if let Some(value) = BooleanOperandView::Shared(&operand).constant() {
            KernelTermImport::default().machine(
                destination,
                &MachineTerm::bool_cast(destination, ConditionTerm::Constant(value)),
            )
        } else {
            Self::bool_cast(destination, operand).expect("Boolean conversion")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boolean_cast_observation_preserves_native_argument_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(999450)),
            ProgramType::Int32Pointer,
        );
        let roots = [pointer.clone(), pointer.with_pointee_constant(true)].map(|pointer| {
            let application = SharedPureApplication::intern(
                "cast_bool_identity".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(pointer))],
            );
            KernelTerm::boolean_cast(
                MachineIntegerType::Int32,
                KernelTermImport::default().boolean_call(&application),
            )
        });
        assert_ne!(roots[0], roots[1]);
        let observations = roots.map(|root| {
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::Int32, root).unwrap()
        });
        assert_eq!(observations[0], observations[1]);
    }
    #[test]
    fn boolean_composition_matches_native_root_reductions() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = [
            ConditionTerm::Constant(false),
            ConditionTerm::Constant(true),
            ConditionTerm::Variable(Variable(999420)),
            ConditionTerm::BoolApplication(SharedPureApplication::intern(
                "bool_composed".into(),
                vec![],
            )),
        ];
        for guard in &values {
            for yes in &values {
                for no in &values {
                    let root = KernelTerm::boolean_if(
                        [guard, yes, no].map(|value| KernelTermImport::default().condition(value)),
                    );
                    assert_eq!(
                        KernelTermExport::condition(&root).unwrap(),
                        ConditionTerm::bool_if(guard.clone(), yes.clone(), no.clone())
                    );
                }
                let root = KernelTerm::boolean_equal(
                    [guard, yes].map(|value| KernelTermImport::default().condition(value)),
                );
                assert_eq!(
                    KernelTermExport::condition(&root).unwrap(),
                    ConditionTerm::bool_equal(guard.clone(), yes.clone())
                );
            }
        }
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
            MachineIntegerType::UInt128,
        ] {
            for value in &values {
                let root =
                    KernelTerm::boolean_cast(format, KernelTermImport::default().condition(value));
                assert!(root.is_shared_machine_operand());
                assert_eq!(
                    KernelTermExport::machine(&root).unwrap(),
                    MachineTerm::bool_cast(format, value.clone())
                );
            }
        }
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/composition.rs");
}
