//! Logical constructors retain children and apply only the native root rules.
use super::*;

impl KernelTermImport {
    /// Logical truth of a C Bool carrier. Only an unsigned byte literal
    /// folds here. Every other plain word keeps the written byte test.
    pub(crate) fn truth_of_bool_word(&mut self, word: &OldMachineTerm) -> KernelTerm {
        let byte = MachineIntegerType::UInt8;
        if let Some(condition) = word.bool_cast_operand() {
            return self.condition(condition);
        }
        if let Some(value) = byte.constant_from_term(word) {
            return KernelTerm::boolean_literal(value.bits() != 0);
        }
        let zero = KernelMachineLiteral::constant_term(MachineIntegerConstant::from_term_bits(
            byte.format(),
            0,
        ));
        let equal = KernelTerm::boolean_comparison_raw(
            byte,
            CompareRelation::Equal,
            [self.machine(byte, word), zero],
        );
        KernelTerm::boolean_if_raw([
            equal,
            KernelTerm::boolean_literal(false),
            KernelTerm::boolean_literal(true),
        ])
    }
}

impl KernelTerm {
    pub(crate) fn boolean_literal(value: bool) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(value))
    }

    pub(crate) fn boolean_if(arguments: [Self; 3]) -> Self {
        Self::boolean_if_in(arguments, false)
    }

    pub(in crate::kernel) fn boolean_if_preserving_equal_arms(arguments: [Self; 3]) -> Self {
        Self::boolean_if_in(arguments, true)
    }

    fn boolean_if_in([guard, yes, no]: [Self; 3], preserve_equal_arms: bool) -> Self {
        let view = BooleanOperandView::Shared;
        match view(&guard).constant() {
            Some(true) => yes,
            Some(false) => no,
            None if !preserve_equal_arms && view(&yes).syntax_equal(view(&no)) => yes,
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
            KernelMachineLiteral::constant_term(MachineIntegerConstant::from_term_bits(
                destination.format(),
                u128::from(value),
            ))
        } else {
            Self::bool_cast(destination, operand).expect("Boolean conversion")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bool_word_truth_preserves_the_written_byte_test() {
        let _session = crate::kernel::VerificationSession::enter();
        for word in [
            OldMachineTerm::bool_cast(MachineIntegerType::UInt8, OldConditionTerm::Constant(false)),
            OldMachineTerm::bool_cast(MachineIntegerType::UInt8, OldConditionTerm::Constant(true)),
            OldMachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 255,
            },
            OldMachineTerm::constant(1),
            OldMachineTerm::Variable(Variable(999421)),
            OldMachineTerm::bool_cast(
                MachineIntegerType::Int64,
                OldConditionTerm::Variable(Variable(999421)),
            ),
        ] {
            let root = KernelTermImport::default().truth_of_bool_word(&word);
            let old = OldConditionTerm::truth_of_bool_word(&word);
            assert_eq!(
                root,
                KernelTermImport::default().condition(&old),
                "{word:?}"
            );
        }
    }

    #[test]
    fn boolean_cast_observation_preserves_native_argument_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        // Two producers of one logical pointer: distinct handles.
        let pointer = || {
            Pointer::new(
                Address::symbolic(Variable(999450)),
                ProgramType::Int32Pointer,
            )
        };
        let roots = [pointer(), pointer()].map(|pointer| {
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
            OldConditionTerm::Constant(false),
            OldConditionTerm::Constant(true),
            OldConditionTerm::Variable(Variable(999420)),
            OldConditionTerm::BoolApplication(SharedPureApplication::intern(
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
                        OldConditionTerm::bool_if(guard.clone(), yes.clone(), no.clone())
                    );
                }
                let root = KernelTerm::boolean_equal(
                    [guard, yes].map(|value| KernelTermImport::default().condition(value)),
                );
                assert_eq!(
                    KernelTermExport::condition(&root).unwrap(),
                    OldConditionTerm::bool_equal(guard.clone(), yes.clone())
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
                    OldMachineTerm::bool_cast(format, value.clone())
                );
            }
        }
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/composition.rs");
}
