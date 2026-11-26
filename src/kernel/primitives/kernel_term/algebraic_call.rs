//! Algebraic calls retain argument roots and the native numeric carrier forms.
//! Unlike SharedPureApplication, the native algebraic argument vector distinguishes
//! Value(machine) from SharedMachine. Preserve the original immutable carrier
//! handle: reconstructing it from its root can change native argument identity.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelAlgebraicCall {
    pub(crate) algebraic_type: AlgebraicType,
    pub(crate) name: String,
    pub(crate) arguments: Vec<KernelTerm>,
    pub(crate) shared_machine_arguments: Vec<Option<SharedMachineIntegerTerm>>,
}

impl KernelAlgebraicCall {
    pub(crate) fn into_term(self) -> KernelTerm {
        KernelTerm::intern(
            KernelType::Algebraic(self.algebraic_type.clone()),
            KernelTermNode::AlgebraicCall(self),
        )
    }
}
impl KernelTerm {
    pub(crate) fn algebraic_call(
        ty: AlgebraicType,
        name: String,
        arguments: Vec<(KernelTerm, Option<SharedMachineIntegerTerm>)>,
    ) -> Self {
        let (arguments, shared_machine_arguments) = arguments.into_iter().unzip();
        KernelAlgebraicCall {
            algebraic_type: ty,
            name,
            arguments,
            shared_machine_arguments,
        }
        .into_term()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_calls_preserve_numeric_argument_forms_and_exact_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(vec![]).algebraic_type;
        let word = OldMachineTerm::add(
            OldMachineTerm::Variable(Variable(999701)),
            OldMachineTerm::constant(1),
        );
        let pointer = OldPointer::new(
            Address::symbolic(Variable(999702)),
            ProgramType::Int32Pointer,
        );
        let arguments = [
            PureFunctionArgument::Value(ProgramValue::Int32(word.clone())),
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                word,
            )),
        ];
        assert_ne!(arguments[0], arguments[1]);
        let sources = arguments.map(|arg| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "algebraic_argument_forms".into(),
                arguments: vec![
                    arg,
                    PureFunctionArgument::Value(ProgramValue::Pointer(pointer.clone())),
                ],
            },
        });
        let roots = sources
            .each_ref()
            .map(|source| KernelTermImport::default().algebraic(source));
        assert_ne!(roots[0], roots[1]);
        assert!(!roots[0].algebraic_syntax_equal(&roots[1]));
        for (root, source) in roots.iter().zip(&sources) {
            let output = KernelTermExport::default().algebraic(root).unwrap();
            assert_eq!(&output, source);
            assert_eq!(format!("{output:?}"), format!("{source:?}"));
        }
    }

    #[test]
    fn algebraic_calls_keep_retained_match_argument_observation_types() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut native = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(
            ProgramType::Int32Pointer,
        )]);
        let ty = native.algebraic_type.clone();
        let scrutinee = KernelTermImport::default().algebraic(&native);
        let pointer = OldPointer::new(
            Address::symbolic(Variable(999703)),
            ProgramType::Int32Pointer,
        );
        native.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(pointer))],
        };
        let matched = KernelMatch::new(
            KernelType::Algebraic(ty.clone()),
            scrutinee.clone(),
            vec![(
                KernelMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![KernelTermImport::default().argument(
                        &PureFunctionArgument::Value(ProgramValue::Pointer(OldPointer::new(
                            Address::symbolic(Variable(999704)),
                            ProgramType::Int32Pointer,
                        ))),
                    )],
                    binding_names: Default::default(),
                },
                KernelTermImport::default().algebraic(&native),
            )],
        )
        .unwrap()
        .into_term();
        let call = KernelTerm::algebraic_call(
            ty,
            "matched_algebraic_argument".into(),
            vec![(matched, None)],
        );
        let guard = KernelTerm::algebraic_equal_raw([call, scrutinee]);
        let native_guard = KernelTermExport::condition(&guard).unwrap();
        let format = MachineIntegerType::Int32;
        let branches = [OldMachineTerm::constant(1), OldMachineTerm::constant(2)];
        let root = KernelTerm::machine_if_shared(
            format,
            [
                guard,
                KernelTermImport::default().machine(format, &branches[0]),
                KernelTermImport::default().machine(format, &branches[1]),
            ],
        );
        let observed = SharedMachineIntegerTerm::observe_shared(format, root).unwrap();
        let expected = SharedMachineIntegerTerm::intern(
            format,
            OldMachineTerm::If {
                condition: Box::new(native_guard),
                then_term: Box::new(branches[0].clone()),
                else_term: Box::new(branches[1].clone()),
            },
        );
        assert_eq!(observed, expected);
    }
}
