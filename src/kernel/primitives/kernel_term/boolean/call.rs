//! Boolean pure-call production retains numeric operands and exact opaque
//! descriptors. Compatibility readers borrow a single selected call adapter.
use super::*;

impl KernelTermImport {
    pub(crate) fn boolean_call(&mut self, application: &SharedPureApplication) -> KernelTerm {
        self.boolean_call_with_retained(application, &[])
    }

    pub(crate) fn boolean_call_with_retained(
        &mut self,
        application: &SharedPureApplication,
        retained: &[Option<KernelTerm>],
    ) -> KernelTerm {
        let arguments = application
            .arguments()
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                retained
                    .get(index)
                    .and_then(Clone::clone)
                    .unwrap_or_else(|| {
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
        KernelTerm::checked_call(KernelType::Bool, application.name().into(), arguments)
    }
}
impl KernelTerm {
    pub(crate) fn boolean_call_native(&self) -> Option<&ConditionTerm> {
        if self.ty() != &KernelType::Bool {
            return None;
        }
        let KernelTermNode::Call { name, arguments } = self.node() else {
            return None;
        };
        let MachineTerm::BoolCast { value, .. } = self.0.machine_leaf.get_or_init(|| {
            let mut export = KernelTermExport::default();
            let arguments = arguments
                .iter()
                .map(|argument| {
                    if let KernelType::Program(ty) = argument.ty()
                        && let Some(format) = MachineIntegerType::from_program_type(*ty)
                        && !matches!(argument.node(), KernelTermNode::Legacy(_))
                    {
                        PureFunctionArgument::SharedMachine(
                            MachineOperandView::Shared(argument).retain(format),
                        )
                    } else {
                        export.argument(argument).expect("Boolean call argument")
                    }
                })
                .collect();
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(ConditionTerm::BoolApplication(
                    SharedPureApplication::intern(name.clone(), arguments),
                )),
            }
        }) else {
            unreachable!("Boolean call descriptor");
        };
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boolean_calls_preserve_exact_descriptors_and_semantic_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(999401)),
            ProgramType::Int32Pointer,
        );
        let applications = [pointer.clone(), pointer.with_pointee_constant(true)].map(|pointer| {
            SharedPureApplication::intern(
                "boolean_exact_arguments".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(pointer))],
            )
        });
        assert_eq!(applications[0], applications[1]);
        let roots = applications
            .each_ref()
            .map(|application| KernelTermImport::default().boolean_call(application));
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        for (root, application) in roots.iter().zip(&applications) {
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(root).unwrap()),
                format!("{:?}", ConditionTerm::BoolApplication(application.clone()))
            );
            assert!(std::ptr::eq(
                root.boolean_call_native().unwrap(),
                root.boolean_call_native().unwrap()
            ));
        }
        let observed = roots.map(|guard| {
            SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [
                        guard,
                        KernelTermImport::default()
                            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1)),
                        KernelTermImport::default()
                            .machine(MachineIntegerType::Int32, &MachineTerm::constant(0)),
                    ],
                ),
            )
            .unwrap()
        });
        assert_eq!(observed[0], observed[1]);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/call.rs");
}
