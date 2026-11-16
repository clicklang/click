//! Typed Click calls preserve their exact native argument carrier forms.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelFloatCall {
    pub(crate) format: KernelFloatType,
    pub(crate) name: String,
    pub(crate) arguments: Vec<KernelTerm>,
    pub(crate) shared_machine_arguments: Vec<Option<SharedMachineIntegerTerm>>,
}
impl KernelFloatCall {
    pub(crate) fn into_term(self) -> KernelTerm {
        KernelTerm::intern(
            KernelType::Program(self.format.program_type()),
            KernelTermNode::FloatCall(self),
        )
    }
}
impl KernelTerm {
    pub(crate) fn float_call(
        format: KernelFloatType,
        name: String,
        arguments: Vec<(Self, Option<SharedMachineIntegerTerm>)>,
    ) -> Self {
        let (arguments, shared_machine_arguments) = arguments.into_iter().unzip();
        KernelFloatCall {
            format,
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
    fn float_calls_preserve_exact_argument_carriers_and_nested_structure() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let integer = MachineTerm::add(
                MachineTerm::Variable(Variable(1008200)),
                MachineTerm::constant(1),
            );
            let arguments = [
                PureFunctionArgument::Value(ProgramValue::Int32(integer.clone())),
                PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    integer,
                )),
            ];
            let roots = arguments.map(|argument| {
                let source = MachineTerm::ClickFunctionApplication {
                    name: "float_result".into(),
                    arguments: vec![
                        argument,
                        PureFunctionArgument::Value(format.value(
                            MachineTerm::ClickFunctionApplication {
                                name: "float_seed".into(),
                                arguments: vec![
                                    PureFunctionArgument::Value(ProgramValue::Float32(
                                        MachineTerm::uint32_constant(0x7fc00123),
                                    )),
                                    PureFunctionArgument::Value(ProgramValue::Float64(
                                        MachineTerm::uint64_constant(0x8000000000000000),
                                    )),
                                ],
                            },
                        )),
                    ],
                };
                let root = KernelTermImport::default().float(format, &source);
                assert!(matches!(root.node(), KernelTermNode::FloatCall(_)));
                assert!(matches!(
                    root.children()[1].node(),
                    KernelTermNode::FloatCall(_)
                ));
                assert_eq!(
                    KernelTermExport::float(&root).unwrap(),
                    format.value(source.clone())
                );
                assert_eq!(
                    format!("{:?}", KernelTermExport::float(&root).unwrap()),
                    format!("{:?}", format.value(source.clone()))
                );
                assert!(
                    FloatOperandView::Shared(&root)
                        .syntax_equal(FloatOperandView::Native(format, &source))
                );
                root
            });
            assert_ne!(roots[0], roots[1]);
            assert!(
                !FloatOperandView::Shared(&roots[0])
                    .syntax_equal(FloatOperandView::Shared(&roots[1]))
            );
        }
    }
}

impl FloatOperandView<'_> {
    pub(crate) fn is_call(self) -> bool {
        match self {
            Self::Native(_, MachineTerm::ClickFunctionApplication { .. }) => true,
            Self::Shared(root) => matches!(root.node(), KernelTermNode::FloatCall(_)),
            _ => false,
        }
    }
}
