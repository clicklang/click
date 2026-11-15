//! Selected native storage identity for retained logical Boolean values.
use super::*;

impl KernelTerm {
    pub(crate) fn boolean_native(&self) -> Option<&ProgramValue> {
        let PureFunctionArgument::Value(value) = self.boolean_argument_native()? else {
            unreachable!("Boolean storage descriptor")
        };
        Some(value)
    }

    pub(crate) fn boolean_argument_native(&self) -> Option<&PureFunctionArgument> {
        if self.ty() != &KernelType::Bool {
            return None;
        }
        Some(
            self.0
                .argument_leaf
                .get_or_init(|| {
                    Box::new(PureFunctionArgument::Value(ProgramValue::Bool(
                        MachineTerm::bool_cast(
                            MachineIntegerType::UInt8,
                            BooleanOperandView::Shared(self)
                                .identity_leaf()
                                .into_owned(),
                        ),
                    )))
                })
                .as_ref(),
        )
    }
}
