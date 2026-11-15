//! Selected native storage identity for retained logical Boolean values.
use super::*;

impl KernelTerm {
    pub(crate) fn boolean_native(&self) -> Option<&ProgramValue> {
        if self.ty() != &KernelType::Bool {
            return None;
        }
        let PureFunctionArgument::Value(value) = self
            .0
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
            .as_ref()
        else {
            unreachable!("Boolean storage descriptor")
        };
        Some(value)
    }
}
