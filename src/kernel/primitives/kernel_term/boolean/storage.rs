//! Selected native storage identity for retained Boolean value carriers.
use super::*;

impl KernelTerm {
    /// A native constructor already produced this exact output. Reuse it in
    /// the existing compatibility slot; reading it must not export its operands
    /// again or change its canonical native spelling.
    pub(crate) fn retain_native_condition_output(&self, value: ConditionTerm) {
        if matches!(self.node(), KernelTermNode::BoolLiteral(_)) {
            return;
        }
        self.0.argument_leaf.get_or_init(|| {
            Box::new(PureFunctionArgument::Value(ProgramValue::Bool(
                MachineTerm::BoolCast {
                    to: MachineIntegerType::UInt8,
                    value: Box::new(value),
                },
            )))
        });
    }

    /// Borrow an output already supplied by a native producer or requested by
    /// a compatibility consumer. This must not initialize the slot: its
    /// initializer itself reads BooleanOperandView::native().
    pub(crate) fn cached_condition_output(&self) -> Option<&ConditionTerm> {
        let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
            value, ..
        })) = self.0.argument_leaf.get()?.as_ref()
        else {
            return None;
        };
        Some(value)
    }

    pub(crate) fn boolean_native(&self) -> Option<&ProgramValue> {
        let PureFunctionArgument::Value(value) = self.boolean_argument_native()? else {
            unreachable!("Boolean storage descriptor")
        };
        Some(value)
    }

    pub(crate) fn boolean_argument_native(&self) -> Option<&PureFunctionArgument> {
        if self.ty() == &KernelType::Program(ProgramType::Bool)
            && let KernelTermNode::Variable(variable) = self.node()
        {
            return Some(
                self.0
                    .argument_leaf
                    .get_or_init(|| {
                        Box::new(PureFunctionArgument::Value(ProgramValue::Bool(
                            MachineTerm::Variable(*variable),
                        )))
                    })
                    .as_ref(),
            );
        }
        if self.ty() != &KernelType::Bool {
            return None;
        }
        if let Some(value) = self.0.argument_leaf.get() {
            return Some(value);
        }
        if let KernelTermNode::LegacyBool(legacy) = self.node()
            && let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value,
            })) = legacy.value()
            && !matches!(value.as_ref(), ConditionTerm::Constant(_))
        {
            return Some(legacy.value());
        }
        Some(
            self.0
                .argument_leaf
                .get_or_init(|| {
                    let condition = BooleanOperandView::Shared(self)
                        .identity_leaf()
                        .into_owned();
                    // Integer comparison export constructs a nonconstant
                    // condition directly. Its storage wrapper needs no second
                    // constant-folding constructor.
                    let value = if matches!(self.node(), KernelTermNode::IntegerCompare { .. }) {
                        MachineTerm::BoolCast {
                            to: MachineIntegerType::UInt8,
                            value: Box::new(condition),
                        }
                    } else {
                        MachineTerm::bool_cast(MachineIntegerType::UInt8, condition)
                    };
                    Box::new(PureFunctionArgument::Value(ProgramValue::Bool(value)))
                })
                .as_ref(),
        )
    }
}
