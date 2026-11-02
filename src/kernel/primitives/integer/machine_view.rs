//! Borrowed root views of machine operands. Inspecting a shared root never
//! requests its boxed expansion; child observations retain child handles.
use super::*;

#[derive(Clone, Copy)]
pub(crate) enum MachineOperandView<'a> {
    Shared(&'a KernelTerm),
    Legacy(&'a Bitvector32Term),
}

impl SharedMachineIntegerTerm {
    pub(crate) fn operand_view(&self) -> MachineOperandView<'_> {
        match &self.0.operand {
            MachineIntegerOperand::Shared { term, .. } => MachineOperandView::Shared(term),
            MachineIntegerOperand::Legacy(value) => MachineOperandView::Legacy(value),
        }
    }
}

impl<'a> MachineOperandView<'a> {
    pub(crate) fn binary(self) -> Option<(MachineIntegerType, MachineBinaryOp, [Self; 2])> {
        match self {
            Self::Shared(term) => match term.node() {
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => Some((
                    *format,
                    *operator,
                    [Self::Shared(&arguments[0]), Self::Shared(&arguments[1])],
                )),
                _ => None,
            },
            Self::Legacy(Bitvector32Term::Binary {
                format,
                op,
                left,
                right,
            }) => Some((*format, *op, [Self::Legacy(left), Self::Legacy(right)])),
            Self::Legacy(_) => None,
        }
    }

    /// Literal payload only, without descending through an operation.
    pub(crate) fn literal(self) -> Option<Bitvector32Term> {
        match self {
            Self::Shared(term) if matches!(term.node(), KernelTermNode::MachineLiteral(_)) => {
                Some(KernelTermExport::machine(term).expect("machine literal"))
            }
            Self::Legacy(value) if is_machine_constant(value) => Some(value.clone()),
            _ => None,
        }
    }

    pub(crate) fn observe(self, ty: MachineIntegerType) -> Option<IntegerTerm> {
        if let Some(literal) = self.literal() {
            return IntegerTerm::from_machine(ty, literal);
        }
        match self {
            Self::Shared(term)
                if ty.format().bits() == 128
                    && !matches!(term.node(), KernelTermNode::Variable(_)) =>
            {
                None
            }
            Self::Shared(term) => Some(IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(ty, term.with_machine_observation_type(ty))?,
            )),
            Self::Legacy(value) => IntegerTerm::from_machine(ty, value.clone()),
        }
    }

    /// Legacy leaves retain the existing read-over-write adapter. A shared
    /// variable can also name a read, but constructing that leaf costs O(1).
    /// Explicit shared operators are never recursively resolved here.
    pub(crate) fn read_source(self) -> Option<std::borrow::Cow<'a, Bitvector32Term>> {
        match self {
            Self::Legacy(value) => Some(std::borrow::Cow::Borrowed(value)),
            Self::Shared(term) => match term.node() {
                KernelTermNode::Variable(variable) => Some(std::borrow::Cow::Owned(
                    Bitvector32Term::Variable(*variable),
                )),
                _ => None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operand_views_preserve_legacy_operation_readings() {
        use crate::kernel::machine_integer::{Operation, bounds, identity, representation};
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftRight,
            ] {
                let left = Bitvector32Term::Variable(Variable(956100));
                let right = ty
                    .constant_term(
                        MachineIntegerConstant::from_integer(ty.format(), &2.into()).unwrap(),
                    )
                    .unwrap();
                let boxed = Bitvector32Term::Binary {
                    format: ty,
                    op,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let shared = KernelTermImport::default().machine(ty, &boxed);
                let observation = SharedMachineIntegerTerm::from_shared(ty, shared).unwrap();
                let source = IntegerTerm::Machine(observation.clone());
                let expected =
                    representation::word_operation(ty, &boxed).map(|(operation, a, b)| {
                        (
                            ty,
                            operation.exact(
                                IntegerTerm::from_machine(ty, a.clone()).unwrap(),
                                IntegerTerm::from_machine(ty, b.clone()).unwrap(),
                            ),
                        )
                    });
                assert_eq!(identity::mathematical(&source), expected);
                let additive = representation::word_operation(ty, &boxed)
                    .is_some_and(|(op, _, _)| matches!(op, Operation::Add | Operation::Subtract));
                assert_eq!(
                    identity::additive_mathematical(&source),
                    additive.then_some(expected).flatten()
                );
                let view = observation.operand_view();
                let (_, _, [a, b]) = view.binary().unwrap();
                assert_eq!(a.observe(ty), IntegerTerm::from_machine(ty, left));
                assert_eq!(b.observe(ty), IntegerTerm::from_machine(ty, right));
                for upper in [false, true] {
                    let result = bounds::operation_bound(&observation, upper);
                    assert_eq!(
                        result.is_some(),
                        matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::ShiftRight)
                            || op == MachineBinaryOp::Remainder
                                && (upper || ty.format().is_signed())
                    );
                }
                assert!(!observation.has_boxed_operand());
            }
        }
    }

    #[test]
    fn operand_view_observation_preserves_format_admission() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt32;
        let boxed = Bitvector32Term::Binary {
            format: ty,
            op: MachineBinaryOp::Add,
            left: Box::new(Bitvector32Term::Variable(Variable(956101))),
            right: Box::new(Bitvector32Term::UInt32Constant(0)),
        };
        let shared = KernelTermImport::default().machine(ty, &boxed);
        for observed_ty in [
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
            let actual = MachineOperandView::Shared(&shared).observe(observed_ty);
            if let Some(IntegerTerm::Machine(machine)) = &actual {
                assert!(!machine.has_boxed_operand());
            }
            assert_eq!(
                actual,
                IntegerTerm::from_machine(observed_ty, boxed.clone())
            );
        }
    }
}
