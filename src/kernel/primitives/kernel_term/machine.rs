//! Lossless machine-value boundary. Result type and operator format are
//! separate: a uint32 value can contain a sign-free int32 word operation.
use super::*;

/// Exact legacy literal form, including the uint32-at-rest tag. Converting
/// through a mathematical value would erase that structural distinction.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum KernelMachineLiteral {
    Word32(u32),
    UInt32(u32),
    Int64(i64),
    UInt64(u64),
    Wide(MachineIntegerConstant),
}

pub(super) fn wrap_exact(format: MachineIntegerType, term: Bitvector32Term) -> CValue {
    // value_from_term applies the word-format convention. This adapter must
    // preserve the payload exactly, including constants inside operations.
    match format {
        MachineIntegerType::Int8 => CValue::Int8(term),
        MachineIntegerType::UInt8 => CValue::UInt8(term),
        MachineIntegerType::Int16 => CValue::Int16(term),
        MachineIntegerType::UInt16 => CValue::UInt16(term),
        MachineIntegerType::Int32 => CValue::Int32(term),
        MachineIntegerType::UInt32 => CValue::UInt32(term),
        MachineIntegerType::Int64 => CValue::Int64(term),
        MachineIntegerType::UInt64 => CValue::UInt64(term),
        MachineIntegerType::Int128 => CValue::Int128(term),
        MachineIntegerType::UInt128 => CValue::UInt128(term),
    }
}

impl KernelTermImport {
    pub(super) fn machine(
        &mut self,
        result: MachineIntegerType,
        term: &Bitvector32Term,
    ) -> KernelTerm {
        use Bitvector32Term as Old;
        use KernelMachineLiteral as Literal;
        use KernelTermNode as Node;
        crate::instrumentation::record_deterministic_work(1);
        let node = match term {
            Old::Constant(bits) => Node::MachineLiteral(Literal::Word32(*bits)),
            Old::UInt32Constant(bits) => Node::MachineLiteral(Literal::UInt32(*bits)),
            Old::Int64Constant(value) => Node::MachineLiteral(Literal::Int64(*value)),
            Old::UInt64Constant(value) => Node::MachineLiteral(Literal::UInt64(*value)),
            Old::MachineIntegerConstant(value) => Node::MachineLiteral(Literal::Wide(*value)),
            Old::Variable(variable) => Node::Variable(*variable),
            Old::Binary {
                op,
                format,
                left,
                right,
            } if !matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight) => {
                Node::MachineBinary {
                    format: *format,
                    operator: *op,
                    arguments: [self.machine(*format, left), self.machine(*format, right)],
                }
            }
            Old::Unary {
                format,
                op,
                operand,
            } => Node::MachineUnary {
                format: *format,
                operator: *op,
                operand: self.machine(*format, operand),
            },
            Old::MachineIntegerCast {
                source,
                destination,
                value,
            } => Node::MachineCast {
                source: *source,
                destination: *destination,
                operand: self.machine(*source, value),
            },
            // Shifts need an independently typed count; loads, binders and
            // pointer observations retain their complete legacy payload.
            _ => {
                return KernelTerm::legacy(PureFunctionArgument::Value(wrap_exact(
                    result,
                    term.clone(),
                )));
            }
        };
        KernelTerm::intern(KernelType::C(result.c_type()), node)
    }
}

impl KernelTermExport {
    pub(super) fn machine(term: &KernelTerm) -> Result<Bitvector32Term, &'static str> {
        use Bitvector32Term as Old;
        use KernelMachineLiteral as Literal;
        use KernelTermNode as Node;
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::MachineLiteral(value) => match value {
                Literal::Word32(bits) => Old::Constant(*bits),
                Literal::UInt32(bits) => Old::UInt32Constant(*bits),
                Literal::Int64(value) => Old::Int64Constant(*value),
                Literal::UInt64(value) => Old::UInt64Constant(*value),
                Literal::Wide(value) => Old::MachineIntegerConstant(*value),
            },
            Node::Variable(variable) => Old::Variable(*variable),
            Node::MachineBinary {
                format,
                operator,
                arguments,
            } => Old::Binary {
                format: *format,
                op: *operator,
                left: Box::new(Self::machine(&arguments[0])?),
                right: Box::new(Self::machine(&arguments[1])?),
            },
            Node::MachineUnary {
                format,
                operator,
                operand,
            } => Old::Unary {
                format: *format,
                op: *operator,
                operand: Box::new(Self::machine(operand)?),
            },
            Node::MachineCast {
                source,
                destination,
                operand,
            } => Old::MachineIntegerCast {
                source: *source,
                destination: *destination,
                value: Box::new(Self::machine(operand)?),
            },
            Node::Legacy(value) => {
                let PureFunctionArgument::Value(value) = value.value() else {
                    return Err("expected a machine value legacy payload");
                };
                let (integer_c_value!(bits)) = value else {
                    return Err("expected a machine integer legacy payload");
                };
                bits.clone()
            }
            _ => return Err("expected a machine kernel term"),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn machine_bridge_preserves_formats_payloads_and_structure() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let constant = match format {
                MachineIntegerType::Int32 => Bitvector32Term::Constant(u32::MAX),
                MachineIntegerType::UInt32 => Bitvector32Term::UInt32Constant(u32::MAX),
                MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(i64::MIN),
                _ => Bitvector32Term::UInt64Constant(u64::MAX),
            };
            for operator in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                let bits = Bitvector32Term::Binary {
                    format,
                    op: operator,
                    left: Box::new(Bitvector32Term::Variable(Variable(991100))),
                    right: Box::new(constant.clone()),
                };
                let source = PureFunctionArgument::Value(wrap_exact(format, bits));
                let common = KernelTermImport::default().argument(&source);
                assert_eq!(common.ty(), &KernelType::C(format.c_type()));
                assert_eq!(common.children().len(), 2);
                assert_eq!(
                    KernelTermExport::default().argument(&common).unwrap(),
                    source
                );
                assert_eq!(KernelTermImport::default().argument(&source), common);
            }
        }
        // The result's unsigned type does not retag a sign-free word node,
        // or change the exact constant representation used by its operand.
        let source = PureFunctionArgument::Value(CValue::UInt32(Bitvector32Term::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(Bitvector32Term::Constant(1)),
            right: Box::new(Bitvector32Term::UInt32Constant(1)),
        }));
        let term = KernelTermImport::default().argument(&source);
        assert_ne!(term.children()[0], term.children()[1]);
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }

    #[test]
    fn machine_import_keeps_complete_pointer_integer_metadata() {
        let value = CValue::UInt64(Bitvector32Term::Variable(Variable(991101)))
            .complete_word(Pointer::symbolic(Variable(991102)));
        let source = PureFunctionArgument::Value(value);
        let term = KernelTermImport::default().argument(&source);
        assert!(matches!(term.node(), KernelTermNode::Legacy(_)));
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }

    #[test]
    fn machine_cast_bridge_keeps_source_and_destination_without_evaluation() {
        let source =
            PureFunctionArgument::Value(CValue::UInt64(Bitvector32Term::MachineIntegerCast {
                source: MachineIntegerType::Int32,
                destination: MachineIntegerType::UInt64,
                value: Box::new(Bitvector32Term::Constant(u32::MAX)),
            }));
        let term = KernelTermImport::default().argument(&source);
        assert_eq!(term.children()[0].ty(), &KernelType::C(CType::Int32));
        assert_eq!(term.ty(), &KernelType::C(CType::UInt64));
        assert!(matches!(term.node(), KernelTermNode::MachineCast { .. }));
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }
}
