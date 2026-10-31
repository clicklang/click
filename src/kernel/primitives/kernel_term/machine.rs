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

/// Transitional checker encoding, kept distinct from cast semantics so an
/// import/export round trip preserves the exact old constructor. Remove this
/// distinction when checker consumers no longer require the old tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum KernelMachineCastEncoding {
    Generic,
    Int64From32,
    UInt64From32,
    UInt32From64,
    Int64FromUInt32,
    UInt64FromInt32,
    UInt64FromInt64,
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
            } => Node::MachineBinary {
                format: *format,
                operator: *op,
                // Shift lowering has already converted the count to this
                // carrier width. Preserve that conversion in the operand;
                // do not infer a source count type from the result type.
                arguments: [self.machine(*format, left), self.machine(*format, right)],
            },
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
                encoding: KernelMachineCastEncoding::Generic,
                source: *source,
                destination: *destination,
                operand: self.machine(*source, value),
            },
            Old::Int64From32(value)
            | Old::UInt64From32(value)
            | Old::UInt32From64(value)
            | Old::Int64FromUInt32(value)
            | Old::UInt64FromInt32(value)
            | Old::UInt64FromInt64(value) => {
                use KernelMachineCastEncoding as Encoding;
                use MachineIntegerType as Ty;
                let (encoding, source, destination) = match term {
                    Old::Int64From32(_) => (Encoding::Int64From32, Ty::Int32, Ty::Int64),
                    Old::UInt64From32(_) => (Encoding::UInt64From32, Ty::UInt32, Ty::UInt64),
                    // Low bits do not depend on signedness. UInt64 is the
                    // operand's bit interpretation, not its source C type.
                    Old::UInt32From64(_) => (Encoding::UInt32From64, Ty::UInt64, Ty::UInt32),
                    Old::Int64FromUInt32(_) => (Encoding::Int64FromUInt32, Ty::UInt32, Ty::Int64),
                    Old::UInt64FromInt32(_) => (Encoding::UInt64FromInt32, Ty::Int32, Ty::UInt64),
                    Old::UInt64FromInt64(_) => (Encoding::UInt64FromInt64, Ty::Int64, Ty::UInt64),
                    _ => unreachable!(),
                };
                Node::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand: self.machine(source, value),
                }
            }
            // Loads, binders and pointer observations retain their complete
            // legacy payload.
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
                encoding,
                source,
                destination,
                operand,
            } => {
                use KernelMachineCastEncoding as Encoding;
                let value = Box::new(Self::machine(operand)?);
                match encoding {
                    Encoding::Generic => Old::MachineIntegerCast {
                        source: *source,
                        destination: *destination,
                        value,
                    },
                    Encoding::Int64From32 => Old::Int64From32(value),
                    Encoding::UInt64From32 => Old::UInt64From32(value),
                    Encoding::UInt32From64 => Old::UInt32From64(value),
                    Encoding::Int64FromUInt32 => Old::Int64FromUInt32(value),
                    Encoding::UInt64FromInt32 => Old::UInt64FromInt32(value),
                    Encoding::UInt64FromInt64 => Old::UInt64FromInt64(value),
                }
            }
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
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
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
    fn specialized_casts_share_typed_nodes_without_losing_their_encoding() {
        use Bitvector32Term as Old;
        use MachineIntegerType as Ty;
        let casts: [(fn(Box<Old>) -> Old, Ty, Ty); 6] = [
            (Old::Int64From32, Ty::Int32, Ty::Int64),
            (Old::UInt64From32, Ty::UInt32, Ty::UInt64),
            (Old::UInt32From64, Ty::UInt64, Ty::UInt32),
            (Old::Int64FromUInt32, Ty::UInt32, Ty::Int64),
            (Old::UInt64FromInt32, Ty::Int32, Ty::UInt64),
            (Old::UInt64FromInt64, Ty::Int64, Ty::UInt64),
        ];
        for (constructor, source, destination) in casts {
            let operand = Old::Variable(Variable(991103));
            let value = PureFunctionArgument::Value(wrap_exact(
                destination,
                constructor(Box::new(operand.clone())),
            ));
            let common = KernelTermImport::default().argument(&value);
            assert!(matches!(common.node(), KernelTermNode::MachineCast { .. }));
            assert_eq!(common.children()[0].ty(), &KernelType::C(source.c_type()));
            assert!(matches!(
                common.children()[0].node(),
                KernelTermNode::Variable(_)
            ));
            assert_eq!(common.ty(), &KernelType::C(destination.c_type()));
            assert_eq!(
                KernelTermExport::default().argument(&common).unwrap(),
                value
            );
            assert_eq!(KernelTermImport::default().argument(&value), common);
            let generic = PureFunctionArgument::Value(wrap_exact(
                destination,
                Old::MachineIntegerCast {
                    source,
                    destination,
                    value: Box::new(operand),
                },
            ));
            assert_ne!(KernelTermImport::default().argument(&generic), common);
        }
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
