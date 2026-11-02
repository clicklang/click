//! Lossless machine-value boundary. Result type and operator format are
//! separate: a uint32 value can contain a sign-free int32 word operation.
use super::*;

impl KernelTerm {
    /// Retain a legacy machine operator over shared children without folding.
    /// Child interpretation is supplied by the caller, as in the legacy node.
    pub(crate) fn machine_binary_shared(
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [Self; 2],
    ) -> Self {
        Self::intern(
            KernelType::C(format.c_type()),
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            },
        )
    }

    pub(crate) fn machine_unary_shared(
        format: MachineIntegerType,
        operator: MachineUnaryOp,
        operand: Self,
    ) -> Self {
        Self::intern(
            KernelType::C(format.c_type()),
            KernelTermNode::MachineUnary {
                format,
                operator,
                operand,
            },
        )
    }

    pub(crate) fn machine_cast_shared(
        encoding: KernelMachineCastEncoding,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        operand: Self,
    ) -> Self {
        Self::intern(
            KernelType::C(destination.c_type()),
            KernelTermNode::MachineCast {
                encoding,
                source,
                destination,
                operand,
            },
        )
    }

    /// Change only the observation's numeric interpretation. The underlying
    /// word node and its format-tagged operations remain exactly as written.
    pub(crate) fn with_machine_observation_type(&self, format: MachineIntegerType) -> Self {
        if self.ty() == &KernelType::C(format.c_type()) {
            return self.clone();
        }
        Self::intern(KernelType::C(format.c_type()), self.node().clone())
    }

    /// Construct one arithmetic operation structurally from shared children.
    /// Signed definedness belongs to the evaluator's separate obligations.
    pub(crate) fn arithmetic_binary(
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [Self; 2],
    ) -> Result<Self, &'static str> {
        if !matches!(
            format,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        ) || !matches!(
            operator,
            MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply
        ) || arguments
            .iter()
            .any(|arg| arg.ty() != &KernelType::C(format.c_type()))
        {
            return Err("arithmetic requires matching 32-bit or 64-bit integer operands");
        }
        Ok(Self::intern(
            KernelType::C(format.c_type()),
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            },
        ))
    }
}

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

impl KernelMachineLiteral {
    pub(crate) fn legacy_term(&self) -> Bitvector32Term {
        match self {
            Self::Word32(bits) => Bitvector32Term::Constant(*bits),
            Self::UInt32(bits) => Bitvector32Term::UInt32Constant(*bits),
            Self::Int64(value) => Bitvector32Term::Int64Constant(*value),
            Self::UInt64(value) => Bitvector32Term::UInt64Constant(*value),
            Self::Wide(value) => Bitvector32Term::MachineIntegerConstant(*value),
        }
    }
}

/// Cached checking metadata, never a replacement for the structural node.
/// Apply the existing constant readers to one operator over literal children;
/// signed overflow and undefined division/shift readings remain absent.
pub(super) fn constant_reading(node: &KernelTermNode) -> Option<KernelMachineLiteral> {
    let (format, root) = match node {
        KernelTermNode::MachineLiteral(value) => return Some(value.clone()),
        KernelTermNode::MachineBinary {
            format,
            operator,
            arguments: [left, right],
        } => {
            // The legacy wide reader accepts only literal shift counts.
            // Preserve that admission rule even if a count has a cached value.
            if matches!(
                format,
                MachineIntegerType::Int64 | MachineIntegerType::UInt64
            ) && matches!(
                operator,
                MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight
            ) && !matches!(right.node(), KernelTermNode::MachineLiteral(_))
            {
                return None;
            }
            (
                *format,
                Bitvector32Term::Binary {
                    format: *format,
                    op: *operator,
                    left: Box::new(left.machine_constant_reading()?.legacy_term()),
                    right: Box::new(right.machine_constant_reading()?.legacy_term()),
                },
            )
        }
        KernelTermNode::MachineUnary {
            format,
            operator,
            operand,
        } => (
            *format,
            Bitvector32Term::Unary {
                format: *format,
                op: *operator,
                operand: Box::new(operand.machine_constant_reading()?.legacy_term()),
            },
        ),
        KernelTermNode::MachineCast {
            encoding,
            source,
            destination,
            operand,
        } => (
            *destination,
            encoding
                .unary(*source, *destination)
                .build_raw(operand.machine_constant_reading()?.legacy_term()),
        ),
        _ => return None,
    };
    match format {
        MachineIntegerType::Int32 => root.as_const().map(KernelMachineLiteral::Word32),
        MachineIntegerType::UInt32 => root.as_const().map(KernelMachineLiteral::UInt32),
        MachineIntegerType::Int64 => root.int64_as_const().map(KernelMachineLiteral::Int64),
        MachineIntegerType::UInt64 => root.uint64_as_const().map(KernelMachineLiteral::UInt64),
        _ => None,
    }
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

impl KernelMachineCastEncoding {
    pub(crate) fn of_unary(
        op: BitvectorUnaryOp,
    ) -> Option<(Self, MachineIntegerType, MachineIntegerType)> {
        use BitvectorUnaryOp as U;
        use MachineIntegerType as T;
        Some(match op {
            U::MachineIntegerCast {
                source,
                destination,
            } => (Self::Generic, source, destination),
            U::Int64From32 => (Self::Int64From32, T::Int32, T::Int64),
            U::UInt64From32 => (Self::UInt64From32, T::UInt32, T::UInt64),
            U::UInt32From64 => (Self::UInt32From64, T::UInt64, T::UInt32),
            U::Int64FromUInt32 => (Self::Int64FromUInt32, T::UInt32, T::Int64),
            U::UInt64FromInt32 => (Self::UInt64FromInt32, T::Int32, T::UInt64),
            U::UInt64FromInt64 => (Self::UInt64FromInt64, T::Int64, T::UInt64),
            _ => return None,
        })
    }

    pub(crate) fn unary(
        self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> BitvectorUnaryOp {
        use BitvectorUnaryOp as U;
        match self {
            Self::Generic => U::MachineIntegerCast {
                source,
                destination,
            },
            Self::Int64From32 => U::Int64From32,
            Self::UInt64From32 => U::UInt64From32,
            Self::UInt32From64 => U::UInt32From64,
            Self::Int64FromUInt32 => U::Int64FromUInt32,
            Self::UInt64FromInt32 => U::UInt64FromInt32,
            Self::UInt64FromInt64 => U::UInt64FromInt64,
        }
    }
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
    /// Import only the arithmetic storage fragment. Do not traverse a Bool,
    /// Integer conversion, pointer, or other opaque payload to reject it.
    pub(crate) fn machine_arithmetic(
        &mut self,
        result: MachineIntegerType,
        term: &Bitvector32Term,
    ) -> Option<KernelTerm> {
        use Bitvector32Term as Old;
        use KernelMachineLiteral as Literal;
        let node = match term {
            Old::Binary {
                op,
                format,
                left,
                right,
            } => KernelTermNode::MachineBinary {
                format: *format,
                operator: *op,
                arguments: [
                    self.machine_arithmetic(*format, left)?,
                    self.machine_arithmetic(*format, right)?,
                ],
            },
            Old::Unary {
                op,
                format,
                operand,
            } => KernelTermNode::MachineUnary {
                format: *format,
                operator: *op,
                operand: self.machine_arithmetic(*format, operand)?,
            },
            value
                if value
                    .as_unary()
                    .and_then(|(op, _)| KernelMachineCastEncoding::of_unary(op))
                    .is_some() =>
            {
                let (op, operand) = value.as_unary()?;
                let (encoding, source, destination) = KernelMachineCastEncoding::of_unary(op)?;
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand: self.machine_arithmetic(source, operand)?,
                }
            }
            Old::Variable(value) => KernelTermNode::Variable(*value),
            Old::Constant(value) => KernelTermNode::MachineLiteral(Literal::Word32(*value)),
            Old::UInt32Constant(value) => KernelTermNode::MachineLiteral(Literal::UInt32(*value)),
            Old::Int64Constant(value) => KernelTermNode::MachineLiteral(Literal::Int64(*value)),
            Old::UInt64Constant(value) => KernelTermNode::MachineLiteral(Literal::UInt64(*value)),
            Old::MachineIntegerConstant(value) => {
                KernelTermNode::MachineLiteral(Literal::Wide(*value))
            }
            _ => return None,
        };
        // Interning charges the one selected source node; no other bridge
        // or evaluator is invoked for these literal/variable leaves.
        Some(KernelTerm::intern(KernelType::C(result.c_type()), node))
    }

    pub(crate) fn machine(
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
            Old::BoolCast { to, value } => Node::BoolCast {
                destination: *to,
                operand: self.condition(value),
            },
            Old::IntegerToMachine { value, destination } => Node::IntegerToMachine {
                destination: *destination,
                operand: self.integer(value),
            },
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
    pub(crate) fn machine(term: &KernelTerm) -> Result<Bitvector32Term, &'static str> {
        use Bitvector32Term as Old;
        use KernelTermNode as Node;
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::MachineLiteral(value) => value.legacy_term(),
            Node::Variable(variable) => Old::Variable(*variable),
            Node::BoolCast {
                destination,
                operand,
            } => Old::BoolCast {
                to: *destination,
                value: Box::new(Self::condition(operand)?),
            },
            Node::IntegerToMachine {
                destination,
                operand,
            } => Old::IntegerToMachine {
                value: Self::default().integer(operand)?,
                destination: *destination,
            },
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
    fn integer_conversion_preserves_destination_and_operand_without_folding() {
        for destination in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt128,
        ] {
            let operand: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::constant_i64(1).into(),
                IntegerTerm::constant_i64(2).into(),
            )
            .into();
            let source = PureFunctionArgument::Value(wrap_exact(
                destination,
                Bitvector32Term::IntegerToMachine {
                    value: operand,
                    destination,
                },
            ));
            let common = KernelTermImport::default().argument(&source);
            assert!(
                matches!(common.node(), KernelTermNode::IntegerToMachine { destination: actual, .. } if *actual == destination)
            );
            assert_eq!(common.children()[0].ty(), &KernelType::Integer);
            assert!(matches!(
                common.children()[0].node(),
                KernelTermNode::IntegerOperation { .. }
            ));
            assert_eq!(
                KernelTermExport::default().argument(&common).unwrap(),
                source
            );
            drop(source);
            let restored = KernelTermExport::default().argument(&common).unwrap();
            assert_eq!(KernelTermImport::default().argument(&restored), common);
        }
    }

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

thread_local! {
    static CHECKED_CASTS: std::cell::RefCell<std::collections::HashMap<(u64, MachineIntegerType, MachineIntegerType), KernelTerm>> = Default::default();
}

impl KernelTerm {
    /// Checking-only reconstruction of a generic cast over the shared arithmetic
    /// fragment. Children stay shared; literal folding matches the old checker.
    pub(crate) fn clear_cast_checks() {
        CHECKED_CASTS.with(|cache| cache.borrow_mut().clear());
    }

    pub(crate) fn checking_machine_cast(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Self {
        assert!(self.is_shared_machine_operand());
        CHECKED_CASTS.with(|cache| {
            let mut cache = cache.borrow_mut();
            let mut term = self.clone();
            let mut source = source;
            let mut path = Vec::new();
            let result = loop {
                crate::instrumentation::record_deterministic_work(1);
                let key = (term.id(), source, destination);
                if let Some(result) = cache.get(&key) {
                    break result.clone();
                }
                path.push(key);
                if source == destination {
                    break term.with_machine_observation_type(destination);
                }
                if let KernelTermNode::MachineLiteral(literal) = term.node()
                    && let Some(constant) = source.constant_from_term(&literal.legacy_term())
                {
                    let value = destination
                        .constant_term(constant.convert_modulo(destination.format()))
                        .expect("matching format");
                    break KernelTermImport::default().machine(destination, &value);
                }
                if let KernelTermNode::MachineCast {
                    encoding: KernelMachineCastEncoding::Generic,
                    source: original,
                    destination: intermediate,
                    operand,
                } = term.node()
                    && original.carrier_bytes() == 4
                    && source.carrier_bytes() == 4
                    && destination.carrier_bytes() == 4
                    && *intermediate == source
                    && destination.format().bits() <= intermediate.format().bits()
                {
                    source = *original;
                    term = operand.clone();
                    continue;
                }
                break Self::checking_cast_node(
                    term,
                    source,
                    destination,
                    KernelMachineCastEncoding::Generic,
                );
            };
            for key in path {
                cache.insert(key, result.clone());
            }
            result
        })
    }

    fn checking_cast_node(
        operand: Self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        encoding: KernelMachineCastEncoding,
    ) -> Self {
        Self::machine_cast_shared(
            encoding,
            source,
            destination,
            operand.with_machine_observation_type(source),
        )
    }

    /// The low-word constructor's root arithmetic policy, without exporting
    /// either child. This is used by checking, never Surface lowering.
    pub(crate) fn checking_low_word(&self) -> Self {
        assert!(self.is_shared_machine_operand());
        use KernelMachineLiteral as L;
        use MachineIntegerType as Ty;
        let literal =
            |bits| KernelTermImport::default().machine(Ty::Int32, &Bitvector32Term::Constant(bits));
        let root = |value: &Self| match value.node() {
            KernelTermNode::MachineLiteral(L::Int64(bits)) => literal(*bits as u32),
            KernelTermNode::MachineLiteral(L::UInt64(bits)) => literal(*bits as u32),
            KernelTermNode::MachineCast {
                encoding:
                    KernelMachineCastEncoding::Int64From32
                    | KernelMachineCastEncoding::UInt64From32
                    | KernelMachineCastEncoding::Int64FromUInt32
                    | KernelMachineCastEncoding::UInt64FromInt32,
                operand,
                ..
            } => operand.with_machine_observation_type(Ty::Int32),
            _ => Self::checking_cast_node(
                value.clone(),
                Ty::UInt64,
                Ty::UInt32,
                KernelMachineCastEncoding::UInt32From64,
            )
            .with_machine_observation_type(Ty::Int32),
        };
        let operation = match self.node() {
            KernelTermNode::MachineBinary {
                format: Ty::UInt64,
                operator: op @ (MachineBinaryOp::Add | MachineBinaryOp::Subtract),
                arguments: [a, b],
            } => match (a.node(), b.node()) {
                (_, KernelTermNode::MachineLiteral(L::UInt64(bits))) => {
                    Some((*op, root(a), literal(*bits as u32)))
                }
                (KernelTermNode::MachineLiteral(L::UInt64(bits)), _)
                    if *op == MachineBinaryOp::Add =>
                {
                    Some((*op, literal(*bits as u32), root(b)))
                }
                _ => None,
            },
            _ => None,
        };
        let Some((operator, a, b)) = operation else {
            return root(self);
        };
        let bits = |value: &Self| match value.node() {
            KernelTermNode::MachineLiteral(L::Word32(bits) | L::UInt32(bits)) => Some(*bits),
            _ => None,
        };
        if let (Some(a), Some(b)) = (bits(&a), bits(&b)) {
            return literal(if operator == MachineBinaryOp::Add {
                a.wrapping_add(b)
            } else {
                a.wrapping_sub(b)
            });
        }
        if bits(&b) == Some(0) {
            return a;
        }
        if operator == MachineBinaryOp::Add && bits(&a) == Some(0) {
            return b;
        }
        Self::intern(
            KernelType::C(Ty::Int32.c_type()),
            KernelTermNode::MachineBinary {
                format: Ty::Int32,
                operator,
                arguments: [a, b],
            },
        )
    }

    pub(crate) fn checking_legacy_machine_conversion(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Self {
        use crate::kernel::machine_integer::conversion::{
            ConversionLowering as C, ConversionPolicy, convert_value, lower,
        };
        use KernelMachineCastEncoding as E;
        assert!(self.is_shared_machine_operand());
        if let KernelTermNode::MachineLiteral(literal) = self.node() {
            let value = convert_value(source.value_from_term(literal.legacy_term()), destination)
                .expect("integer conversion");
            return KernelTermImport::default().argument(&PureFunctionArgument::Value(value));
        }
        let value = match lower(source, destination, ConversionPolicy::Modular).lowering {
            C::Identity => self.clone(),
            C::Cast | C::SignCast => self.checking_machine_cast(source, destination),
            C::LowWord => self.checking_low_word(),
            C::Reinterpret64 if destination.format().is_signed() => self.clone(),
            C::Reinterpret64 => {
                if matches!(
                    self.node(),
                    KernelTermNode::MachineCast {
                        encoding: E::UInt64FromInt64,
                        ..
                    }
                ) {
                    self.clone()
                } else {
                    Self::checking_cast_node(self.clone(), source, destination, E::UInt64FromInt64)
                }
            }
            C::Extend64 => {
                let encoding = match (
                    source.format().is_signed(),
                    destination.format().is_signed(),
                ) {
                    (true, true) => E::Int64From32,
                    (false, true) => E::Int64FromUInt32,
                    (true, false) => E::UInt64FromInt32,
                    (false, false) => E::UInt64From32,
                };
                if matches!(self.node(), KernelTermNode::MachineCast {encoding: actual, ..} if *actual == encoding)
                {
                    self.clone()
                } else {
                    Self::checking_cast_node(self.clone(), source, destination, encoding)
                }
            }
        };
        if let KernelTermNode::MachineLiteral(literal) = value.node() {
            return KernelTermImport::default().machine(
                destination,
                &literal
                    .legacy_term()
                    .in_format32(destination)
                    .in_narrow_format(destination),
            );
        }
        value.with_machine_observation_type(destination)
    }
}
