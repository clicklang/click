//! Lossless machine-value boundary. Result type and operator format are
//! separate: a uint32 value can contain a sign-free int32 word operation.
use super::*;
use crate::kernel::MachineCastSpelling;

fn retained_machine_input(node: &KernelTermNode) -> Option<&OldMachineTerm> {
    match node {
        KernelTermNode::MachineObservationInput { observation, .. } => Some(observation.value()),
        KernelTermNode::WrittenMachine(value) => Some(value.value()),
        _ => None,
    }
}

impl KernelTerm {
    pub(crate) fn int32_literal(bits: u32) -> Self {
        Self::intern(
            KernelType::Program(ProgramType::Int32),
            KernelTermNode::MachineLiteral(KernelMachineLiteral::Word32(bits)),
        )
    }

    /// Wide shifts accept a literal count at either word width.
    pub(super) fn literal_shift_count(&self) -> Option<u32> {
        self.machine_literal()?.shift_count()
    }

    /// Read only literal roots, including a selected native compatibility input.
    pub(in crate::kernel) fn machine_literal(&self) -> Option<KernelMachineLiteral> {
        match self.node() {
            KernelTermNode::MachineLiteral(value) => Some(value.clone()),
            _ => {
                let OldMachineTerm::Constant { format, bits } = self
                    .retained_machine_input()
                    .or_else(|| self.written_machine_input())?
                else {
                    return None;
                };
                Some(KernelMachineLiteral::from_term_bits(*format, *bits))
            }
        }
    }

    /// Borrow a selected operand already owned by its machine input.
    pub(crate) fn retained_machine_input(&self) -> Option<&OldMachineTerm> {
        retained_machine_input(self.node())
    }

    /// Borrow a machine operand inside a generic scalar or argument descriptor.
    pub(in crate::kernel) fn written_machine_input(&self) -> Option<&OldMachineTerm> {
        if let KernelTermNode::ImportedScalar(input) = self.node() {
            MachineIntegerType::from_program_type(input.carrier())?;
            return Some(input.value());
        }
        let PureFunctionArgument::Value(integer_c_value!(value)) = self.written_argument()? else {
            return None;
        };
        Some(value)
    }

    pub(crate) fn machine_if_shared(format: MachineIntegerType, arguments: [Self; 3]) -> Self {
        debug_assert_eq!(arguments[0].ty(), &KernelType::Bool);
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::MachineIf { arguments },
        )
    }
    /// Certificate source matching reads typed machine arguments directly.
    /// Other argument domains retain the written compatibility policy.
    pub(in crate::kernel) fn machine_call_identity(
        &self,
    ) -> Option<std::sync::Arc<PureApplicationIdentity>> {
        let KernelTermNode::Call { name, arguments } = self.node() else {
            return None;
        };
        match self.0.machine_leaf.0.get() {
            Some(MachineLeaf::Application(application)) => return Some(application.identity()),
            Some(MachineLeaf::Old(_)) => {}
            None => {
                if let Some(identity) =
                    SharedPureApplication::identity_for_machine_roots(name, arguments)
                {
                    return Some(identity);
                }
            }
        }
        let OldMachineTerm::ClickFunctionApplication { name, arguments } =
            self.machine_conversion_leaf()?
        else {
            return None;
        };
        Some(SharedPureApplication::identity_for(name, arguments))
    }

    /// An explicitly retained native leaf or the compatibility reading of a
    /// mathematical integer conversion. The surrounding machine DAG is never
    /// exported; conversion Integer payloads stay shared.
    pub(crate) fn machine_conversion_leaf(&self) -> Option<&OldMachineTerm> {
        if let KernelTermNode::ThreadHandle(id) = self.node() {
            return Some(
                self.0
                    .machine_leaf
                    .get_or_init(|| OldMachineTerm::ThreadHandle(*id)),
            );
        }
        if let KernelTermNode::IntegerAddress {
            address,
            object_class,
            ..
        } = self.node()
        {
            return Some(self.0.machine_leaf.get_or_init(|| {
                OldMachineTerm::IntegerAddress(
                    Box::new(address.export().expect("address observation")),
                    AddressObjectClass::new(object_class.clone()),
                )
            }));
        }
        if let Some(operand) = self.retained_machine_input() {
            return Some(operand);
        }
        if let KernelTermNode::Call { name, arguments } = self.node()
            && matches!(self.ty(), KernelType::Program(ty) if MachineIntegerType::from_program_type(*ty).is_some())
        {
            // A bounded compatibility reading of this root. Machine arguments
            // keep their shared handles; no surrounding prefix is exported.
            return Some(self.0.machine_leaf.get_or_init(|| {
                crate::instrumentation::record_deterministic_work(name.len() + arguments.len() + 1);
                let mut export = KernelTermExport::default();
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        if let KernelType::Program(ty) = argument.ty()
                            && let Some(format) = MachineIntegerType::from_program_type(*ty)
                            && let Some(value) =
                                SharedMachineIntegerTerm::from_shared(format, argument.clone())
                        {
                            PureFunctionArgument::SharedMachine(value)
                        } else {
                            export.argument(argument).expect("typed call argument")
                        }
                    })
                    .collect();
                OldMachineTerm::ClickFunctionApplication {
                    name: name.clone(),
                    arguments,
                }
            }));
        }
        if let KernelTermNode::BoolCast {
            destination,
            operand,
        } = self.node()
        {
            return Some(self.0.machine_leaf.get_or_init(|| {
                OldMachineTerm::BoolCast {
                    to: *destination,
                    value: Box::new(
                        BooleanOperandView::Shared(operand)
                            .identity_leaf()
                            .into_owned(),
                    ),
                }
            }));
        }
        let KernelTermNode::IntegerToMachine {
            destination,
            operand,
        } = self.node()
        else {
            return None;
        };
        Some(self.0.machine_leaf.get_or_init(|| {
            OldMachineTerm::IntegerToMachine {
                destination: *destination,
                value: KernelTermExport::default()
                    .integer(operand)
                    .expect("Integer conversion operand"),
            }
        }))
    }

    /// Retain a legacy machine operator over shared children without folding.
    /// Child interpretation is supplied by the caller, as in the legacy node.
    pub(crate) fn machine_binary_shared(
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [Self; 2],
    ) -> Self {
        Self::machine_binary_shared_as(format, format, operator, arguments)
    }

    /// A checking word reading can have a different result interpretation from
    /// its operator format. Build that root directly, without an intermediate
    /// node followed by `with_machine_observation_type`.
    pub(crate) fn machine_binary_shared_as(
        result: MachineIntegerType,
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [Self; 2],
    ) -> Self {
        Self::intern(
            KernelType::Program(result.program_type()),
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
            KernelType::Program(format.program_type()),
            KernelTermNode::MachineUnary {
                format,
                operator,
                operand,
            },
        )
    }

    pub(crate) fn machine_cast_shared(
        encoding: MachineCastSpelling,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        operand: Self,
    ) -> Self {
        Self::intern(
            KernelType::Program(destination.program_type()),
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
        if self.ty() == &KernelType::Program(format.program_type()) {
            return self.clone();
        }
        if !matches!(
            self.node(),
            KernelTermNode::MachineIf { .. } | KernelTermNode::Match(_)
        ) {
            return Self::intern(
                KernelType::Program(format.program_type()),
                self.node().clone(),
            );
        }
        // A conditional's arms have its observation type, unlike an arithmetic
        // operator whose own format determines its operands. Reinterpret the
        // selected word at every conditional arm, exactly as native import
        // does. Memoize DAG nodes so repeated signed/unsigned key readings do
        // not expand shared branches or revisit an already read suffix.
        CONDITIONAL_READINGS.with(|cache| {
            let mut cache = cache.borrow_mut();
            let mut pending = vec![(self, false)];
            while let Some((term, finish)) = pending.pop() {
                let key = (term.id(), format);
                if cache.contains_key(&key) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if term.ty() == &KernelType::Program(format.program_type()) {
                    cache.insert(key, term.clone());
                    continue;
                }
                let value = if let KernelTermNode::MachineIf { arguments } = term.node() {
                    if !finish {
                        pending.push((term, true));
                        pending.extend(arguments[1..].iter().map(|arm| (arm, false)));
                        continue;
                    }
                    Self::machine_if_shared(
                        format,
                        [
                            arguments[0].clone(),
                            cache[&(arguments[1].id(), format)].clone(),
                            cache[&(arguments[2].id(), format)].clone(),
                        ],
                    )
                } else if let KernelTermNode::Match(matched) = term.node() {
                    if !finish {
                        pending.push((term, true));
                        pending.extend(matched.arguments[1..].iter().map(|arm| (arm, false)));
                        continue;
                    }
                    let mut matched = matched.clone();
                    matched.result_type = KernelType::Program(format.program_type());
                    for body in &mut matched.arguments[1..] {
                        *body = cache[&(body.id(), format)].clone();
                    }
                    matched.into_term()
                } else {
                    Self::intern(
                        KernelType::Program(format.program_type()),
                        term.node().clone(),
                    )
                };
                cache.insert(key, value);
            }
            cache[&(self.id(), format)].clone()
        })
    }

    /// Construct one arithmetic operation structurally from shared children.
    /// Signed definedness belongs to the evaluator's separate obligations.
    #[cfg(test)]
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
            .any(|arg| arg.ty() != &KernelType::Program(format.program_type()))
        {
            return Err("arithmetic requires matching 32-bit or 64-bit integer operands");
        }
        Ok(Self::intern(
            KernelType::Program(format.program_type()),
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
    /// A typed literal reading admits either 32-bit carrier at either
    /// 32-bit format. Every other width retains its written signedness.
    pub(crate) fn constant_at(&self, ty: MachineIntegerType) -> Option<MachineIntegerConstant> {
        let bits = match (self, ty) {
            (_, MachineIntegerType::Int32 | MachineIntegerType::UInt32) => {
                u128::from(self.word32()?)
            }
            (Self::Int64(value), MachineIntegerType::Int64) => u128::from(*value as u64),
            (Self::UInt64(value), MachineIntegerType::UInt64) => u128::from(*value),
            (Self::Wide(value), _) if value.format() == ty.format() => return Some(*value),
            _ => return None,
        };
        Some(MachineIntegerConstant::from_term_bits(ty.format(), bits))
    }

    fn converted_term(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Option<KernelTerm> {
        let value = self
            .constant_at(source)?
            .convert_modulo(destination.format());
        Some(Self::constant_term(value))
    }

    pub(super) fn shift_count(&self) -> Option<u32> {
        self.word32()
            .or_else(|| u32::try_from(self.signed64()?).ok())
    }

    pub(in crate::kernel) fn from_term_bits(format: MachineIntegerType, bits: u128) -> Self {
        match format {
            MachineIntegerType::Int32 => Self::Word32(bits as u32),
            MachineIntegerType::UInt32 => Self::UInt32(bits as u32),
            MachineIntegerType::Int64 => Self::Int64(bits as i64),
            MachineIntegerType::UInt64 => Self::UInt64(bits as u64),
            _ => Self::Wide(MachineIntegerConstant::from_term_bits(
                format.format(),
                bits,
            )),
        }
    }

    fn from_constant(value: MachineIntegerConstant) -> Self {
        Self::from_term_bits(MachineIntegerType::of_format(value.format()), value.bits())
    }

    pub(super) fn constant_term(value: MachineIntegerConstant) -> KernelTerm {
        let destination = MachineIntegerType::of_format(value.format());
        KernelTerm::intern(
            KernelType::Program(destination.program_type()),
            KernelTermNode::MachineLiteral(Self::from_constant(value)),
        )
    }

    /// Comparison and overflow constructors read a 32-bit literal as its word.
    pub(super) fn guard_operand(&self, format: MachineIntegerType) -> KernelTerm {
        let literal = if format.format().bits() == 32
            && let Some(bits) = self.word32()
        {
            Self::Word32(bits)
        } else if let Self::Wide(value) = self {
            Self::from_constant(*value)
        } else {
            self.clone()
        };
        KernelTerm::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::MachineLiteral(literal),
        )
    }

    pub(crate) fn word32(&self) -> Option<u32> {
        match self {
            Self::Word32(bits) | Self::UInt32(bits) => Some(*bits),
            Self::Wide(value) if value.format().bits() == 32 => Some(value.bits() as u32),
            _ => None,
        }
    }

    pub(crate) fn unsigned64(&self) -> Option<u64> {
        match self {
            Self::UInt64(bits) => Some(*bits),
            Self::Wide(value) if value.format() == MachineIntegerType::UInt64.format() => {
                Some(value.bits() as u64)
            }
            _ => None,
        }
    }

    /// The signed reader also accepts unsigned 64-bit words by their bits.
    pub(crate) fn signed64(&self) -> Option<i64> {
        match self {
            Self::Int64(value) => Some(*value),
            Self::Wide(value) if value.format() == MachineIntegerType::Int64.format() => {
                Some(value.bits() as i64)
            }
            _ => self.unsigned64().map(|bits| bits as i64),
        }
    }

    /// An atomic literal output, preserving its written carrier exactly.
    pub(crate) fn value_at(&self, format: MachineIntegerType) -> ProgramValue {
        wrap_exact(format, self.old_term())
    }

    pub(crate) fn old_term(&self) -> OldMachineTerm {
        match self {
            Self::Word32(bits) => OldMachineTerm::constant(*bits),
            Self::UInt32(bits) => OldMachineTerm::uint32_constant(*bits),
            Self::Int64(value) => OldMachineTerm::int64_constant(*value),
            Self::UInt64(value) => OldMachineTerm::uint64_constant(*value),
            Self::Wide(value) => OldMachineTerm::machine_constant(*value),
        }
    }
}

pub(super) fn native_constant_reading(operand: &OldMachineTerm) -> Option<KernelMachineLiteral> {
    operand
        .uint64_as_const()
        .map(KernelMachineLiteral::UInt64)
        .or_else(|| operand.int64_as_const().map(KernelMachineLiteral::Int64))
        .or_else(|| operand.as_const().map(KernelMachineLiteral::Word32))
}

/// Cached checking metadata, never a replacement for the structural node.
/// Apply the existing constant readers to one operator over literal children;
/// signed overflow and undefined division/shift readings remain absent.
pub(super) fn constant_reading(node: &KernelTermNode) -> Option<KernelMachineLiteral> {
    match node {
        KernelTermNode::MachineLiteral(value) => Some(value.clone()),
        // The native word reader recognizes the exact null address. Keep
        // the written zero offset distinct from an expression that evaluates to zero.
        KernelTermNode::IntegerAddress { address, .. }
            if matches!(address.atom(), AddressBase::Concrete(name) if name == "null")
                && matches!(address.offset().node(), KernelAddressOffset::Constant(0)) =>
        {
            Some(KernelMachineLiteral::UInt64(0))
        }
        KernelTermNode::MachineIf { arguments } => {
            let KernelTermNode::BoolLiteral(value) = arguments[0].node() else {
                return None;
            };
            let value = arguments[if *value { 1 } else { 2 }].machine_constant_reading()?;
            value
                .word32()
                .map(KernelMachineLiteral::Word32)
                .or_else(|| value.unsigned64().map(KernelMachineLiteral::UInt64))
                .or_else(|| value.signed64().map(KernelMachineLiteral::Int64))
        }
        KernelTermNode::MachineObservationInput { .. } | KernelTermNode::WrittenMachine(_) => {
            // Read the selected native leaf once, on introduction. Shared
            // parents reuse this metadata, including a literal-conditioned
            // native `If`, instead of exporting the enclosing DAG to read it.
            native_constant_reading(retained_machine_input(node)?)
        }
        KernelTermNode::MachineBinary {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            operator,
            arguments: [left, right],
        } => {
            let bits = operator.evaluate_word32(
                *format,
                left.machine_constant_reading()?.word32()?,
                right.machine_constant_reading()?.word32()?,
            )?;
            Some(if *format == MachineIntegerType::Int32 {
                KernelMachineLiteral::Word32(bits)
            } else {
                KernelMachineLiteral::UInt32(bits)
            })
        }
        KernelTermNode::MachineBinary {
            format,
            operator,
            arguments: [left, right],
        } => {
            let left = left.machine_constant_reading()?;
            let rhs = right.machine_constant_reading()?;
            Some(match format {
                MachineIntegerType::Int64 => {
                    let right = if operator.is_shift() {
                        i64::from(right.literal_shift_count()?)
                    } else {
                        rhs.signed64()?
                    };
                    KernelMachineLiteral::Int64(operator.evaluate_int64(left.signed64()?, right)?)
                }
                MachineIntegerType::UInt64 => {
                    let right = if operator.is_shift() {
                        u64::from(right.literal_shift_count()?)
                    } else {
                        rhs.unsigned64()?
                    };
                    KernelMachineLiteral::UInt64(
                        operator.evaluate_uint64(left.unsigned64()?, right)?,
                    )
                }
                _ => return None,
            })
        }
        KernelTermNode::MachineUnary {
            format,
            operator: MachineUnaryOp::BitwiseNot,
            operand,
        } => {
            let literal = operand.machine_constant_reading()?;
            Some(match format {
                MachineIntegerType::Int32 => KernelMachineLiteral::Word32(!literal.word32()?),
                MachineIntegerType::UInt32 => KernelMachineLiteral::UInt32(!literal.word32()?),
                MachineIntegerType::Int64 => KernelMachineLiteral::Int64(!literal.signed64()?),
                MachineIntegerType::UInt64 => KernelMachineLiteral::UInt64(!literal.unsigned64()?),
                _ => return None,
            })
        }
        KernelTermNode::MachineCast {
            encoding, operand, ..
        } => {
            use MachineCastSpelling as Cast;
            let reading = operand.machine_constant_reading()?;
            // Extensions accept narrow constants only at a literal root.
            // Computed operands must already have a readable wide value.
            let literal = operand.machine_literal();
            let word = literal.as_ref().and_then(KernelMachineLiteral::word32);
            Some(match encoding {
                Cast::Generic | Cast::UInt32From64 => return None,
                Cast::Int64From32 | Cast::Int64FromUInt32 => {
                    let value = match word {
                        Some(bits) if *encoding == Cast::Int64From32 => i64::from(bits as i32),
                        Some(bits) => i64::from(bits),
                        None => reading.signed64()?,
                    };
                    KernelMachineLiteral::Int64(value)
                }
                Cast::UInt64From32 | Cast::UInt64FromInt32 => {
                    let bits = match word {
                        Some(bits) if *encoding == Cast::UInt64FromInt32 => {
                            i64::from(bits as i32) as u64
                        }
                        Some(bits) => u64::from(bits),
                        None => reading.unsigned64()?,
                    };
                    KernelMachineLiteral::UInt64(bits)
                }
                Cast::UInt64FromInt64 => {
                    let bits = if literal.is_some() {
                        reading.signed64()? as u64
                    } else {
                        reading.unsigned64()?
                    };
                    KernelMachineLiteral::UInt64(bits)
                }
            })
        }
        _ => None,
    }
}

/// The kernel reads a conversion's spelling as the term does: its
/// `MachineCast` node keeps the [`MachineCastSpelling`], so an
/// import/export round trip preserves the exact constructor.
impl MachineCastSpelling {
    pub(crate) fn of_unary(
        op: BitvectorUnaryOp,
    ) -> Option<(Self, MachineIntegerType, MachineIntegerType)> {
        match op {
            BitvectorUnaryOp::Cast { spelling, from, to } => Some((spelling, from, to)),
            _ => None,
        }
    }

    pub(crate) fn unary(
        self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> BitvectorUnaryOp {
        let (from, to) = self.legacy_formats().unwrap_or((source, destination));
        BitvectorUnaryOp::Cast {
            spelling: self,
            from,
            to,
        }
    }
}

pub(in crate::kernel) fn wrap_exact(
    format: MachineIntegerType,
    term: OldMachineTerm,
) -> ProgramValue {
    // value_from_term applies the word-format convention. This adapter must
    // preserve the payload exactly, including constants inside operations.
    match format {
        MachineIntegerType::Int8 => ProgramValue::Int8(term),
        MachineIntegerType::UInt8 => ProgramValue::UInt8(term),
        MachineIntegerType::Int16 => ProgramValue::Int16(term),
        MachineIntegerType::UInt16 => ProgramValue::UInt16(term),
        MachineIntegerType::Int32 => ProgramValue::Int32(term),
        MachineIntegerType::UInt32 => ProgramValue::UInt32(term),
        MachineIntegerType::Int64 => ProgramValue::Int64(term),
        MachineIntegerType::UInt64 => ProgramValue::UInt64(term),
        MachineIntegerType::Int128 => ProgramValue::Int128(term),
        MachineIntegerType::UInt128 => ProgramValue::UInt128(term),
    }
}

impl KernelTermImport {
    /// Import arithmetic and typed Integer conversion leaves. Bool, pointer,
    /// and other opaque payloads retain their existing compatibility boundary.
    pub(crate) fn machine_arithmetic(
        &mut self,
        result: MachineIntegerType,
        term: &OldMachineTerm,
    ) -> Option<KernelTerm> {
        use KernelMachineLiteral as Literal;
        use OldMachineTerm as Old;
        if matches!(term, Old::MemoryLoad(..))
            || matches!(term, Old::Variable(v) if crate::kernel::registered_load_kind_for_variable(v).is_some())
        {
            return self.scalar_read(result, term);
        }
        if let Some(root) = self.float_to_machine(result, term) {
            return Some(root);
        }
        let node = match term {
            Old::AlgebraicMatch { .. } => {
                return Some(KernelMatch::import_machine(self, result, term)?.into_term());
            }
            Old::RangeFold { .. } => {
                return Some(
                    KernelFold::import_machine(self, term)?
                        .into_term()
                        .with_machine_observation_type(result),
                );
            }
            Old::If {
                condition,
                then_term,
                else_term,
            } => KernelTermNode::MachineIf {
                arguments: [
                    self.condition(condition),
                    self.machine_arithmetic(result, then_term)?,
                    self.machine_arithmetic(result, else_term)?,
                ],
            },
            Old::BoolCast { to, value } => KernelTermNode::BoolCast {
                destination: *to,
                operand: self.condition(value),
            },
            Old::IntegerToMachine { value, destination } => {
                let operand = self.integer(value);
                if operand.has_opaque_observation_boundary() {
                    return None;
                }
                KernelTermNode::IntegerToMachine {
                    destination: *destination,
                    operand,
                }
            }
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
                    .and_then(|(op, _)| MachineCastSpelling::of_unary(op))
                    .is_some() =>
            {
                let (op, operand) = value.as_unary()?;
                let (encoding, source, destination) = MachineCastSpelling::of_unary(op)?;
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand: self.machine_arithmetic(source, operand)?,
                }
            }
            Old::ThreadHandle(id) => KernelTermNode::ThreadHandle(*id),
            Old::Variable(value) => KernelTermNode::Variable(*value),
            Old::Constant { format, bits } => {
                KernelTermNode::MachineLiteral(Literal::from_term_bits(*format, *bits))
            }
            _ => return None,
        };
        // Interning charges the one selected source node; no other bridge
        // or evaluator is invoked for these literal/variable leaves.
        Some(KernelTerm::intern(
            KernelType::Program(result.program_type()),
            node,
        ))
    }

    /// Construct a common machine call root. Numeric children retain their
    /// structure; opaque argument
    /// descriptors retain this producer's exact payload, not a semantic alias.
    pub(crate) fn machine_call(
        &mut self,
        result: MachineIntegerType,
        application: &SharedPureApplication,
    ) -> KernelTerm {
        let arguments = application
            .arguments()
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                if self.exact_field_inputs {
                    if matches!(argument, PureFunctionArgument::SharedMachine(_)) {
                        // This is a typed input descriptor, not a boxed value
                        // argument. Keep its existing shared operand and exact
                        // envelope through native field storage/output.
                        KernelTerm::written_call_argument(application, index)
                    } else {
                        self.structural_argument(argument).unwrap_or_else(|| {
                            KernelTerm::written_call_argument(application, index)
                        })
                    }
                } else if let Some(root) = application.common_argument(index) {
                    root
                } else {
                    KernelTerm::written_call_argument(application, index)
                }
            })
            .collect();
        let root = KernelTerm::checked_call(
            KernelType::Program(result.program_type()),
            application.name().into(),
            arguments,
        );
        // Boxed numeric inputs have just been imported as shared children.
        // Their compatibility reading must use those handles, even if a later
        // producer reuses this root with an already-shared argument. Opaque
        // descriptors and shared numeric inputs can borrow the original call.
        crate::instrumentation::record_deterministic_work(application.arguments().len());
        if application
            .arguments()
            .iter()
            .all(|argument| !matches!(argument, PureFunctionArgument::Value(integer_c_value!(_))))
        {
            root.0.machine_leaf.retain_application(application);
        }
        root
    }

    pub(crate) fn machine(
        &mut self,
        result: MachineIntegerType,
        term: &OldMachineTerm,
    ) -> KernelTerm {
        use KernelMachineLiteral as Literal;
        use KernelTermNode as Node;
        use OldMachineTerm as Old;
        crate::instrumentation::record_deterministic_work(1);
        if matches!(
            result,
            MachineIntegerType::Int64 | MachineIntegerType::UInt64
        ) && let Old::IntegerAddress(address, object_class) = term
        {
            return KernelTerm::numeric_address_term(result, address, object_class.clone());
        }
        if let Some(read) = self.scalar_read(result, term) {
            return read;
        }
        if let Some(conversion) = self.float_to_machine(result, term) {
            return conversion;
        }
        let node = match term {
            Old::ThreadHandle(id) => Node::ThreadHandle(*id),
            Old::AlgebraicMatch { .. } => {
                return KernelMatch::import_machine(self, result, term)
                    .expect("machine match")
                    .into_term();
            }
            Old::RangeFold { .. } => {
                return KernelFold::import_machine(self, term)
                    .expect("machine fold")
                    .into_term()
                    .with_machine_observation_type(result);
            }
            Old::ClickFunctionApplication { name, arguments } => {
                return self.machine_call(
                    result,
                    &SharedPureApplication::intern(name.clone(), arguments.clone()),
                );
            }
            Old::If {
                condition,
                then_term,
                else_term,
            } => Node::MachineIf {
                arguments: [
                    self.condition(condition),
                    self.machine(result, then_term),
                    self.machine(result, else_term),
                ],
            },
            Old::Constant { format, bits } => {
                Node::MachineLiteral(Literal::from_term_bits(*format, *bits))
            }
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
            // A legacy spelling's formats are fixed: the low word reads its
            // operand as `uint64` bits, not as its source C type.
            Old::Cast {
                spelling,
                value,
                from,
                to,
            } => Node::MachineCast {
                encoding: *spelling,
                source: *from,
                destination: *to,
                operand: self.machine(*from, value),
            },
            // Unrecognized untyped intrinsics, wrong-sort float inputs and
            // read/address descriptors not admitted above keep exact payloads.
            // A slice application's count is an opaque `usize` leaf keyed by
            // its application, so it keeps its exact payload too.
            Old::PureFunctionApplication { .. }
            | Old::PureApplicationCount(_)
            | Old::MemoryLoad(..)
            | Old::IntegerAddress(..)
            | Old::Float32Negate(_)
            | Old::Float32Binary { .. }
            | Old::Float64Negate(_)
            | Old::Float64Binary { .. } => {
                return KernelTerm::imported_scalar(result.program_type(), term);
            }
        };
        KernelTerm::intern(KernelType::Program(result.program_type()), node)
    }
}

#[cfg(test)]
thread_local! {
    static MACHINE_EXPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl KernelTermExport {
    #[cfg(test)]
    pub(crate) fn machine_export_count() -> usize {
        MACHINE_EXPORT_COUNT.with(std::cell::Cell::get)
    }

    pub(crate) fn machine(term: &KernelTerm) -> Result<OldMachineTerm, &'static str> {
        use KernelTermNode as Node;
        use OldMachineTerm as Old;
        #[cfg(test)]
        MACHINE_EXPORT_COUNT.with(|count| count.set(count.get() + 1));
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::FloatConvert { .. } => Self::float_to_machine(term)?,
            Node::Fold(fold) => fold.export_machine()?,
            Node::Match(matched) => matched.export_machine(&mut KernelTermExport::default())?,
            Node::Call { name, arguments } if matches!(term.ty(), KernelType::Program(ty) if MachineIntegerType::from_program_type(*ty).is_some()) =>
            {
                let mut export = Self::default();
                Old::ClickFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|arg| export.argument(arg))
                        .collect::<Result<_, _>>()?,
                }
            }
            Node::MachineIf { arguments } => Old::If {
                condition: Box::new(Self::condition(&arguments[0])?),
                then_term: Box::new(Self::machine(&arguments[1])?),
                else_term: Box::new(Self::machine(&arguments[2])?),
            },
            Node::IntegerAddress {
                address,
                object_class,
                ..
            } => Old::IntegerAddress(
                Box::new(address.export()?),
                AddressObjectClass::new(object_class.clone()),
            ),
            Node::ThreadHandle(id) => Old::ThreadHandle(*id),
            Node::MachineLiteral(value) => value.old_term(),
            Node::Variable(variable) => Old::Variable(*variable),
            Node::MemoryLoad {
                point,
                address,
                kind,
            } => Old::read_named(point.clone(), address.export()?, *kind),
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
            } => Old::cast_node(*encoding, *source, *destination, Self::machine(operand)?),
            Node::MachineObservationInput { observation, .. } => observation.value().clone(),
            Node::WrittenMachine(value) => value.value().clone(),
            Node::ImportedScalar(_) | Node::ObservedArgument(_) | Node::CallArgument(_) => term
                .written_machine_input()
                .ok_or("expected a machine integer payload")?
                .clone(),
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
                OldMachineTerm::IntegerToMachine {
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
    fn only_the_exact_null_address_has_a_constant_word_reading() {
        let zero = KernelAddressOffset::Constant(0).into_shared().unwrap();
        let sum = KernelAddressOffset::Add([zero.clone(), zero])
            .into_shared()
            .unwrap();
        let null = Address::null();
        for (address, expected) in [
            (null.clone(), Some(0)),
            (null.offset_by_bytes(1), None),
            (
                null.with_offset(AddressOffset::try_from_shared(sum).unwrap()),
                None,
            ),
            (Address::symbolic(Variable(982815)), None),
        ] {
            let native =
                OldMachineTerm::IntegerAddress(Box::new(address), AddressObjectClass::NONE);
            assert_eq!(native.bitvector64_as_const(), expected);
            let root = KernelTermImport::default().machine(MachineIntegerType::UInt64, &native);
            assert_eq!(
                MachineOperandView::Shared(&root).uint64_constant(),
                expected
            );
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
                MachineIntegerType::Int32 => OldMachineTerm::constant(u32::MAX),
                MachineIntegerType::UInt32 => OldMachineTerm::uint32_constant(u32::MAX),
                MachineIntegerType::Int64 => OldMachineTerm::int64_constant(i64::MIN),
                _ => OldMachineTerm::uint64_constant(u64::MAX),
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
                let bits = OldMachineTerm::Binary {
                    format,
                    op: operator,
                    left: Box::new(OldMachineTerm::Variable(Variable(991100))),
                    right: Box::new(constant.clone()),
                };
                let source = PureFunctionArgument::Value(wrap_exact(format, bits));
                let common = KernelTermImport::default().argument(&source);
                assert_eq!(common.ty(), &KernelType::Program(format.program_type()));
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
        let source = PureFunctionArgument::Value(ProgramValue::UInt32(OldMachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::constant(1)),
            right: Box::new(OldMachineTerm::uint32_constant(1)),
        }));
        let term = KernelTermImport::default().argument(&source);
        assert_ne!(term.children()[0], term.children()[1]);
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }

    #[test]
    fn specialized_casts_share_typed_nodes_without_losing_their_encoding() {
        use MachineCastSpelling as S;
        use MachineIntegerType as Ty;
        use OldMachineTerm as Old;
        let casts = [
            (S::Int64From32, Ty::Int32, Ty::Int64),
            (S::UInt64From32, Ty::UInt32, Ty::UInt64),
            (S::UInt32From64, Ty::UInt64, Ty::UInt32),
            (S::Int64FromUInt32, Ty::UInt32, Ty::Int64),
            (S::UInt64FromInt32, Ty::Int32, Ty::UInt64),
            (S::UInt64FromInt64, Ty::Int64, Ty::UInt64),
        ];
        for (spelling, source, destination) in casts {
            let constructor = |value| Old::legacy_cast(spelling, value);
            let operand = Old::Variable(Variable(991103));
            let value = PureFunctionArgument::Value(wrap_exact(
                destination,
                constructor(Box::new(operand.clone())),
            ));
            let common = KernelTermImport::default().argument(&value);
            assert!(matches!(common.node(), KernelTermNode::MachineCast { .. }));
            assert_eq!(
                common.children()[0].ty(),
                &KernelType::Program(source.program_type())
            );
            assert!(matches!(
                common.children()[0].node(),
                KernelTermNode::Variable(_)
            ));
            assert_eq!(
                common.ty(),
                &KernelType::Program(destination.program_type())
            );
            assert_eq!(
                KernelTermExport::default().argument(&common).unwrap(),
                value
            );
            assert_eq!(KernelTermImport::default().argument(&value), common);
            let generic = PureFunctionArgument::Value(wrap_exact(
                destination,
                Old::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    to: destination,
                    value: Box::new(operand),
                },
            ));
            assert_ne!(KernelTermImport::default().argument(&generic), common);
        }
    }

    #[test]
    fn machine_import_keeps_complete_pointer_integer_metadata() {
        let value = ProgramValue::UInt64(OldMachineTerm::Variable(Variable(991101)))
            .complete_word(Address::symbolic(Variable(991102)));
        let source = PureFunctionArgument::Value(value);
        let term = KernelTermImport::default().argument(&source);
        assert!(matches!(term.node(), KernelTermNode::NativeDescriptor(_)));
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }

    #[test]
    fn machine_cast_bridge_keeps_source_and_destination_without_evaluation() {
        let source = PureFunctionArgument::Value(ProgramValue::UInt64(OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::Int32,
            to: MachineIntegerType::UInt64,
            value: Box::new(OldMachineTerm::constant(u32::MAX)),
        }));
        let term = KernelTermImport::default().argument(&source);
        assert_eq!(
            term.children()[0].ty(),
            &KernelType::Program(ProgramType::Int32)
        );
        assert_eq!(term.ty(), &KernelType::Program(ProgramType::UInt64));
        assert!(matches!(term.node(), KernelTermNode::MachineCast { .. }));
        assert_eq!(KernelTermExport::default().argument(&term).unwrap(), source);
    }
}

thread_local! {
    static CONDITIONAL_READINGS: std::cell::RefCell<std::collections::HashMap<(u64, MachineIntegerType), KernelTerm>> = Default::default();
    static CHECKED_CASTS: std::cell::RefCell<std::collections::HashMap<(u64, MachineIntegerType, MachineIntegerType, bool), KernelTerm>> = Default::default();
}

impl KernelTerm {
    /// Checking-only reconstruction of a generic cast over the shared arithmetic
    /// fragment. Children stay shared; literal folding matches the old checker.
    pub(crate) fn clear_cast_checks() {
        CHECKED_CASTS.with(|cache| cache.borrow_mut().clear());
        CONDITIONAL_READINGS.with(|cache| cache.borrow_mut().clear());
    }

    pub(crate) fn checking_machine_cast(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Self {
        self.checking_machine_cast_with_policy(source, destination, false)
    }

    /// Generated premises preserve the native constructor's written inverse
    /// sign-cast pair; comparison readings may compose that pair instead.
    pub(crate) fn checking_machine_cast_preserving_sign_pairs(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Self {
        self.checking_machine_cast_with_policy(source, destination, true)
    }

    fn checking_machine_cast_with_policy(
        &self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        preserve_sign_pairs: bool,
    ) -> Self {
        assert!(self.is_shared_machine_operand());
        // A 32-to-64-bit extension has the one typed spelling lowering builds.
        if crate::kernel::machine_integer::conversion::extension_encoding(source, destination)
            .is_some()
        {
            return self.checking_legacy_machine_conversion(source, destination);
        }
        CHECKED_CASTS.with(|cache| {
            let mut cache = cache.borrow_mut();
            let mut term = self.clone();
            let mut source = source;
            let mut path = Vec::new();
            let result = loop {
                crate::instrumentation::record_deterministic_work(1);
                let key = (term.id(), source, destination, preserve_sign_pairs);
                if let Some(result) = cache.get(&key) {
                    break result.clone();
                }
                path.push(key);
                if source == destination {
                    break term.with_machine_observation_type(destination);
                }
                if let KernelTermNode::MachineLiteral(literal) = term.node()
                    && let Some(result) = literal.converted_term(source, destination)
                {
                    break result;
                }
                if let KernelTermNode::MachineCast {
                    encoding: MachineCastSpelling::Generic,
                    source: original,
                    destination: intermediate,
                    operand,
                } = term.node()
                    && original.carrier_bytes() == 4
                    && source.carrier_bytes() == 4
                    && destination.carrier_bytes() == 4
                    && *intermediate == source
                    && destination.format().bits() <= intermediate.format().bits()
                    && !(preserve_sign_pairs
                        && *original == destination
                        && crate::kernel::is_sign_cast32(*original, *intermediate))
                {
                    source = *original;
                    term = operand.clone();
                    continue;
                }
                break Self::checking_cast_node(
                    term,
                    source,
                    destination,
                    MachineCastSpelling::Generic,
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
        encoding: MachineCastSpelling,
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
        let root = |value: &Self| match value.node() {
            KernelTermNode::MachineLiteral(L::Int64(bits)) => Self::int32_literal(*bits as u32),
            KernelTermNode::MachineLiteral(L::UInt64(bits)) => Self::int32_literal(*bits as u32),
            KernelTermNode::MachineCast {
                encoding:
                    MachineCastSpelling::Int64From32
                    | MachineCastSpelling::UInt64From32
                    | MachineCastSpelling::Int64FromUInt32
                    | MachineCastSpelling::UInt64FromInt32,
                operand,
                ..
            } => operand.with_machine_observation_type(Ty::Int32),
            _ => Self::checking_cast_node(
                value.clone(),
                Ty::UInt64,
                Ty::UInt32,
                MachineCastSpelling::UInt32From64,
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
                    Some((*op, root(a), Self::int32_literal(*bits as u32)))
                }
                (KernelTermNode::MachineLiteral(L::UInt64(bits)), _)
                    if *op == MachineBinaryOp::Add =>
                {
                    Some((*op, Self::int32_literal(*bits as u32), root(b)))
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
            return Self::int32_literal(if operator == MachineBinaryOp::Add {
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
            KernelType::Program(Ty::Int32.program_type()),
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
        use MachineCastSpelling as E;
        assert!(self.is_shared_machine_operand());
        if let KernelTermNode::MachineLiteral(literal) = self.node() {
            if let Some(result) = literal.converted_term(source, destination) {
                return result;
            }
            // A literal can be observed through a different carrier. Lower
            // those conversions with the existing wrapper normalization.
            let value = convert_value(source.value_from_term(literal.old_term()), destination)
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
                    .old_term()
                    .in_format32(destination)
                    .in_narrow_format(destination),
            );
        }
        value.with_machine_observation_type(destination)
    }
}

#[cfg(test)]
mod call_tests {
    include!("machine_call_tests.rs");
}
