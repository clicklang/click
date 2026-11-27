//! Typed floating-point values. Import is structural: neither host floating-point
//! conversion nor constant evaluation changes a written carrier or its bits.
use super::*;
mod arithmetic;
mod call;
pub use call::KernelFloatCall;
mod condition;
mod conversion;
mod read;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum KernelFloatType {
    Float32,
    Float64,
}
impl KernelFloatType {
    pub(crate) fn from_program_type(ty: ProgramType) -> Option<Self> {
        match ty {
            ProgramType::Float32 => Some(Self::Float32),
            ProgramType::Float64 => Some(Self::Float64),
            _ => None,
        }
    }
    pub(crate) fn program_type(self) -> ProgramType {
        match self {
            Self::Float32 => ProgramType::Float32,
            Self::Float64 => ProgramType::Float64,
        }
    }
    fn carrier_bits(self, carrier: MachineIntegerType, bits: u128) -> Option<u64> {
        match (self, carrier) {
            (KernelFloatType::Float32, MachineIntegerType::Int32 | MachineIntegerType::UInt32) => {
                Some(u64::from(constant_u32(bits)))
            }
            (KernelFloatType::Float64, MachineIntegerType::UInt64) => Some(constant_u64(bits)),
            _ => None,
        }
    }
    pub(crate) fn value(self, term: OldMachineTerm) -> ProgramValue {
        match self {
            Self::Float32 => ProgramValue::Float32(term),
            Self::Float64 => ProgramValue::Float64(term),
        }
    }
}

/// Borrow the selected float root. Shape reads do not export an expression,
/// evaluate an operation or consult facts. Compound native payloads remain an
/// explicit boundary until their operation slices migrate.
#[derive(Clone, Copy)]
pub(crate) enum FloatOperandView<'a> {
    Native(KernelFloatType, &'a OldMachineTerm),
    Shared(&'a KernelTerm),
}
impl<'a> FloatOperandView<'a> {
    pub(crate) fn from_value(value: &'a ProgramValue) -> Option<Self> {
        match value {
            ProgramValue::Float32(term) => Some(Self::Native(KernelFloatType::Float32, term)),
            ProgramValue::Float64(term) => Some(Self::Native(KernelFloatType::Float64, term)),
            _ => None,
        }
    }
    pub(crate) fn from_shared(root: &'a KernelTerm) -> Option<Self> {
        let KernelType::Program(ty) = root.ty() else {
            return None;
        };
        KernelFloatType::from_program_type(*ty).map(|_| Self::Shared(root))
    }
    pub(crate) fn format(self) -> KernelFloatType {
        match self {
            Self::Native(format, _) => format,
            Self::Shared(root) => {
                let KernelType::Program(ty) = root.ty() else {
                    unreachable!("float view type");
                };
                KernelFloatType::from_program_type(*ty).expect("float view type")
            }
        }
    }
    pub(crate) fn literal(self) -> Option<(MachineIntegerType, u128)> {
        match self {
            Self::Native(_, OldMachineTerm::Constant { format, bits }) => Some((*format, *bits)),
            Self::Shared(root) => match root.node() {
                KernelTermNode::FloatLiteral { carrier, bits } => Some((*carrier, *bits)),
                KernelTermNode::ObservedArgument(_) | KernelTermNode::CallArgument(_) => {
                    Self::from_value(match root.written_argument()? {
                        PureFunctionArgument::Value(value) => value,
                        _ => return None,
                    })?
                    .literal()
                }
                _ => None,
            },
            _ => None,
        }
    }
    /// Read a literal operand without evaluating a compound float expression.
    pub(crate) fn literal_bits(self) -> Option<u64> {
        let (carrier, bits) = self.literal()?;
        self.format().carrier_bits(carrier, bits)
    }
    pub(crate) fn variable(self) -> Option<Variable> {
        match self {
            Self::Native(_, OldMachineTerm::Variable(variable)) => Some(*variable),
            Self::Shared(root) => match root.node() {
                KernelTermNode::Variable(variable) => Some(*variable),
                KernelTermNode::ObservedArgument(_) | KernelTermNode::CallArgument(_) => {
                    Self::from_value(match root.written_argument()? {
                        PureFunctionArgument::Value(value) => value,
                        _ => return None,
                    })?
                    .variable()
                }
                _ => None,
            },
            _ => None,
        }
    }
    /// Explicit selected native reading. Shared atoms have no child prefix;
    /// still-native compound operands are borrowed without cloning them.
    pub(crate) fn old_form(self) -> Option<&'a OldMachineTerm> {
        match self {
            Self::Native(_, term) => Some(term),
            Self::Shared(root) => match root.node() {
                KernelTermNode::FloatRead(_)
                | KernelTermNode::FloatLiteral { .. }
                | KernelTermNode::Variable(_) => {
                    Self::from_value(root.float_native_value()?)?.old_form()
                }
                KernelTermNode::ImportedScalar(input) => Some(input.value()),
                KernelTermNode::ObservedArgument(_) | KernelTermNode::CallArgument(_) => {
                    Self::from_value(match root.written_argument()? {
                        PureFunctionArgument::Value(value) => value,
                        _ => return None,
                    })?
                    .old_form()
                }
                _ => None,
            },
        }
    }
}

impl KernelTermImport {
    fn float_atom(&mut self, format: KernelFloatType, term: &OldMachineTerm) -> KernelTerm {
        crate::instrumentation::record_deterministic_work(1);
        if let OldMachineTerm::MemoryLoad(point, pointer, kind) = term
            && *kind == format.load_kind()
        {
            return KernelTerm::float_read(
                format,
                point.point().clone(),
                pointer.address().shared().clone(),
            );
        }
        let view = FloatOperandView::Native(format, term);
        let ty = KernelType::Program(format.program_type());
        if let Some((carrier, bits)) = view.literal() {
            KernelTerm::intern(ty, KernelTermNode::FloatLiteral { carrier, bits })
        } else if let Some(variable) = view.variable() {
            KernelTerm::variable(ty, variable)
        } else {
            KernelTerm::imported_scalar(format.program_type(), term)
        }
    }
}
#[cfg(test)]
thread_local! {
    static FLOAT_EXPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
impl KernelTermExport {
    #[cfg(test)]
    pub(crate) fn float_export_count() -> usize {
        FLOAT_EXPORT_COUNT.with(std::cell::Cell::get)
    }
    pub(crate) fn float(term: &KernelTerm) -> Result<ProgramValue, &'static str> {
        let view = FloatOperandView::from_shared(term).ok_or("expected float term")?;
        Ok(view.format().value(Self::float_machine(term)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn float_atoms_preserve_exact_bits_carriers_and_widths() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let carriers: &[MachineIntegerType] = match format {
                KernelFloatType::Float32 => {
                    &[MachineIntegerType::Int32, MachineIntegerType::UInt32]
                }
                KernelFloatType::Float64 => &[MachineIntegerType::UInt64],
            };
            let patterns: &[u128] = match format {
                KernelFloatType::Float32 => &[
                    0, 0x80000000, 1, 0x007fffff, 0x3f800000, 0x7f800000, 0xff800000, 0x7fc00001,
                    0x7f800123, 0xffffffff,
                ],
                KernelFloatType::Float64 => &[
                    0,
                    0x8000000000000000,
                    1,
                    0x000fffffffffffff,
                    0x3ff0000000000000,
                    0x7ff0000000000000,
                    0xfff0000000000000,
                    0x7ff8000000000001,
                    0x7ff0000000000123,
                    0xffffffffffffffff,
                ],
            };
            let mut identities = std::collections::HashSet::new();
            for carrier in carriers {
                for bits in patterns {
                    let native = OldMachineTerm::Constant {
                        format: *carrier,
                        bits: *bits,
                    };
                    let value = format.value(native.clone());
                    let argument = PureFunctionArgument::Value(value.clone());
                    let root = KernelTermImport::default().argument(&argument);
                    assert!(identities.insert(root.id()));
                    assert_eq!(root.ty(), &KernelType::Program(format.program_type()));
                    assert!(matches!(root.node(), KernelTermNode::FloatLiteral { .. }));
                    assert!(!root.is_shared_machine_operand());
                    assert!(root.children().is_empty());
                    let view = FloatOperandView::from_shared(&root).unwrap();
                    assert_eq!(view.format(), format);
                    assert_eq!(view.literal(), Some((*carrier, *bits)));
                    assert_eq!(view.literal_bits(), Some(*bits as u64));
                    assert_eq!(view.constant_bits(), Some(*bits as u64));
                    assert!(root.0.argument_leaf.get().is_none());
                    assert_eq!(view.variable(), None);
                    assert_eq!(view.old_form(), Some(&native));
                    assert_eq!(KernelTermExport::float(&root).unwrap(), value);
                    assert_eq!(
                        KernelTermExport::default().argument(&root).unwrap(),
                        argument
                    );
                    assert_eq!(KernelTermImport::default().float(format, &native), root);
                }
            }
        }
        let native = OldMachineTerm::Variable(Variable(999801));
        let roots = [KernelFloatType::Float32, KernelFloatType::Float64].map(|format| {
            let root = KernelTermImport::default().float(format, &native);
            let view = FloatOperandView::from_shared(&root).unwrap();
            assert_eq!(view.variable(), Some(Variable(999801)));
            assert_eq!(view.literal(), None);
            assert_eq!(
                KernelTermExport::float(&root).unwrap(),
                format.value(native.clone())
            );
            root
        });
        assert_ne!(roots[0], roots[1]);
        assert_ne!(
            roots[0],
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999801))
        );
        assert!(FloatOperandView::from_shared(&KernelTerm::integer_literal(0.into())).is_none());
    }

    #[test]
    fn unmigrated_float_selections_keep_the_exact_native_payload() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let native = OldMachineTerm::If {
                condition: Box::new(OldConditionTerm::Constant(true)),
                then_term: Box::new(OldMachineTerm::Variable(Variable(999937))),
                else_term: Box::new(OldMachineTerm::Variable(Variable(999938))),
            };
            let root = KernelTermImport::default().float(format, &native);
            assert!(matches!(root.node(), KernelTermNode::ImportedScalar(_)));
            assert_eq!(
                KernelTermExport::float(&root).unwrap(),
                format.value(native)
            );
        }
    }

    #[test]
    fn float_arithmetic_uses_shared_operands_and_explicit_export() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let native = match format {
                KernelFloatType::Float32 => OldMachineTerm::Float32Binary {
                    operator: FloatBinaryOperator::Add,
                    left: Box::new(OldMachineTerm::Variable(Variable(999802))),
                    right: Box::new(OldMachineTerm::constant(0)),
                },
                KernelFloatType::Float64 => OldMachineTerm::Float64Binary {
                    operator: FloatBinaryOperator::Add,
                    left: Box::new(OldMachineTerm::Variable(Variable(999802))),
                    right: Box::new(OldMachineTerm::uint64_constant(0)),
                },
            };
            let root = KernelTermImport::default().float(format, &native);
            assert!(matches!(root.node(), KernelTermNode::FloatBinary { .. }));
            let view = FloatOperandView::from_shared(&root).unwrap();
            assert_eq!(view.literal(), None);
            assert_eq!(view.variable(), None);
            assert!(view.old_form().is_none());
            assert_eq!(
                KernelTermExport::float(&root).unwrap(),
                format.value(native)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/float.rs");
}

impl KernelTerm {
    /// Selected compatibility reading for native value keys and APIs. Ordinary
    /// execution handoffs retain the root without requesting this view.
    pub(crate) fn float_native_value(&self) -> Option<&ProgramValue> {
        let format = FloatOperandView::from_shared(self)?.format();
        if let Some(PureFunctionArgument::Value(value)) = self.written_argument() {
            return FloatOperandView::from_value(value).map(|_| value);
        }
        let PureFunctionArgument::Value(value) = self
            .0
            .argument_leaf
            .get_or_init(|| {
                // Build native leaves directly. The compound exporter reads
                // its child leaves through this same slot.
                let value = match self.node() {
                    KernelTermNode::FloatLiteral { carrier, bits } => {
                        format.value(OldMachineTerm::Constant {
                            format: *carrier,
                            bits: *bits,
                        })
                    }
                    KernelTermNode::ImportedScalar(input) => format.value(input.value().clone()),
                    KernelTermNode::Variable(variable) => {
                        format.value(OldMachineTerm::Variable(*variable))
                    }
                    KernelTermNode::FloatRead(read) => {
                        let (point, address) = read.parts();
                        format.value(crate::kernel::OldMachineTerm::read_named(
                            point.clone(),
                            address.export().expect("float read address"),
                            format.load_kind(),
                        ))
                    }
                    _ => KernelTermExport::float(self).expect("float value output"),
                };
                Box::new(PureFunctionArgument::Value(value))
            })
            .as_ref()
        else {
            unreachable!("float value descriptor");
        };
        Some(value)
    }
}
