//! Float-producing numeric conversions. Construction and import/export are
//! structural; the native producer owns constant normalization and obligations.
use super::*;
use crate::kernel::primitives::float_conversion::numeric_float_conversion_types;

#[derive(Clone, Copy)]
pub(crate) enum FloatConversionOperand<'a> {
    Native(ProgramType, &'a MachineTerm),
    Shared(&'a KernelTerm),
}
impl<'a> FloatConversionOperand<'a> {
    pub(crate) fn shared(self) -> Option<&'a KernelTerm> {
        match self {
            Self::Shared(root) => Some(root),
            _ => None,
        }
    }

    pub(crate) fn source_type(self) -> ProgramType {
        match self {
            Self::Native(source, _) => source,
            Self::Shared(root) => match root.ty() {
                KernelType::Program(source) => *source,
                _ => unreachable!("numeric conversion operand"),
            },
        }
    }
    pub(crate) fn native(self) -> Option<&'a MachineTerm> {
        match self {
            Self::Native(_, value) => Some(value),
            _ => None,
        }
    }
}

impl<'a> FloatOperandView<'a> {
    pub(crate) fn conversion(self) -> Option<FloatConversionOperand<'a>> {
        match self {
            Self::Native(format, MachineTerm::PureFunctionApplication { name, arguments }) => {
                let [operand] = arguments.as_slice() else {
                    return None;
                };
                let (source, target) = numeric_float_conversion_types(name)?;
                (target == format.program_type())
                    .then_some(FloatConversionOperand::Native(source, operand))
            }
            Self::Shared(root) => match root.node() {
                KernelTermNode::FloatConvert { operand, .. } => {
                    Some(FloatConversionOperand::Shared(operand))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

impl KernelTerm {
    pub(crate) fn float_convert(
        target: KernelFloatType,
        source: ProgramType,
        operand: Self,
    ) -> Result<Self, &'static str> {
        Self::numeric_float_convert(target.program_type(), source, operand)
    }

    pub(crate) fn numeric_float_convert(
        target: ProgramType,
        source: ProgramType,
        operand: Self,
    ) -> Result<Self, &'static str> {
        let name = numeric_float_conversion_name(source, target);
        if numeric_float_conversion_types(&name) != Some((source, target))
            || operand.ty() != &KernelType::Program(source)
        {
            return Err("numeric float conversion types");
        }
        Ok(Self::intern(
            KernelType::Program(target),
            KernelTermNode::FloatConvert {
                source,
                destination: target,
                operand,
            },
        ))
    }
}

pub(super) fn float_conversion_name(source: ProgramType, target: KernelFloatType) -> String {
    numeric_float_conversion_name(source, target.program_type())
}

fn numeric_float_conversion_name(source: ProgramType, target: ProgramType) -> String {
    format!(
        "c_{}_to_{}",
        crate::kernel::program_type_spelling(source),
        crate::kernel::program_type_spelling(target)
    )
}

impl KernelTermImport {
    pub(crate) fn float_to_machine(
        &mut self,
        target: MachineIntegerType,
        term: &MachineTerm,
    ) -> Option<KernelTerm> {
        let MachineTerm::PureFunctionApplication { name, arguments } = term else {
            return None;
        };
        let [operand] = arguments.as_slice() else {
            return None;
        };
        let (source, destination) = numeric_float_conversion_types(name)?;
        MachineIntegerType::from_program_type(destination)?;
        let format = KernelFloatType::from_program_type(source)?;
        let operand = self.float(format, operand);
        Some(
            KernelTerm::numeric_float_convert(destination, source, operand)
                .ok()?
                .with_machine_observation_type(target),
        )
    }
}

impl KernelTermExport {
    pub(crate) fn float_to_machine(term: &KernelTerm) -> Result<MachineTerm, &'static str> {
        let KernelTermNode::FloatConvert {
            source,
            destination,
            operand,
        } = term.node()
        else {
            return Err("float conversion root");
        };
        Ok(MachineTerm::PureFunctionApplication {
            name: numeric_float_conversion_name(*source, *destination),
            arguments: vec![Self::float_machine(operand)?],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn float_to_machine_conversions_preserve_types_and_invalid_literal_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        for source in [KernelFloatType::Float32, KernelFloatType::Float64] {
            for target in [
                MachineIntegerType::Int8,
                MachineIntegerType::UInt8,
                MachineIntegerType::Int16,
                MachineIntegerType::UInt16,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                MachineIntegerType::UInt64,
            ] {
                let literals = match source {
                    KernelFloatType::Float32 => vec![
                        MachineTerm::Variable(Variable(999970)),
                        MachineTerm::constant(0x3fc00000),
                        MachineTerm::constant(0x80000000),
                        MachineTerm::constant(0x7f800000),
                        MachineTerm::constant(0x7fc00001),
                    ],
                    KernelFloatType::Float64 => vec![
                        MachineTerm::Variable(Variable(999970)),
                        MachineTerm::uint64_constant(0x3ff8000000000000),
                        MachineTerm::uint64_constant(0x8000000000000000),
                        MachineTerm::uint64_constant(0x7ff0000000000000),
                        MachineTerm::uint64_constant(0x7ff8000000000001),
                    ],
                };
                for operand in literals {
                    let native = MachineTerm::PureFunctionApplication {
                        name: numeric_float_conversion_name(
                            source.program_type(),
                            target.program_type(),
                        ),
                        arguments: vec![operand],
                    };
                    let root = KernelTermImport::default().machine(target, &native);
                    let KernelTermNode::FloatConvert {
                        source: actual,
                        operand,
                        ..
                    } = root.node()
                    else {
                        panic!("retained float-to-integer conversion");
                    };
                    assert_eq!(*actual, source.program_type());
                    assert_eq!(operand.ty(), &KernelType::Program(source.program_type()));
                    assert_eq!(root.ty(), &KernelType::Program(target.program_type()));
                    assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
                    let observed = root.with_machine_observation_type(MachineIntegerType::UInt64);
                    assert_eq!(KernelTermExport::machine(&observed).unwrap(), native);
                }
            }
        }
    }

    #[test]
    fn float_to_machine_import_preserves_unrecognized_signatures() {
        for (name, target) in [
            ("c_float64_to_int128", MachineIntegerType::Int128),
            ("c_int32_to_int64", MachineIntegerType::Int64),
        ] {
            let native = MachineTerm::PureFunctionApplication {
                name: name.into(),
                arguments: vec![MachineTerm::Variable(Variable(999971))],
            };
            let root = KernelTermImport::default().machine(target, &native);
            assert!(matches!(root.node(), KernelTermNode::Legacy(_)));
            assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
        }
    }

    #[test]
    fn float_conversions_retain_typed_operands_and_exact_native_structure() {
        let _session = crate::kernel::VerificationSession::enter();
        for source in [
            ProgramType::Int8,
            ProgramType::UInt8,
            ProgramType::Int16,
            ProgramType::UInt16,
            ProgramType::Int32,
            ProgramType::UInt32,
            ProgramType::Int64,
            ProgramType::UInt64,
            ProgramType::Float32,
            ProgramType::Float64,
        ] {
            for target in [KernelFloatType::Float32, KernelFloatType::Float64] {
                if source == target.program_type() {
                    continue;
                }
                let native = MachineTerm::PureFunctionApplication {
                    name: float_conversion_name(source, target),
                    arguments: vec![MachineTerm::Variable(Variable(999960))],
                };
                let root = KernelTermImport::default().float(target, &native);
                let count = KernelTermExport::machine_export_count();
                let view = FloatOperandView::from_shared(&root)
                    .unwrap()
                    .conversion()
                    .unwrap();
                assert_eq!(view.source_type(), source);
                assert_eq!(root.children().len(), 1);
                assert_eq!(root.children()[0].ty(), &KernelType::Program(source));
                assert_eq!(KernelTermExport::machine_export_count(), count);
                assert_eq!(
                    KernelTermExport::float(&root).unwrap(),
                    target.value(native)
                );
            }
        }
        // Structural import/export never calls the evaluating native constructor.
        for (source, target, literal) in [
            (
                ProgramType::Int32,
                KernelFloatType::Float32,
                MachineTerm::constant(1),
            ),
            (
                ProgramType::Float32,
                KernelFloatType::Float64,
                MachineTerm::constant(0x7f800123),
            ),
            (
                ProgramType::Float64,
                KernelFloatType::Float32,
                MachineTerm::uint64_constant(0x8000000000000000),
            ),
        ] {
            let native = MachineTerm::PureFunctionApplication {
                name: float_conversion_name(source, target),
                arguments: vec![literal],
            };
            let root = KernelTermImport::default().float(target, &native);
            assert!(matches!(root.node(), KernelTermNode::FloatConvert { .. }));
            assert_eq!(
                KernelTermExport::float(&root).unwrap(),
                target.value(native)
            );
        }
    }

    #[test]
    fn float_conversion_recognition_preserves_unknown_and_mismatched_calls() {
        for (name, arguments) in [
            ("ordinary_call", vec![MachineTerm::constant(1)]),
            ("c_int128_to_float32", vec![MachineTerm::constant(1)]),
            ("c_float32_to_float32", vec![MachineTerm::constant(1)]),
            ("c_int32_to_float64", vec![MachineTerm::constant(1)]),
            (
                "c_int32_to_float32",
                vec![MachineTerm::constant(1), MachineTerm::constant(2)],
            ),
        ] {
            let native = MachineTerm::PureFunctionApplication {
                name: name.into(),
                arguments,
            };
            let root = KernelTermImport::default().float(KernelFloatType::Float32, &native);
            assert!(matches!(root.node(), KernelTermNode::Legacy(_)));
            assert_eq!(
                KernelTermExport::float(&root).unwrap(),
                ProgramValue::Float32(native)
            );
        }
        let operand =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999961));
        assert!(
            KernelTerm::float_convert(
                KernelFloatType::Float32,
                ProgramType::UInt32,
                operand.clone()
            )
            .is_err()
        );
        assert!(
            KernelTerm::float_convert(KernelFloatType::Float32, ProgramType::Bool, operand)
                .is_err()
        );
    }
}
