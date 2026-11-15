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
    pub(crate) fn source_type(self) -> ProgramType {
        match self {
            Self::Native(source, _) => source,
            Self::Shared(root) => match root.ty() {
                KernelType::Program(source) => *source,
                _ => unreachable!("numeric conversion operand"),
            },
        }
    }
    pub(super) fn native(self) -> Option<&'a MachineTerm> {
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
        let name = float_conversion_name(source, target);
        if numeric_float_conversion_types(&name) != Some((source, target.program_type()))
            || operand.ty() != &KernelType::Program(source)
        {
            return Err("numeric float conversion types");
        }
        Ok(Self::intern(
            KernelType::Program(target.program_type()),
            KernelTermNode::FloatConvert { source, operand },
        ))
    }
}

pub(super) fn float_conversion_name(source: ProgramType, target: KernelFloatType) -> String {
    format!(
        "c_{}_to_{}",
        crate::kernel::program_type_spelling(source),
        crate::kernel::program_type_spelling(target.program_type())
    )
}

#[cfg(test)]
mod tests {
    use super::*;

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
