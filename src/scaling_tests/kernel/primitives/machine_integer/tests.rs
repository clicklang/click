// Scaling tests of `src/kernel/primitives/machine_integer.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_cast_construction_and_validation_do_constant_work_on_large_operands() {
    use crate::kernel::Variable;
    for size in [16, 64, 256, 1024] {
        let mut operand = Bitvector32Term::Variable(Variable(149_002));
        for _ in 0..size {
            operand = Bitvector32Term::Int64Add(
                Box::new(operand),
                Box::new(Bitvector32Term::Int64Constant(1)),
            );
        }
        let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineIntegerType::Int128.convert_modulo_value(CValue::Int64(operand))
        });
        let CValue::Int128(term) = converted.unwrap() else {
            unreachable!()
        };
        assert_eq!(work, 3, "size {size}");
        let (accepted, validation_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerType::Int128.accepts_wide_term(&term)
            });
        assert!(accepted);
        assert_eq!(validation_work, 2);
    }
}

#[test]
fn symbolic_modulo_conversion_work_is_independent_of_operand_depth() {
    for right_nested in [false, true] {
        for size in [16, 64, 256, 1024] {
            let mut term = Bitvector32Term::Variable(super::super::super::Variable(138_002));
            for _ in 0..size {
                let one = Bitvector32Term::UInt64Constant(1);
                term = if right_nested {
                    Bitvector32Term::UInt64Add(Box::new(one), Box::new(term))
                } else {
                    Bitvector32Term::UInt64Add(Box::new(term), Box::new(one))
                };
            }
            let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerType::Int16.convert_modulo_value(CValue::UInt64(term))
            });
            assert_eq!(
                converted.unwrap().c_type(),
                super::super::super::CType::Int16
            );
            assert_eq!(work, 1, "size {size}, right nested {right_nested}");
        }
    }
}

#[test]
fn truncating_machine_division_work_scales_with_explicit_operations() {
    for format in formats() {
        let left = MachineIntegerConstant::from_bits(format, format.mask()).unwrap();
        let right = MachineIntegerConstant::from_unsigned(format, 3).unwrap();
        for size in [2usize, 8, 32, 128] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    left.truncating_div_rem(right).unwrap();
                }
            });
            assert!(work <= 4 * size, "{format:?}, {size}: {work}");
        }
    }
}

#[test]
fn machine_integer_constant_work_is_linear_and_oversized_integer_rejection_is_constant() {
    let format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, true);
    let source =
        MachineIntegerConstant::from_signed(MachineIntegerType::Int64.format(), -1).unwrap();
    let mut previous = None;
    for size in [4, 16, 64, 256, 1024] {
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let widened = source.checked_convert(format).unwrap();
                assert_eq!(widened.checked_convert(source.format()), Some(source));
                assert_eq!(widened.convert_modulo(source.format()), source);
            }
        });
        if let Some(previous) = previous {
            assert_eq!(work, previous * 4);
        }
        assert!(work > 0);
        previous = Some(work);
    }
    let mut previous = None;
    for bits in [256usize, 1024, 4096, 16384, 65536] {
        let value = BigInt::from(1) << bits;
        let (rejected, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineIntegerConstant::from_integer(format, &value).is_none()
        });
        assert!(rejected);
        assert!(work > 0);
        if let Some(previous) = previous {
            assert_eq!(work, previous);
        }
        previous = Some(work);
    }
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let spelling = format!("{}1", "0".repeat(size));
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineIntegerConstant::parse_decimal(format, &spelling)
        });
        assert_eq!(value.unwrap().to_i128(), Some(1));
        assert_eq!(work, size + 3);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}
