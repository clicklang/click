// Scaling tests of `src/kernel/primitives/machine_integer.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::{MachineBinaryOp, MachineIntegerType};

#[test]
fn wide_cast_construction_and_validation_do_constant_work_on_large_operands() {
    use crate::kernel::Variable;
    for size in [16, 64, 256, 1024] {
        let mut operand = MachineTerm::Variable(Variable(149_002));
        for _ in 0..size {
            operand = MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left: Box::new(operand),
                right: Box::new(MachineTerm::int64_constant(1)),
            };
        }
        let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::machine_integer::conversion::convert_value(
                ProgramValue::Int64(operand),
                MachineIntegerType::Int128,
            )
        });
        let ProgramValue::Int128(term) = converted.unwrap() else {
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
            let mut term = MachineTerm::Variable(super::super::super::Variable(138_002));
            for _ in 0..size {
                let one = MachineTerm::uint64_constant(1);
                term = if right_nested {
                    MachineTerm::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Add,
                        left: Box::new(one),
                        right: Box::new(term),
                    }
                } else {
                    MachineTerm::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Add,
                        left: Box::new(term),
                        right: Box::new(one),
                    }
                };
            }
            let (converted, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::machine_integer::conversion::convert_value(
                    ProgramValue::UInt64(term),
                    MachineIntegerType::Int16,
                )
            });
            assert_eq!(
                converted.unwrap().program_type(),
                super::super::super::ProgramType::Int16
            );
            // One unit for the conversion and one for the cast node it
            // builds (the conversion table's `Cast`), whatever the depth.
            assert_eq!(work, 2, "size {size}, right nested {right_nested}");
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

/// Building σ, the 32-bit sign cast, building σ of it back, and reading an
/// index's word through it (`into_index_word32`, decision G1) inspect only
/// the operand's root: the work is the same for operands of 16 to 1,024
/// nodes. σ is a node of its own: σ of σ(x) is kept as written (R0 relates
/// it to `x` in the e-graph), its observation reads as `x`'s through both σ
/// (rule W) in the same work at every size, and a 32-bit operator over σ(x)
/// keeps σ(x) as its operand ("Every format its own nodes", step 4b).
#[test]
fn sign_cast_construction_and_word_reads_do_constant_work_on_deep_operands() {
    use crate::kernel::Variable;
    let mut observe_works = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut operand = MachineTerm::Variable(Variable(149_003));
        for _ in 0..size {
            operand = binary_node!(
                Int32,
                Add,
                Box::new(operand),
                Box::new(MachineTerm::Variable(Variable(149_004))),
            );
        }
        let (cast, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineTerm::sign_cast32(
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                operand.clone(),
            )
        });
        assert_eq!(work, 1, "size {size}");
        let ((), read_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                cast.sign_cast32_operand(),
                Some((MachineIntegerType::Int32, &operand))
            );
        });
        assert_eq!(read_work, 0, "size {size}");
        let (index, index_work) =
            crate::instrumentation::measure_deterministic_work(|| cast.clone().into_index_word32());
        assert_eq!(index, operand, "size {size}");
        assert_eq!(index_work, 0, "size {size}");
        let (back, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineTerm::sign_cast32(
                MachineIntegerType::UInt32,
                MachineIntegerType::Int32,
                cast.clone(),
            )
        });
        assert_eq!(work, 1, "size {size}");
        let ((), back_read_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                back.sign_cast32_operand(),
                Some((MachineIntegerType::UInt32, &cast)),
                "σ(σ(x)) is kept as written, size {size}"
            );
            assert_eq!(back.sign_cast32_bits(), &cast, "size {size}");
        });
        assert_eq!(back_read_work, 0, "size {size}");
        // Rule W reads the observation of σ(σ(x)) through both σ nodes, as
        // `x`'s. Building the observation imports the boxed operand, the
        // cost of any first observation of it; reading it walks only the σ
        // roots, the same work at every size.
        let read =
            crate::kernel::IntegerTerm::from_machine(MachineIntegerType::Int32, operand.clone())
                .map(|observed| observed.value_read().clone());
        let observed =
            crate::kernel::IntegerTerm::from_machine(MachineIntegerType::Int32, back.clone())
                .expect("σ(σ(x)) is observable");
        let (reading, observe_work) =
            crate::instrumentation::measure_deterministic_work(|| observed.value_read().clone());
        assert_eq!(Some(reading), read, "σ(σ(x)) reads as x, size {size}");
        observe_works.push(observe_work);
        let sum = MachineTerm::add_at(
            MachineIntegerType::UInt32,
            cast.clone(),
            MachineTerm::uint32_constant(1),
        );
        assert!(
            matches!(&sum, MachineTerm::Binary { left, .. } if **left == cast),
            "size {size}"
        );
    }
    assert!(
        observe_works.windows(2).all(|pair| pair[0] == pair[1]),
        "{observe_works:?}"
    );
}

/// The widening of a narrow value into 32 bits (rule K8, a relation) is a
/// node of its own: building it, and reading its operand through
/// `narrow_widening32_operand`, inspect only the operand's root, so the work
/// is the same for operands of 16 to 1,024 nodes. Its word is not peeled to
/// the operand, so a 32-bit operator over the widening keeps the widening.
#[test]
fn narrow_widening_construction_and_word_reads_do_constant_work_on_deep_operands() {
    use crate::kernel::Variable;
    for size in [16, 64, 256, 1024] {
        let mut sum = MachineTerm::Variable(Variable(149_005));
        for _ in 0..size {
            sum = binary_node!(
                Int32,
                Add,
                Box::new(sum),
                Box::new(MachineTerm::Variable(Variable(149_006))),
            );
        }
        // A narrow value over a deep word: the C narrowing of the sum.
        let operand = MachineTerm::machine_integer_cast(
            MachineIntegerType::Int32,
            MachineIntegerType::UInt8,
            sum,
        );
        for destination in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let (cast, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::machine_integer::conversion::convert_term(
                    MachineIntegerType::UInt8,
                    destination,
                    operand.clone(),
                )
            });
            assert_eq!(work, 1, "size {size}");
            let ((), read_work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    cast.narrow_widening32_operand(),
                    Some((MachineIntegerType::UInt8, &operand))
                );
                assert_eq!(cast.sign_cast32_operand(), None);
            });
            assert_eq!(read_work, 0, "size {size}");
            assert_ne!(
                MachineTerm::add(cast.clone(), MachineTerm::constant(1)),
                MachineTerm::add(operand.clone(), MachineTerm::constant(1)),
                "size {size}"
            );
        }
    }
}
