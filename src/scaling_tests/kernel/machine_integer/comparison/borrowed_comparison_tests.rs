use super::*;

#[test]
fn comparing_conversions_of_a_read_reuses_the_native_operand() {
    use crate::instrumentation::measure_deterministic_work;
    use crate::kernel::{
        Address, KernelIntegerOperator, KernelTerm, KernelTermImport, LoadKind, ProgramPoint,
        SymbolicMemory, intern_memory,
    };

    let format = MachineIntegerType::UInt32;
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let read = OldMachineTerm::read_named(
            ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
            Box::new(Address::symbolic(Variable(999742))),
            LoadKind::UInt32,
        );
        let observed = IntegerTerm::from_machine(format, read).unwrap();
        let mut input = KernelTermImport::default().integer(&observed.into());
        let one = KernelTerm::integer_literal(1.into());
        for _ in 0..size {
            input =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![input, one.clone()])
                    .unwrap();
        }
        let converted = KernelTerm::integer_to_machine(format, input).unwrap();
        assert!(!converted.is_shared_machine_operand());
        let compare = || {
            logical_condition_for_operand_views(
                format,
                R::Equal,
                [MachineOperandView::Shared(&converted); 2],
            )
        };
        let (cold_condition, cold_work) = measure_deterministic_work(compare);
        let (warm_condition, warm_work) = measure_deterministic_work(compare);
        assert_eq!(cold_condition, warm_condition);
        assert!(cold_work <= 16 * size + 32, "size={size}, work={cold_work}");
        assert!(warm_work <= 8, "size={size}, work={warm_work}");
    }
}

#[test]
fn conditional_atom_reads_fixed_roots_without_exporting_arithmetic() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};
    for format in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let literal = |n| {
                KernelTerm::retained_native_machine_operand(
                    format,
                    &if format == MachineIntegerType::UInt32 {
                        OldMachineTerm::uint32_constant(n as u32)
                    } else {
                        OldMachineTerm::uint64_constant(n)
                    },
                )
            };
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999740));
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [arithmetic, literal(1)],
                );
            }
            let guard_operands = [
                [literal(9), literal(8)],
                [variable.clone(), literal(8)],
                [literal(8), variable.clone()],
                [variable.clone(), variable.clone()],
                [arithmetic.clone(), literal(8)],
                [literal(8), arithmetic.clone()],
            ];
            let mut cases = guard_operands
                .into_iter()
                .enumerate()
                .flat_map(|(index, operands)| {
                    [R::LessThan, R::Equal]
                        .into_iter()
                        .map(move |relation| (index, operands.clone(), relation))
                })
                .map(|(index, operands, relation)| {
                    let guard_format =
                        if relation == R::Equal && format == MachineIntegerType::UInt64 {
                            MachineIntegerType::Int64
                        } else {
                            format
                        };
                    let guard =
                        KernelTerm::boolean_comparison_raw(guard_format, relation, operands);
                    let hit = KernelTerm::machine_if_shared(
                        format,
                        [guard.clone(), variable.clone(), literal(3)],
                    );
                    let miss = KernelTerm::machine_if_shared(
                        format,
                        [guard, arithmetic.clone(), literal(3)],
                    );
                    (hit, miss, index < 4)
                })
                .collect::<Vec<_>>();
            let flag = KernelTerm::variable(KernelType::Bool, Variable(999741));
            let conditional =
                |arm| KernelTerm::machine_if_shared(format, [flag.clone(), arm, literal(3)]);
            let inner = conditional(variable.clone());
            let shallow = conditional(inner.clone());
            let nested_arithmetic = conditional(conditional(arithmetic.clone()));
            let mut deep = inner.clone();
            for _ in 0..size {
                deep = conditional(deep);
            }
            let guarded = |operands| {
                KernelTerm::machine_if_shared(
                    format,
                    [
                        KernelTerm::boolean_comparison_raw(format, R::LessThan, operands),
                        variable.clone(),
                        literal(3),
                    ],
                )
            };
            cases.push((
                guarded([inner.clone(), literal(8)]),
                guarded([deep.clone(), literal(8)]),
                true,
            ));
            cases.push((
                guarded([literal(8), inner]),
                guarded([literal(8), deep.clone()]),
                true,
            ));
            cases.push((shallow, nested_arithmetic, true));
            cases.push((deep, conditional(arithmetic.clone()), false));
            let mut compound = flag.clone();
            for index in 0..size {
                compound = KernelTerm::boolean_if([
                    flag.clone(),
                    compound,
                    KernelTerm::variable(KernelType::Bool, Variable(999742 + index)),
                ]);
            }
            let other_flag = KernelTerm::variable(KernelType::Bool, Variable(999739));
            let equal_variables = KernelTerm::boolean_equal_raw([flag.clone(), other_flag.clone()]);
            let compound_equality = KernelTerm::boolean_equal_raw([compound.clone(), other_flag]);
            for (guard, expected) in [
                (flag, true),
                (equal_variables, true),
                (compound, false),
                (compound_equality, false),
            ] {
                let hit = KernelTerm::machine_if_shared(
                    format,
                    [guard.clone(), variable.clone(), literal(3)],
                );
                let miss =
                    KernelTerm::machine_if_shared(format, [guard, arithmetic.clone(), literal(3)]);
                cases.push((hit, miss, expected));
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (hit, miss, expected) in &cases {
                    assert_eq!(conditional_atom(hit).is_some(), *expected);
                    assert!(conditional_atom(miss).is_none());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{size} arithmetic nodes"
            );
        }
    }
}

#[test]
fn reflexive_variable_comparisons_do_not_walk_arithmetic_operands() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView as V,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999950));
            let one = KernelTerm::retained_native_machine_operand(
                format,
                &crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap(),
            );
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [arithmetic, one.clone()],
                );
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let retained = logical_condition_for_operand_views(
                    format,
                    R::Equal,
                    [V::Shared(&variable), V::Shared(&variable)],
                );
                assert!(
                    matches!(retained, OldConditionTerm::Compare { relation: R::Equal, left, right, .. }
                    if matches!((left.as_ref(), right.as_ref()), (OldMachineTerm::Variable(a), OldMachineTerm::Variable(b)) if a == b))
                );
                let other = logical_condition_for_operand_views(
                    format,
                    R::Equal,
                    [V::Shared(&arithmetic), V::Shared(&arithmetic)],
                );
                assert!(!matches!(other, OldConditionTerm::Compare { .. }));
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{format:?}, {size} arithmetic nodes"
            );
        }
    }
}

#[test]
fn bitwise_conditional_arms_read_only_fixed_roots() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as O};
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999970));
            let literal = |n: u64| {
                KernelTerm::retained_native_machine_operand(
                    format,
                    &crate::kernel::machine_integer::range::constant_word(format, &n.into())
                        .unwrap(),
                )
            };
            let guard = KernelTerm::variable(KernelType::Bool, Variable(999971));
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic =
                    KernelTerm::machine_binary_shared(format, O::Add, [arithmetic, literal(1)]);
            }
            let cases = [O::BitwiseAnd, O::BitwiseOr, O::BitwiseXor].map(|op| {
                let bitwise = |a, b| KernelTerm::machine_binary_shared(format, op, [a, b]);
                let conditional =
                    |a, b| KernelTerm::machine_if_shared(format, [guard.clone(), a, b]);
                (
                    conditional(bitwise(variable.clone(), literal(7)), literal(3)),
                    conditional(literal(3), bitwise(literal(7), variable.clone())),
                    conditional(bitwise(arithmetic.clone(), literal(7)), literal(3)),
                    conditional(literal(3), bitwise(literal(7), arithmetic.clone())),
                )
            });
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (left, right, left_miss, right_miss) in &cases {
                    assert!(
                        matches!(conditional_atom(left), Some(OldMachineTerm::If { then_term, .. })
                        if matches!(then_term.as_ref(), OldMachineTerm::Binary { .. }))
                    );
                    assert!(
                        matches!(conditional_atom(right), Some(OldMachineTerm::If { else_term, .. })
                        if matches!(else_term.as_ref(), OldMachineTerm::Binary { .. }))
                    );
                    assert!(conditional_atom(left_miss).is_none());
                    assert!(conditional_atom(right_miss).is_none());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{format:?}, {size} nested arithmetic nodes"
            );
        }
    }
}

#[test]
fn machine_comparison_and_guard_reads_are_bounded_on_hits_and_misses() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as O, MachineOperandView as V,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999980));
            let other =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999981));
            let literal = |n: u64| {
                KernelTerm::retained_native_machine_operand(
                    format,
                    &crate::kernel::machine_integer::range::constant_word(format, &n.into())
                        .unwrap(),
                )
            };
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic =
                    KernelTerm::machine_binary_shared(format, O::Add, [arithmetic, literal(1)]);
            }
            let binary_cases = [O::BitwiseAnd, O::BitwiseOr, O::BitwiseXor].map(|op| {
                (
                    KernelTerm::machine_binary_shared(format, op, [variable.clone(), literal(7)]),
                    KernelTerm::machine_binary_shared(format, op, [arithmetic.clone(), literal(7)]),
                    KernelTerm::machine_binary_shared(format, op, [literal(7), arithmetic.clone()]),
                )
            });
            let complement = |child| {
                KernelTerm::machine_unary_shared(
                    format,
                    crate::kernel::MachineUnaryOp::BitwiseNot,
                    child,
                )
            };
            let unary_case = (
                complement(variable.clone()),
                complement(arithmetic.clone()),
                complement(complement(variable.clone())),
            );
            let shifts = [O::ShiftRight, O::ShiftLeft];
            let shift_cases = shifts
                .into_iter()
                .filter(|op| *op == O::ShiftRight || !format.format().is_signed())
                .flat_map(|op| {
                    let shift =
                        |left, count| KernelTerm::machine_binary_shared(format, op, [left, count]);
                    let width = u64::from(format.format().bits());
                    let variable_shift = shift(variable.clone(), other.clone());
                    assert!(
                        bounded_comparison_operand(format, V::Shared(&variable_shift), false)
                            .is_none()
                    );
                    [
                        (
                            shift(variable.clone(), literal(1)),
                            shift(arithmetic.clone(), literal(1)),
                            shift(variable.clone(), arithmetic.clone()),
                        ),
                        (
                            variable_shift,
                            shift(arithmetic.clone(), other.clone()),
                            shift(variable.clone(), arithmetic.clone()),
                        ),
                        (
                            shift(variable.clone(), literal(width - 1)),
                            shift(variable.clone(), literal(width)),
                            shift(variable.clone(), literal(width + 1)),
                        ),
                    ]
                })
                .collect::<Vec<_>>();
            if format.format().is_signed() {
                for count in [literal(1), other.clone()] {
                    let signed_left_shift = KernelTerm::machine_binary_shared(
                        format,
                        O::ShiftLeft,
                        [variable.clone(), count],
                    );
                    assert!(
                        bounded_comparison_operand(format, V::Shared(&signed_left_shift), true)
                            .is_none()
                    );
                }
            }
            let wrapping_cases = [O::Add, O::Subtract, O::Multiply].map(|op| {
                let word_encoding = if format == MachineIntegerType::UInt32 {
                    MachineIntegerType::Int32
                } else {
                    format
                };
                let operation = |encoding, left, right| {
                    KernelTerm::machine_binary_shared(encoding, op, [left, right])
                };
                let variable_pair = operation(format, variable.clone(), other.clone());
                assert!(
                    bounded_comparison_operand(format, V::Shared(&variable_pair), false).is_none()
                );
                [
                    (
                        operation(word_encoding, variable.clone(), literal(7)),
                        operation(word_encoding, arithmetic.clone(), literal(7)),
                        operation(word_encoding, literal(7), arithmetic.clone()),
                    ),
                    (
                        variable_pair,
                        operation(format, arithmetic.clone(), other.clone()),
                        operation(format, variable.clone(), arithmetic.clone()),
                    ),
                ]
            });
            let signed = format.format().is_signed();
            if signed {
                for [literal, _] in &wrapping_cases {
                    assert!(
                        bounded_comparison_operand(format, V::Shared(&literal.0), true).is_none()
                    );
                }
            }
            let division_cases = [O::Divide, O::Remainder].map(|op| {
                let operation =
                    |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
                let zero = operation(variable.clone(), literal(0));
                assert!(bounded_comparison_operand(format, V::Shared(&zero), true).is_none());
                if format.format().is_signed() {
                    let minus_one =
                        crate::kernel::machine_integer::range::constant_word(format, &(-1).into())
                            .unwrap();
                    let minus_one = KernelTerm::retained_native_machine_operand(format, &minus_one);
                    let exceptional = operation(variable.clone(), minus_one);
                    assert!(
                        bounded_comparison_operand(format, V::Shared(&exceptional), true).is_none()
                    );
                }
                let hit = operation(variable.clone(), literal(3));
                assert!(bounded_comparison_operand(format, V::Shared(&hit), false).is_none());
                (
                    hit,
                    operation(arithmetic.clone(), literal(3)),
                    operation(variable.clone(), arithmetic.clone()),
                )
            });
            let variable_divisors = [O::Divide, O::Remainder].map(|op| {
                let operation =
                    |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
                let hit = operation(variable.clone(), other.clone());
                assert!(bounded_comparison_operand(format, V::Shared(&hit), false).is_none());
                (
                    hit,
                    operation(arithmetic.clone(), other.clone()),
                    operation(variable.clone(), arithmetic.clone()),
                )
            });
            let variable_divisor_hits = if format.format().is_signed() {
                for (signed, ..) in &variable_divisors {
                    assert!(bounded_comparison_operand(format, V::Shared(signed), true).is_none());
                }
                &variable_divisors[..0]
            } else {
                &variable_divisors[..]
            };
            use crate::kernel::MachineCastSpelling as C;
            let mut cast_cases = Vec::new();
            for (spelling, source, destination) in [
                C::Int64From32,
                C::Int64FromUInt32,
                C::UInt64FromInt32,
                C::UInt64From32,
                C::UInt32From64,
                C::UInt64FromInt64,
            ]
            .map(|spelling| {
                let (source, destination) = spelling.legacy_formats().unwrap();
                (spelling, source, destination)
            })
            .into_iter()
            .chain([
                (
                    C::Generic,
                    MachineIntegerType::Int32,
                    MachineIntegerType::UInt32,
                ),
                (
                    C::Generic,
                    MachineIntegerType::UInt32,
                    MachineIntegerType::Int32,
                ),
            ]) {
                if destination != format {
                    continue;
                }
                let child = variable.with_machine_observation_type(source);
                let cast = |operand| {
                    KernelTerm::machine_cast_shared(spelling, source, destination, operand)
                };
                cast_cases.push((
                    cast(child.clone()),
                    cast(arithmetic.with_machine_observation_type(source)),
                    cast(KernelTerm::machine_unary_shared(
                        source,
                        crate::kernel::MachineUnaryOp::BitwiseNot,
                        child,
                    )),
                ));
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (hit, left_miss, right_miss) in binary_cases
                    .iter()
                    .chain(std::iter::once(&unary_case))
                    .chain(&shift_cases)
                    .chain(wrapping_cases.iter().flat_map(|[literal, variables]| {
                        [(!signed).then_some(literal), Some(variables)]
                            .into_iter()
                            .flatten()
                    }))
                    .chain(&division_cases)
                    .chain(variable_divisor_hits)
                    .chain(&cast_cases)
                {
                    for operands in [
                        [V::Shared(hit), V::Shared(&other)],
                        [V::Shared(&other), V::Shared(hit)],
                    ] {
                        let condition =
                            logical_conditional_guard_for_operand_views(format, R::Equal, operands);
                        assert!(is_bounded_machine_comparison(&condition));
                        let guard =
                            crate::kernel::KernelTermImport::default().condition(&condition);
                        let conditional = KernelTerm::machine_if_shared(
                            format,
                            [guard, variable.clone(), literal(3)],
                        );
                        assert!(conditional_atom(&conditional).is_some());
                    }
                    for miss in [left_miss, right_miss] {
                        let condition = logical_conditional_guard_for_operand_views(
                            format,
                            R::Equal,
                            [V::Shared(miss), V::Shared(&other)],
                        );
                        assert!(!is_bounded_machine_comparison(&condition));
                    }
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{format:?}, {size} nested arithmetic nodes"
            );
        }
    }
}

#[test]
fn builtin_machine_order_rejects_a_shared_sum_at_its_root() {
    use crate::kernel::{KernelTermExport, MachineBinaryOp, StoredConditionTerm};
    let format = MachineIntegerType::Int32;
    let mut samples = Vec::new();
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut sum = KernelTerm::int32_literal(0);
        for _ in 0..depth {
            sum =
                KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [sum.clone(), sum]);
        }
        let root = KernelTerm::boolean_comparison_raw(format, R::LessEqual, [sum.clone(), sum]);
        let proposition =
            Proposition::condition_is(StoredConditionTerm::from_root(root.clone()).unwrap(), true);
        let exports = KernelTermExport::machine_export_count();
        let (decided, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::path_facts::solve_builtin_prop(&proposition)
        });
        assert!(!decided);
        assert!(!root.has_cached_native_argument());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|work| work[0] == work[1]),
        "{samples:?}"
    );
}
