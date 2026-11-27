//! Overflow conditions retain their written format and numeric operands.
use super::*;
fn literal_overflow(
    format: MachineIntegerType,
    operation: OverflowOperation,
    left: &KernelMachineLiteral,
    right: &KernelMachineLiteral,
) -> Option<bool> {
    use MachineIntegerType as Ty;
    use OverflowOperation as Op;
    if let Some(arithmetic) = crate::kernel::machine_integer::Operation::from_overflow(operation) {
        if format == Ty::Int32 && operation == Op::Subtract && right.word32() == Some(0) {
            return Some(false);
        }
        // Signed 64-bit arithmetic also accepts an unsigned literal's bits.
        let (a, b) = if format == Ty::Int64 {
            (left.signed64()?.into(), right.signed64()?.into())
        } else {
            (
                left.constant_at(format)?.to_integer(),
                right.constant_at(format)?.to_integer(),
            )
        };
        return Some(arithmetic.overflows(format, a, b));
    }
    match (format, operation) {
        (Ty::Int32, Op::Divide) => {
            Some((left.word32()?, right.word32()?) == (i32::MIN as u32, u32::MAX))
        }
        (Ty::Int64, Op::Divide) => Some(left.signed64()?.checked_div(right.signed64()?).is_none()),
        (Ty::Int32, Op::ShiftLeft) => {
            crate::kernel::primitives::term_operations::signed_shift_left_overflows_const(
                left.word32()?,
                right.word32()?,
            )
        }
        (Ty::Int64, Op::ShiftLeft) => Some(
            MachineBinaryOp::ShiftLeft
                .evaluate_int64(left.signed64()?, i64::from(right.shift_count()?))
                .is_none(),
        ),
        _ => None,
    }
}
impl KernelTerm {
    pub(crate) fn boolean_overflow_raw(
        format: MachineIntegerType,
        operation: OverflowOperation,
        arguments: [Self; 2],
    ) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::BoolOverflow {
                format,
                operation,
                arguments,
            },
        )
    }
    pub(crate) fn boolean_overflow(
        format: MachineIntegerType,
        operation: OverflowOperation,
        mut arguments: [Self; 2],
    ) -> Self {
        let literals = arguments.each_ref().map(Self::guard_literal);
        if let [Some(left), Some(right)] = &literals {
            if let Some(value) = literal_overflow(format, operation, left, right) {
                return Self::boolean_literal(value);
            }
            let operands = [left, right].map(|literal| literal.guard_operand(format));
            return Self::boolean_overflow_raw(format, operation, operands);
        }
        if format.format().bits() == 32 {
            for (argument, literal) in arguments.iter_mut().zip(literals) {
                if let Some(value) = literal {
                    *argument = value.guard_operand(format);
                }
            }
        }
        let views = arguments.each_ref().map(MachineOperandView::Shared);
        let no_overflow = match (format, operation) {
            (MachineIntegerType::Int32, OverflowOperation::Subtract) => {
                views[1].word32_constant() == Some(0)
            }
            (MachineIntegerType::Int64, OverflowOperation::Add) => {
                crate::kernel::primitives::int64_add_interval_fits(
                    views[0].int64_width_interval(),
                    views[1].int64_width_interval(),
                )
            }
            (MachineIntegerType::Int64, OverflowOperation::Subtract) => {
                crate::kernel::primitives::int64_subtract_interval_fits(
                    views[0].int64_width_interval(),
                    views[1].int64_width_interval(),
                )
            }
            _ => false,
        };
        if no_overflow {
            Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(false))
        } else {
            Self::boolean_overflow_raw(format, operation, arguments)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn operations() -> [OverflowOperation; 5] {
        use OverflowOperation::*;
        [Add, Subtract, Multiply, Divide, ShiftLeft]
    }
    fn values(format: MachineIntegerType) -> Vec<OldMachineTerm> {
        let mut values = vec![OldMachineTerm::Variable(Variable(999201))];
        for value in [0, 1, 31, 32, 63, 64] {
            values.push(OldMachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), value).unwrap(),
            ));
        }
        let (minimum, maximum) = format.format().bounds();
        for limit in [minimum, maximum] {
            values.push(OldMachineTerm::machine_constant(
                MachineIntegerConstant::from_integer(format.format(), &limit).unwrap(),
            ));
        }
        if let Some(value) = MachineIntegerConstant::from_signed(format.format(), -1) {
            values.push(OldMachineTerm::machine_constant(value));
        }
        if matches!(
            format,
            MachineIntegerType::Int32 | MachineIntegerType::Int64
        ) {
            values.extend([
                OldMachineTerm::uint32_constant(63),
                OldMachineTerm::uint64_constant(1 << 32),
            ]);
        }
        if format == MachineIntegerType::Int64 {
            values.push(OldMachineTerm::legacy_cast(
                MachineCastSpelling::Int64From32,
                Box::new(OldMachineTerm::Variable(Variable(999202))),
            ));
        }
        values
    }
    #[test]
    fn overflow_conditions_preserve_native_constructor_and_raw_shape() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in crate::kernel::machine_integer::FORMATS {
            for operation in operations() {
                let values = values(format);
                for a in &values {
                    for b in &values {
                        let native = OldConditionTerm::Overflows {
                            format,
                            op: operation,
                            left: Box::new(a.clone()),
                            right: Box::new(b.clone()),
                        };
                        let raw = KernelTermImport::default().condition(&native);
                        assert!(matches!(raw.node(), KernelTermNode::BoolOverflow { .. }));
                        assert_eq!(
                            format!("{:?}", KernelTermExport::condition(&raw).unwrap()),
                            format!("{native:?}")
                        );
                        let args = [
                            KernelTermImport::default().machine(format, a),
                            KernelTermImport::default().machine(format, b),
                        ];
                        let actual = KernelTerm::boolean_overflow(format, operation, args);
                        let expected = OldConditionTerm::machine_overflows(
                            format,
                            operation,
                            a.clone(),
                            b.clone(),
                        );
                        assert_eq!(
                            format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                            format!("{expected:?}"),
                            "{format:?} {operation:?} {a:?} {b:?}"
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn retained_literal_guards_match_imported_guards() {
        use MachineIntegerType as Ty;
        let _session = crate::kernel::VerificationSession::enter();
        for (format, a, b) in [
            (
                Ty::Int64,
                OldMachineTerm::uint64_constant(i64::MAX as u64),
                OldMachineTerm::int64_constant(1),
            ),
            (
                Ty::Int32,
                OldMachineTerm::uint64_constant(2),
                OldMachineTerm::uint32_constant(0),
            ),
            (
                Ty::UInt128,
                OldMachineTerm::int64_constant(-1),
                OldMachineTerm::uint64_constant(u64::MAX),
            ),
        ] {
            let retained = KernelTerm::intern(
                KernelType::Program(format.program_type()),
                KernelTermNode::WrittenMachine(KernelWrittenMachine::expression(format, &a)),
            );
            let args = [retained, KernelTermImport::default().machine(format, &b)];
            for op in operations() {
                let expected =
                    OldConditionTerm::machine_overflows(format, op, a.clone(), b.clone());
                assert_eq!(
                    KernelTerm::boolean_overflow(format, op, args.clone()),
                    KernelTermImport::default().condition(&expected),
                    "{format:?} {op:?}"
                );
            }
            let expected = OldConditionTerm::machine_compare(format, CompareRelation::Equal, a, b);
            assert_eq!(
                KernelTerm::boolean_comparison(format, CompareRelation::Equal, args),
                KernelTermImport::default().condition(&expected),
                "{format:?}"
            );
        }
    }

    #[test]
    fn overflow_conditions_preserve_distinct_substitution_policies() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in crate::kernel::machine_integer::FORMATS {
            for operation in operations() {
                let source = OldConditionTerm::Overflows {
                    format,
                    op: operation,
                    left: Box::new(OldMachineTerm::Variable(Variable(999201))),
                    right: Box::new(OldMachineTerm::machine_constant(
                        MachineIntegerConstant::from_signed(format.format(), 0).unwrap(),
                    )),
                };
                for source in [
                    source.clone(),
                    OldConditionTerm::BoolEqual(
                        Box::new(source),
                        Box::new(OldConditionTerm::Constant(false)),
                    ),
                ] {
                    let root = KernelTermImport::default().condition(&source);
                    let bits = OldMachineTerm::machine_constant(
                        MachineIntegerConstant::from_signed(format.format(), 1).unwrap(),
                    );
                    let expected =
                        crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                            &source,
                            Variable(999201),
                            &bits,
                        );
                    let actual = crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(&root,Variable(999201),&bits).unwrap();
                    assert_eq!(
                        format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                        format!("{expected:?}")
                    );
                    let target = Address::null();
                    let expected =
                        crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
                            &Proposition::condition_is(source.clone(), true),
                            Variable(999201),
                            &target,
                        );
                    let Proposition::ConditionIs(expected, true) = expected else {
                        panic!("condition");
                    };
                    let actual =
                        crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                            &root,
                            Variable(999201),
                            &target,
                        )
                        .unwrap();
                    assert_eq!(
                        format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                        format!("{expected:?}")
                    );
                }
            }
        }
    }
    #[test]
    fn overflow_conditions_keep_native_load_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::SymbolicMemory::new()
            .with_block("overflow-read", 8)
            .with_block("overflow-other", 4);
        let after = before.clone().store(
            crate::kernel::SymbolicMemory::global_pointer("overflow-other"),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let memories = [before, after].map(crate::kernel::intern_memory);
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            for op in operations() {
                let sources = memories
                    .each_ref()
                    .map(|memory| OldConditionTerm::Overflows {
                        format,
                        op,
                        left: Box::new(OldMachineTerm::read_named(
                            ProgramPoint::at(memory),
                            Box::new(crate::kernel::SymbolicMemory::global_pointer(
                                "overflow-read",
                            )),
                            if format == MachineIntegerType::Int32 {
                                LoadKind::Int32
                            } else {
                                LoadKind::Bits64
                            },
                        )),
                        right: Box::new(OldMachineTerm::Variable(Variable(999203))),
                    });
                let roots = sources
                    .each_ref()
                    .map(|source| KernelTermImport::default().condition(source));
                for allowed in [false, true] {
                    let loads = |_: &OldMachineTerm, _: &OldMachineTerm| allowed;
                    let expected = crate::kernel::assumptions::conditions_equal_with_load_atoms(
                        &sources[0],
                        &sources[1],
                        &loads,
                    );
                    assert_eq!(
                        crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                            BooleanOperandView::Shared(&roots[0]),
                            BooleanOperandView::Shared(&roots[1]),
                            &loads
                        ),
                        expected
                    );
                    assert_eq!(
                        crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                            BooleanOperandView::Shared(&roots[0]),
                            BooleanOperandView::Native(&sources[1]),
                            &loads
                        ),
                        expected
                    );
                }
            }
        }
    }
    #[test]
    fn overflow_conditions_pointer_rewrite_keeps_nested_literals_raw() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = OldConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left: Box::new(OldMachineTerm::IntegerAddress(
                Box::new(Address::symbolic(Variable(999210))),
                AddressObjectClass::NONE,
            )),
            right: Box::new(OldMachineTerm::uint64_constant(0)),
        };
        for source in [
            source.clone(),
            OldConditionTerm::BoolEqual(
                Box::new(source),
                Box::new(OldConditionTerm::Constant(false)),
            ),
        ] {
            let root = KernelTermImport::default().condition(&source);
            let expected = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
                &Proposition::condition_is(source.clone(), true),
                Variable(999210),
                &Address::null(),
            );
            let Proposition::ConditionIs(expected, true) = expected else {
                panic!("condition");
            };
            let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                &root,
                Variable(999210),
                &Address::null(),
            )
            .unwrap();
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                format!("{expected:?}")
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/overflow.rs");
}
