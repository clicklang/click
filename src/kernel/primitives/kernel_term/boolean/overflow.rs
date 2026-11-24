//! Overflow conditions retain their written format and numeric operands.
use super::*;
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
        let views = arguments.each_ref().map(MachineOperandView::Shared);
        if let [Some(a), Some(b)] = views.map(|view| view.literal()) {
            return KernelTermImport::default()
                .condition(&ConditionTerm::machine_overflows(format, operation, a, b));
        }
        if format.format().bits() == 32 {
            for argument in &mut arguments {
                if let Some(value) = MachineOperandView::Shared(argument).literal() {
                    *argument = KernelTermImport::default().machine(format, &value.into_word32());
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
    fn values(format: MachineIntegerType) -> Vec<MachineTerm> {
        let mut values = vec![MachineTerm::Variable(Variable(999201))];
        for value in [0, 1, 31, 32, 63, 64] {
            values.push(MachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), value).unwrap(),
            ));
        }
        if let Some(value) = MachineIntegerConstant::from_signed(format.format(), -1) {
            values.push(MachineTerm::machine_constant(value));
        }
        if format == MachineIntegerType::Int64 {
            values.push(MachineTerm::legacy_cast(
                MachineCastSpelling::Int64From32,
                Box::new(MachineTerm::Variable(Variable(999202))),
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
                        let native = ConditionTerm::Overflows {
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
                        let expected = ConditionTerm::machine_overflows(
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
    fn overflow_conditions_preserve_distinct_substitution_policies() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in crate::kernel::machine_integer::FORMATS {
            for operation in operations() {
                let source = ConditionTerm::Overflows {
                    format,
                    op: operation,
                    left: Box::new(MachineTerm::Variable(Variable(999201))),
                    right: Box::new(MachineTerm::machine_constant(
                        MachineIntegerConstant::from_signed(format.format(), 0).unwrap(),
                    )),
                };
                for source in [
                    source.clone(),
                    ConditionTerm::BoolEqual(
                        Box::new(source),
                        Box::new(ConditionTerm::Constant(false)),
                    ),
                ] {
                    let root = KernelTermImport::default().condition(&source);
                    let bits = MachineTerm::machine_constant(
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
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let memories = [before, after].map(crate::kernel::intern_memory);
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            for op in operations() {
                let sources = memories.each_ref().map(|memory| ConditionTerm::Overflows {
                    format,
                    op,
                    left: Box::new(MachineTerm::read_named(
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
                    right: Box::new(MachineTerm::Variable(Variable(999203))),
                });
                let roots = sources
                    .each_ref()
                    .map(|source| KernelTermImport::default().condition(source));
                for allowed in [false, true] {
                    let loads = |_: &MachineTerm, _: &MachineTerm| allowed;
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
        let source = ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left: Box::new(MachineTerm::IntegerAddress(
                Box::new(Address::symbolic(Variable(999210))),
                AddressObjectClass::NONE,
            )),
            right: Box::new(MachineTerm::uint64_constant(0)),
        };
        for source in [
            source.clone(),
            ConditionTerm::BoolEqual(Box::new(source), Box::new(ConditionTerm::Constant(false))),
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
