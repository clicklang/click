use super::*;

mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/equality_rewrite/closed_word32_tests.rs");
}

fn rewrite_observation(
    format: MachineIntegerType,
    expression: MachineTerm,
    variable: &MachineTerm,
    replacement: MachineTerm,
    shared: bool,
) -> Proposition {
    let machine = if shared {
        let root = KernelTermImport::default()
            .machine_arithmetic(format, &expression)
            .unwrap();
        SharedMachineIntegerTerm::from_shared(format, root).unwrap()
    } else {
        SharedMachineIntegerTerm::intern(format, expression)
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(
            IntegerTerm::Machine(machine).into(),
            IntegerTerm::constant_i64(5).into(),
        ),
        true,
    );
    let equality = Proposition::ConditionIs(
        ConditionTerm::machine_compare(
            format,
            CompareRelation::Equal,
            variable.clone(),
            replacement,
        ),
        true,
    );
    PureFactStore::from_ordered(std::slice::from_ref(&equality))
        .check_equality_rewrite(&goal, &equality)
        .unwrap()
        .proposition()
        .clone()
}

#[test]
fn newly_closed_word32_arithmetic_has_the_same_value_for_native_and_shared_sources() {
    let _session = VerificationSession::enter();
    use MachineIntegerType as T;
    for (format, value, operand, expected) in [
        (T::Int32, 9i64, 3i64, [3i64, 0, 1]),
        (T::Int32, -10, 3, [-3, -1, -2]),
        (
            T::UInt32,
            i64::from(u32::MAX),
            3,
            [1_431_655_765, 0, 536_870_911],
        ),
        (
            T::UInt32,
            i64::from(u32::MAX),
            1,
            [i64::from(u32::MAX), 0, i64::from(i32::MAX)],
        ),
    ] {
        let variable = MachineTerm::Variable(Variable(992590));
        let word = |n: i64| {
            crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
        };
        for (operator, expected) in [
            MachineBinaryOp::Divide,
            MachineBinaryOp::Remainder,
            MachineBinaryOp::ShiftRight,
        ]
        .into_iter()
        .zip(expected)
        {
            for shared in [false, true] {
                let expression = MachineTerm::Binary {
                    format,
                    op: operator,
                    left: Box::new(variable.clone()),
                    right: Box::new(word(operand)),
                };
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(
                    rewrite_observation(format, expression, &variable, word(value), shared),
                    Proposition::ConditionIs(
                        ConditionTerm::IntegerLessEqual(
                            IntegerTerm::constant_i64(expected).into(),
                            IntegerTerm::constant_i64(5).into()
                        ),
                        true
                    ),
                    "{format:?} {operator:?}, shared={shared}, value={value}",
                );
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }
}

#[test]
fn newly_closed_word32_arithmetic_keeps_undefined_values_opaque() {
    let _session = VerificationSession::enter();
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    for (format, operator, value, operand) in [
        (T::Int32, O::Divide, 9i64, 0i64),
        (T::UInt32, O::Remainder, 9, 0),
        (T::Int32, O::Divide, i64::from(i32::MIN), -1),
        (T::Int32, O::Remainder, i64::from(i32::MIN), -1),
        (T::Int32, O::ShiftRight, 9, -1),
        (T::Int32, O::ShiftRight, 9, 32),
        (T::UInt32, O::ShiftRight, 9, 32),
    ] {
        let variable = MachineTerm::Variable(Variable(992591));
        let word = |n: i64| {
            crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
        };
        for shared in [false, true] {
            let expression = MachineTerm::Binary {
                format,
                op: operator,
                left: Box::new(variable.clone()),
                right: Box::new(word(operand)),
            };
            let result = rewrite_observation(format, expression, &variable, word(value), shared);
            let Some((ConditionTerm::IntegerLessEqual(left, _), true)) =
                (&result).condition_native()
            else {
                panic!("{result:?}");
            };
            assert!(
                matches!(left.as_ref(), IntegerTerm::Machine(_)),
                "{format:?} {operator:?}, shared={shared}: {result:?}"
            );
        }
    }
}

#[test]
fn selected_literal_comparison_operands_keep_their_native_encoding() {
    use crate::kernel::proof::term_rewrite::TermRewrite;
    use MachineIntegerType as T;
    for format in [T::Int32, T::UInt32, T::Int64, T::UInt64] {
        for relation in [
            CompareRelation::Equal,
            CompareRelation::LessThan,
            CompareRelation::LessEqual,
            CompareRelation::GreaterThan,
            CompareRelation::GreaterEqual,
        ] {
            for bits in [0, 3, u32::MAX] {
                let _session = VerificationSession::enter();
                let value = if format == T::Int32 {
                    i64::from(bits as i32)
                } else {
                    i64::from(bits)
                };
                let literal =
                    crate::kernel::machine_integer::range::constant_word(format, &value.into())
                        .unwrap();
                let flag = ConditionTerm::Variable(Variable(992597));
                let choice = MachineTerm::If {
                    condition: Box::new(flag.clone()),
                    then_term: Box::new(MachineTerm::Variable(Variable(992598))),
                    else_term: Box::new(literal.clone()),
                };
                for reverse in [false, true] {
                    let [left, right] = if reverse {
                        [literal.clone(), choice.clone()]
                    } else {
                        [choice.clone(), literal.clone()]
                    };
                    let input = ConditionTerm::Compare {
                        format,
                        relation,
                        left: Box::new(left),
                        right: Box::new(right),
                    };
                    let result =
                        TermRewrite::for_condition_exact(&flag, &ConditionTerm::Constant(false))
                            .condition(&input);
                    let expected = if format.format().bits() == 32 {
                        literal.clone().into_word32()
                    } else {
                        literal.clone()
                    };
                    assert_eq!(
                        result,
                        ConditionTerm::Compare {
                            format,
                            relation,
                            left: Box::new(expected.clone()),
                            right: Box::new(expected)
                        },
                        "{format:?}, {relation:?}, bits={bits}, reverse={reverse}"
                    );
                }
            }
        }
    }
}

fn selected_word32_literal_goal(format: MachineIntegerType, literal: u32) -> Proposition {
    let variable = MachineTerm::Variable(Variable(992599));
    let word = |n: u32| {
        crate::kernel::machine_integer::range::constant_word(format, &i64::from(n).into()).unwrap()
    };
    Proposition::ConditionIs(
        ConditionTerm::Compare {
            format,
            relation: CompareRelation::LessEqual,
            left: Box::new(MachineTerm::If {
                condition: Box::new(ConditionTerm::machine_compare(
                    format,
                    CompareRelation::Equal,
                    variable.clone(),
                    word(10),
                )),
                then_term: Box::new(variable),
                else_term: Box::new(word(literal)),
            }),
            right: Box::new(MachineTerm::constant(100)),
        },
        true,
    )
}

fn selected_word32_literal_equality(format: MachineIntegerType) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::machine_compare(
            format,
            CompareRelation::Equal,
            MachineTerm::Variable(Variable(992599)),
            MachineTerm::constant(9),
        ),
        true,
    )
}
