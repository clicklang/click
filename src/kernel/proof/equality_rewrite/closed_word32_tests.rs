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
    ProofFacts::from_ordered(std::slice::from_ref(&equality))
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
            let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, _), true) = &result
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
