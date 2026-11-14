//! Logical operators construct one value and retain mandatory domain debts.
//! No ambient facts participate in selecting the term or its domain.
use super::*;
use crate::kernel::MachineBinaryOp;

mod wide;

/// Whether a quotient or remainder owes C's nonzero divisor.
///
/// Specification `/` and `%` are total: a zero divisor leaves the kernel's
/// opaque quotient term, a fixed value that no rule relates to anything but
/// itself. Only `defined(...)`, which states C's definedness, still owes it.
/// Signed `MIN / -1` overflows the format, and like `+`, `-` and `*` it owes
/// its no-overflow domain either way.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum SpecDivision {
    Total,
    CDefined,
}

pub(in crate::kernel) fn apply_spec_machine_arithmetic(
    op: MachineBinaryOp,
    division: SpecDivision,
    left: &ProgramValue,
    right: &ProgramValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
) -> Option<CExpressionPath> {
    if matches!(
        left,
        ProgramValue::Pointer(_) | ProgramValue::PointerInteger(_)
    ) || matches!(
        right,
        ProgramValue::Pointer(_) | ProgramValue::PointerInteger(_)
    ) {
        return None;
    }
    if matches!(left, ProgramValue::Int128(_) | ProgramValue::UInt128(_))
        || matches!(right, ProgramValue::Int128(_) | ProgramValue::UInt128(_))
    {
        return wide::apply(op, division, left, right, facts, inherited);
    }
    if matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight) {
        return apply_spec_shift(op, left, right, facts, inherited);
    }
    let (left, right) = promote_c_bool_scalar_operands(left.clone(), right.clone());
    let (left, right, width) = apply_c_scalar_terms(left, right)?;
    let format = width.format();
    let mut obligations = inherited.to_vec();
    let mut domain = Vec::new();
    if matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::Remainder) {
        if division == SpecDivision::CDefined {
            let zero = crate::kernel::machine_integer::range::constant_word(format, &0.into())?;
            domain.push(Proposition::ConditionIs(
                ConditionTerm::machine_compare(
                    format,
                    crate::kernel::CompareRelation::Equal,
                    right.clone(),
                    zero,
                ),
                false,
            ));
        }
        if format.format().is_signed() {
            domain.push(Proposition::signed_division_exclusion(
                format, &left, &right,
            ));
        }
    } else if format.format().is_signed() {
        domain.push(Proposition::signed_arithmetic_domain(
            format, op, &left, &right,
        ));
    }
    if let Some(domain) = Proposition::arithmetic_domain(domain) {
        obligations.push(
            ProofObligation::evaluation_domain(domain)
                .with_context("arithmetic expression is defined"),
        );
    }
    let term = MachineTerm::logical_machine_binary(format, op, left, right);
    Some(CExpressionPath {
        outcome: CExpressionOutcome::Value(match width {
            ScalarWidth::Int32 => ProgramValue::Int32(term),
            ScalarWidth::UInt32 => ProgramValue::UInt32(term),
            ScalarWidth::Int64 => ProgramValue::Int64(term),
            ScalarWidth::UInt64 => ProgramValue::UInt64(term),
        }),
        facts: facts.clone(),
        obligations,
    })
}

/// Shifts promote their operands independently. In particular, a wide count
/// must be checked before narrowing it to the shifted word's representation.
fn apply_spec_shift(
    op: MachineBinaryOp,
    left: &ProgramValue,
    right: &ProgramValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
) -> Option<CExpressionPath> {
    apply_spec_shift_with_count_width(op, left, right, facts, inherited, None)
}

/// Rust keeps the original operand width, including narrow words. Left shifts
/// shift unsigned bits and reinterpret the result; right shifts retain the
/// signed operand for arithmetic sign extension. Only the count is partial.
pub(in crate::kernel) fn apply_spec_rust_shift(
    op: MachineBinaryOp,
    left: &ProgramValue,
    right: &ProgramValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
) -> Option<CExpressionPath> {
    use crate::kernel::machine_integer::conversion::convert_value;
    if matches!(right.numeric_value(), ProgramValue::Bool(_)) {
        return None;
    }
    let left = left.numeric_value();
    let (format, bits) = match left {
        ProgramValue::Int8(_) => (MachineIntegerType::Int8, 8),
        ProgramValue::UInt8(_) => (MachineIntegerType::UInt8, 8),
        ProgramValue::Int16(_) => (MachineIntegerType::Int16, 16),
        ProgramValue::UInt16(_) => (MachineIntegerType::UInt16, 16),
        ProgramValue::Int32(_) => (MachineIntegerType::Int32, 32),
        ProgramValue::UInt32(_) => (MachineIntegerType::UInt32, 32),
        ProgramValue::Int64(_) => (MachineIntegerType::Int64, 64),
        ProgramValue::UInt64(_) => (MachineIntegerType::UInt64, 64),
        _ => return None,
    };
    let operand = if op == MachineBinaryOp::ShiftLeft {
        convert_value(
            left.clone(),
            if bits == 64 {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::UInt32
            },
        )?
    } else {
        left.clone()
    };
    let mut path =
        apply_spec_shift_with_count_width(op, &operand, right, facts, inherited, Some(bits))?;
    let CExpressionOutcome::Value(value) = path.outcome else {
        return None;
    };
    path.outcome = CExpressionOutcome::Value(convert_value(value, format)?);
    Some(path)
}

fn apply_spec_shift_with_count_width(
    op: MachineBinaryOp,
    left: &ProgramValue,
    right: &ProgramValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
    count_width: Option<u32>,
) -> Option<CExpressionPath> {
    let width = scalar_width(left, left)?;
    let left = promote_c_path_value(left.clone(), width.format())?;
    let (right, unsigned_count, right_is_wide) = promote_c_shift_count(right.clone())?;
    let wide = matches!(width, ScalarWidth::Int64 | ScalarWidth::UInt64);
    let count = if wide && !right_is_wide {
        if unsigned_count {
            MachineTerm::uint64_from_32(right)
        } else {
            MachineTerm::int64_from_32(right)
        }
    } else {
        right
    };
    let count_format = match (wide || right_is_wide, unsigned_count) {
        (false, false) => MachineIntegerType::Int32,
        (false, true) => MachineIntegerType::UInt32,
        (true, false) => MachineIntegerType::Int64,
        (true, true) => MachineIntegerType::UInt64,
    };
    let constant = |format, value: u32| {
        crate::kernel::machine_integer::range::constant_word(format, &value.into())
            .expect("shift bounds fit their promoted format")
    };
    let mut obligations = inherited.to_vec();
    let mut domain = Vec::new();
    let mut require_false = |condition| {
        if PureFactContext::decide_intrinsically(&condition) != Some(false) {
            domain.push(Proposition::ConditionIs(condition, false));
        }
    };
    if !unsigned_count {
        require_false(ConditionTerm::machine_compare(
            count_format,
            crate::kernel::CompareRelation::LessThan,
            count.clone(),
            constant(count_format, 0),
        ));
    }
    require_false(ConditionTerm::machine_compare(
        count_format,
        crate::kernel::CompareRelation::GreaterEqual,
        count.clone(),
        constant(
            count_format,
            count_width.unwrap_or(if wide { 64 } else { 32 }),
        ),
    ));
    let count = if !wide && right_is_wide {
        MachineTerm::uint32_from_64(count)
    } else {
        count
    };
    if op == MachineBinaryOp::ShiftLeft && matches!(width, ScalarWidth::Int32 | ScalarWidth::Int64)
    {
        require_false(ConditionTerm::machine_compare(
            width.format(),
            crate::kernel::CompareRelation::LessThan,
            left.clone(),
            constant(width.format(), 0),
        ));
        domain.push(Proposition::ConditionIs(
            ConditionTerm::signed_shift_result_fits(width.format(), left.clone(), count.clone()),
            true,
        ));
    }
    if let Some(domain) = Proposition::arithmetic_domain(domain) {
        obligations.push(
            ProofObligation::evaluation_domain(domain).with_context("shift expression is defined"),
        );
    }
    let term = MachineTerm::logical_machine_binary(width.format(), op, left, count);
    Some(CExpressionPath {
        outcome: CExpressionOutcome::Value(match width {
            ScalarWidth::Int32 => ProgramValue::Int32(term),
            ScalarWidth::UInt32 => uint32(term),
            ScalarWidth::Int64 => ProgramValue::Int64(term),
            ScalarWidth::UInt64 => ProgramValue::UInt64(term),
        }),
        facts: facts.clone(),
        obligations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rust_shift_carrier_discharges_only_established_count_domains() {
        let left = ProgramValue::Int8(MachineTerm::Variable(Variable(991_500)));
        let count = MachineTerm::Variable(Variable(991_501));
        let right = uint32(count.clone());
        let bound = ConditionTerm::unsigned_less_than(count, MachineTerm::uint32_constant(8));
        let empty = PureFactContext::new();
        let defined = empty.clone().assume_condition(bound.clone(), true);
        let invalid = empty.clone().assume_condition(bound, false);
        let structural = apply_spec_rust_shift(
            MachineBinaryOp::ShiftLeft,
            &left,
            &right,
            &ExecutionFacts::default(),
            &[],
        )
        .unwrap();
        assert_eq!(structural.obligations.len(), 1);
        for (context, pending) in [(&empty, 1), (&defined, 0), (&invalid, 1)] {
            let paths = apply_rust_shift_left(
                left.clone(),
                right.clone(),
                ExecutionFacts::default(),
                vec![],
                context,
            );
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].outcome, structural.outcome);
            assert_eq!(paths[0].obligations.len(), pending);
            assert!(paths[0].obligations.iter().all(|debt| !debt.is_assumable()));
        }
        let pending = ProofObligation::new(structural.obligations[0].proposition().clone());
        let paths = apply_rust_shift_left(
            left,
            right,
            ExecutionFacts::default(),
            vec![pending.clone()],
            &empty,
        );
        assert_eq!(paths[0].outcome, structural.outcome);
        assert_eq!(
            paths[0].obligations.len(),
            2,
            "an inherited pending debt cannot prove the count"
        );
        assert_eq!(paths[0].obligations[0], pending);
    }

    #[test]
    fn logical_shifts_keep_values_for_invalid_counts_and_operands() {
        for (left, right, op) in [
            (int32(1), int32(32), MachineBinaryOp::ShiftRight),
            (int32(1), int32(u32::MAX), MachineBinaryOp::ShiftLeft),
            (int32(u32::MAX), int32(1), MachineBinaryOp::ShiftLeft),
            (int32(i32::MAX as u32), int32(1), MachineBinaryOp::ShiftLeft),
            (
                ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
                int32(64),
                MachineBinaryOp::ShiftLeft,
            ),
            // Narrowing the count first would silently turn this into zero.
            (
                int32(1),
                ProgramValue::UInt64(MachineTerm::uint64_constant(1 << 32)),
                MachineBinaryOp::ShiftRight,
            ),
        ] {
            let path = apply_spec_machine_arithmetic(
                op,
                SpecDivision::Total,
                &left,
                &right,
                &ExecutionFacts::default(),
                &[],
            )
            .unwrap();
            assert!(matches!(path.outcome, CExpressionOutcome::Value(_)));
            assert!(path.facts.is_empty());
            assert!(
                path.obligations.iter().any(
                    |obligation| !PureFactContext::new().proves_exact(obligation.proposition())
                )
            );
            assert!(
                path.obligations
                    .iter()
                    .all(|obligation| !obligation.is_assumable())
            );
        }
    }

    #[test]
    fn logical_shift_value_agrees_with_c_for_defined_mixed_width_operands() {
        let values = [
            ProgramValue::Int32(MachineTerm::constant(8)),
            ProgramValue::UInt32(MachineTerm::uint32_constant(8)),
            ProgramValue::Int64(MachineTerm::int64_constant(8)),
            ProgramValue::UInt64(MachineTerm::uint64_constant(8)),
        ];
        let counts = [
            ProgramValue::Int32(MachineTerm::constant(2)),
            ProgramValue::UInt32(MachineTerm::uint32_constant(2)),
            ProgramValue::Int64(MachineTerm::int64_constant(2)),
            ProgramValue::UInt64(MachineTerm::uint64_constant(2)),
        ];
        for left in &values {
            for right in &counts {
                for op in [MachineBinaryOp::ShiftLeft, MachineBinaryOp::ShiftRight] {
                    let logical = apply_spec_machine_arithmetic(
                        op,
                        SpecDivision::Total,
                        left,
                        right,
                        &ExecutionFacts::default(),
                        &[],
                    )
                    .unwrap();
                    let apply = if op == MachineBinaryOp::ShiftLeft {
                        apply_c_shift_left
                    } else {
                        apply_c_shift_right
                    };
                    let executed = apply(
                        left.clone(),
                        right.clone(),
                        ExecutionFacts::default(),
                        vec![],
                        &PureFactContext::new(),
                    );
                    assert_eq!(executed.len(), 1);
                    assert_eq!(logical.outcome, executed[0].outcome);
                    assert!(logical.obligations.is_empty());
                }
            }
        }
    }

    #[test]
    fn logical_arithmetic_retains_domains_for_every_machine_format() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
            ] {
                let wrap = |term| match format {
                    MachineIntegerType::Int32 => ProgramValue::Int32(term),
                    MachineIntegerType::UInt32 => ProgramValue::UInt32(term),
                    MachineIntegerType::Int64 => ProgramValue::Int64(term),
                    MachineIntegerType::UInt64 => ProgramValue::UInt64(term),
                    _ => unreachable!(),
                };
                let left = MachineTerm::Variable(Variable(991_000));
                let right = MachineTerm::Variable(Variable(991_001));
                for mode in [SpecDivision::Total, SpecDivision::CDefined] {
                    let path = apply_spec_machine_arithmetic(
                        op,
                        mode,
                        &wrap(left.clone()),
                        &wrap(right.clone()),
                        &ExecutionFacts::default(),
                        &[],
                    )
                    .unwrap();
                    assert_eq!(
                        path.outcome,
                        CExpressionOutcome::Value(wrap(MachineTerm::machine_binary(
                            format,
                            op,
                            left.clone(),
                            right.clone()
                        )))
                    );
                    assert!(path.facts.is_empty());
                    let signed = matches!(
                        format,
                        MachineIntegerType::Int32 | MachineIntegerType::Int64
                    );
                    let division =
                        matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::Remainder);
                    let shift =
                        matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight);
                    // Unsigned division is total; only C's definedness owes
                    // its nonzero divisor.
                    assert_eq!(
                        path.obligations.len(),
                        usize::from(
                            signed || shift || (division && mode == SpecDivision::CDefined)
                        )
                    );
                    assert!(path.obligations.iter().all(|debt| !debt.is_assumable()));
                }
            }
        }
    }

    #[test]
    fn symbolic_arithmetic_retains_cancellation_and_identity_nodes() {
        let x = MachineTerm::Variable(Variable(991_100));
        let one = MachineTerm::constant(1);
        let sum = MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            x.clone(),
            one.clone(),
        );
        for (op, left, right) in [
            (MachineBinaryOp::Subtract, sum, x.clone()),
            (MachineBinaryOp::Subtract, x.clone(), x.clone()),
            (MachineBinaryOp::Add, x.clone(), MachineTerm::constant(0)),
            (
                MachineBinaryOp::Multiply,
                x.clone(),
                MachineTerm::constant(0),
            ),
            (MachineBinaryOp::Divide, x, one),
        ] {
            let path = apply_spec_machine_arithmetic(
                op,
                SpecDivision::Total,
                &ProgramValue::Int32(left.clone()),
                &ProgramValue::Int32(right.clone()),
                &ExecutionFacts::default(),
                &[],
            )
            .unwrap();
            assert_eq!(
                path.outcome,
                CExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }))
            );
        }
    }

    #[test]
    fn statically_undefined_arithmetic_still_names_its_value_and_owes_false() {
        for (op, left, right) in [
            (MachineBinaryOp::Add, i32::MAX, 1),
            (MachineBinaryOp::Subtract, i32::MIN, 1),
            (MachineBinaryOp::Multiply, i32::MAX, 2),
            (MachineBinaryOp::Remainder, i32::MIN, -1),
            (MachineBinaryOp::Divide, i32::MIN, -1),
        ] {
            let path = apply_spec_machine_arithmetic(
                op,
                SpecDivision::Total,
                &int32(left as u32),
                &int32(right as u32),
                &ExecutionFacts::default(),
                &[],
            )
            .unwrap();
            assert!(matches!(path.outcome, CExpressionOutcome::Value(_)));
            assert!(
                path.obligations
                    .iter()
                    .any(|debt| !PureFactContext::new().proves_exact(debt.proposition()))
            );
        }
    }

    #[test]
    fn a_zero_divisor_is_owed_only_by_c_definedness_and_keeps_the_opaque_quotient() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let word = |value: i64| {
                crate::kernel::machine_integer::range::constant_word(format, &value.into()).unwrap()
            };
            let wrap = |term| match format {
                MachineIntegerType::Int32 => ProgramValue::Int32(term),
                MachineIntegerType::UInt32 => ProgramValue::UInt32(term),
                MachineIntegerType::Int64 => ProgramValue::Int64(term),
                MachineIntegerType::UInt64 => ProgramValue::UInt64(term),
                _ => unreachable!(),
            };
            for op in [MachineBinaryOp::Divide, MachineBinaryOp::Remainder] {
                let (left, right) = (word(7), word(0));
                let total = apply_spec_machine_arithmetic(
                    op,
                    SpecDivision::Total,
                    &wrap(left.clone()),
                    &wrap(right.clone()),
                    &ExecutionFacts::default(),
                    &[],
                )
                .unwrap();
                // No value is chosen: the quotient stays an operation node.
                assert_eq!(
                    total.outcome,
                    CExpressionOutcome::Value(wrap(MachineTerm::Binary {
                        format,
                        op,
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    }))
                );
                assert!(total.obligations.is_empty());
                let defined = apply_spec_machine_arithmetic(
                    op,
                    SpecDivision::CDefined,
                    &wrap(left),
                    &wrap(right),
                    &ExecutionFacts::default(),
                    &[],
                )
                .unwrap();
                assert_eq!(defined.outcome, total.outcome);
                assert!(
                    defined
                        .obligations
                        .iter()
                        .any(|debt| !PureFactContext::new().proves_exact(debt.proposition()))
                );
            }
        }
    }
}
