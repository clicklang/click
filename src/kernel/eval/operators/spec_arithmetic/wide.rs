//! The supported 128-bit logical operators retain their mathematical source
//! and domain. Operand equalities cannot replace that source during lowering.
use super::*;
use crate::kernel::machine_integer::wide_spec;

fn operand_type(value: &ProgramValue) -> Option<MachineIntegerType> {
    match value.program_type() {
        ProgramType::Bool => Some(MachineIntegerType::UInt8),
        ty => MachineIntegerType::from_program_type(ty),
    }
}

fn observe(value: &ProgramValue, ty: MachineIntegerType) -> Option<IntegerTerm> {
    IntegerTerm::from_machine(
        ty,
        crate::kernel::spec::program_value_bitvector_term(value)?,
    )
}

pub(super) fn apply(
    op: MachineBinaryOp,
    division: SpecDivision,
    left: &ProgramValue,
    right: &ProgramValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
) -> Option<ExpressionPath> {
    let a = operand_type(left)?;
    let b = operand_type(right)?;
    let destination = wide_spec::result_type(op, a, b)?;
    let left = observe(left, a)?;
    let right = observe(right, b)?;
    let (result, obligation) = wide_spec::result_and_domain(op, division, destination, left, right);
    let mut obligations = inherited.to_vec();
    obligations.extend(obligation);
    let term = result
        .as_const()
        .and_then(|constant| {
            crate::kernel::machine_integer::range::constant_word(destination, constant)
        })
        .unwrap_or_else(|| MachineTerm::IntegerToMachine {
            value: result.into(),
            destination,
        });
    Some(ExpressionPath {
        outcome: ExpressionOutcome::Value(match destination {
            MachineIntegerType::Int128 => ProgramValue::Int128(term),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(term),
            _ => unreachable!(),
        }),
        facts: facts.clone(),
        obligations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn value(format: MachineIntegerType, constant: i128) -> ProgramValue {
        let term =
            crate::kernel::machine_integer::range::constant_word(format, &constant.into()).unwrap();
        match format {
            MachineIntegerType::Int128 => ProgramValue::Int128(term),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(term),
            _ => unreachable!(),
        }
    }

    #[test]
    fn undefined_wide_arithmetic_keeps_a_value_and_an_unproved_domain() {
        for (op, left, right) in [
            (MachineBinaryOp::Multiply, i128::MAX, 2),
            (MachineBinaryOp::Divide, i128::MIN, -1),
            (MachineBinaryOp::Remainder, i128::MIN, -1),
        ] {
            let path = apply(
                op,
                SpecDivision::Total,
                &value(MachineIntegerType::Int128, left),
                &value(MachineIntegerType::Int128, right),
                &ExecutionFacts::default(),
                &[],
            )
            .unwrap();
            assert!(matches!(
                path.outcome,
                ExpressionOutcome::Value(ProgramValue::Int128(_))
            ));
            assert!(path.facts.is_empty());
            assert!(
                path.obligations
                    .iter()
                    .all(|obligation| !obligation.is_assumable())
            );
            assert!(
                path.obligations.iter().any(
                    |obligation| !PureFactContext::new().proves_exact(obligation.proposition())
                )
            );
        }
    }

    #[test]
    fn a_wide_zero_divisor_is_owed_only_by_program_definedness() {
        for format in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
            for op in [MachineBinaryOp::Divide, MachineBinaryOp::Remainder] {
                let (left, right) = (value(format, 1), value(format, 0));
                let total = apply(
                    op,
                    SpecDivision::Total,
                    &left,
                    &right,
                    &ExecutionFacts::default(),
                    &[],
                )
                .unwrap();
                // The value is the opaque quotient, never a chosen constant.
                let ExpressionOutcome::Value(
                    ProgramValue::Int128(term) | ProgramValue::UInt128(term),
                ) = &total.outcome
                else {
                    panic!("a wide quotient has a wide value");
                };
                assert!(matches!(term, MachineTerm::IntegerToMachine { .. }));
                assert!(total.obligations.is_empty());
                let defined = apply(
                    op,
                    SpecDivision::CDefined,
                    &left,
                    &right,
                    &ExecutionFacts::default(),
                    &[],
                )
                .unwrap();
                assert_eq!(defined.outcome, total.outcome);
                assert!(defined.obligations.iter().any(|obligation| {
                    !PureFactContext::new().proves_exact(obligation.proposition())
                }));
            }
        }
    }

    #[test]
    fn defined_wide_arithmetic_agrees_with_execution() {
        for format in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
            for op in [
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
            ] {
                if format == MachineIntegerType::UInt128 && op == MachineBinaryOp::Multiply {
                    continue; // Not an implemented native operation.
                }
                let left = value(format, (1i128 << 80) + 7);
                let right = value(format, 3);
                let logical = apply(
                    op,
                    SpecDivision::CDefined,
                    &left,
                    &right,
                    &ExecutionFacts::default(),
                    &[],
                )
                .unwrap();
                let execute = match op {
                    MachineBinaryOp::Multiply => apply_program_multiply,
                    MachineBinaryOp::Divide => apply_program_divide,
                    MachineBinaryOp::Remainder => apply_program_remainder,
                    _ => unreachable!(),
                };
                let execution = execute(
                    left,
                    right,
                    ExecutionFacts::default(),
                    vec![],
                    &PureFactContext::new(),
                );
                assert_eq!(execution.len(), 1);
                assert_eq!(logical.outcome, execution[0].outcome);
                assert!(logical.obligations.is_empty());
            }
        }
    }
}
