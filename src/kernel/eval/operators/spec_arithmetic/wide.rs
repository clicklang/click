//! The supported 128-bit logical operators retain their mathematical source
//! and domain. Operand equalities cannot replace that source during lowering.
use super::*;

fn observe(value: &CValue) -> Option<IntegerTerm> {
    let ty = match value.c_type() {
        CType::Bool => MachineIntegerType::UInt8,
        ty => MachineIntegerType::from_c_type(ty)?,
    };
    IntegerTerm::from_machine(ty, crate::kernel::spec::c_value_bitvector_term(value)?)
}

pub(super) fn apply(
    op: MachineBinaryOp,
    left: &CValue,
    right: &CValue,
    facts: &ExecutionFacts,
    inherited: &[ProofObligation],
) -> Option<CExpressionPath> {
    let destination = match op {
        MachineBinaryOp::Multiply
            if (matches!(left, CValue::Int128(_)) || matches!(right, CValue::Int128(_)))
                && !matches!(left, CValue::UInt128(_))
                && !matches!(right, CValue::UInt128(_)) =>
        {
            MachineIntegerType::Int128
        }
        MachineBinaryOp::Divide | MachineBinaryOp::Remainder => match (left, right) {
            (CValue::Int128(_), CValue::Int128(_)) => MachineIntegerType::Int128,
            (CValue::UInt128(_), CValue::UInt128(_)) => MachineIntegerType::UInt128,
            _ => return None,
        },
        _ => return None,
    };
    let left = observe(left)?;
    let right = observe(right)?;
    let mut obligations = inherited.to_vec();
    let mut domain = Vec::new();
    let mut require = |proposition: Proposition| {
        if !matches!(&proposition, Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) if actual == expected)
        {
            domain.push(proposition);
        }
    };
    let result = if op == MachineBinaryOp::Multiply {
        let product = IntegerTerm::multiply(left, right);
        let (min, max) = destination.format().bounds();
        require(Proposition::ConditionIs(
            ConditionTerm::integer_greater_equal(product.clone(), IntegerTerm::constant(min)),
            true,
        ));
        require(Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(product.clone(), IntegerTerm::constant(max)),
            true,
        ));
        product
    } else {
        require(Proposition::ConditionIs(
            ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(0)),
            false,
        ));
        if destination == MachineIntegerType::Int128 {
            let min =
                ConditionTerm::integer_equal(left.clone(), IntegerTerm::constant(i128::MIN.into()));
            let minus_one =
                ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(-1));
            // Either operand excludes MIN / -1. Keep this disjunction scoped
            // with the other domain debts, never as an assumed path fact.
            if !matches!(min, ConditionTerm::Constant(false))
                && !matches!(minus_one, ConditionTerm::Constant(false))
            {
                require(Proposition::Or(
                    Box::new(Proposition::ConditionIs(min, false)),
                    Box::new(Proposition::ConditionIs(minus_one, false)),
                ));
            }
        }
        if op == MachineBinaryOp::Remainder {
            IntegerTerm::truncating_remainder(left, right)
        } else {
            IntegerTerm::truncating_quotient(left, right)
        }
    };
    if let Some(domain) = Proposition::arithmetic_domain(domain) {
        obligations.push(
            ProofObligation::evaluation_domain(domain)
                .with_context("wide arithmetic expression is defined"),
        );
    }
    let term = result
        .as_const()
        .and_then(|constant| {
            crate::kernel::machine_integer::range::constant_word(destination, constant)
        })
        .unwrap_or_else(|| Bitvector32Term::IntegerToMachine {
            value: result.into(),
            destination,
        });
    Some(CExpressionPath {
        outcome: CExpressionOutcome::Value(match destination {
            MachineIntegerType::Int128 => CValue::Int128(term),
            MachineIntegerType::UInt128 => CValue::UInt128(term),
            _ => unreachable!(),
        }),
        facts: facts.clone(),
        obligations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn value(format: MachineIntegerType, constant: i128) -> CValue {
        let term =
            crate::kernel::machine_integer::range::constant_word(format, &constant.into()).unwrap();
        match format {
            MachineIntegerType::Int128 => CValue::Int128(term),
            MachineIntegerType::UInt128 => CValue::UInt128(term),
            _ => unreachable!(),
        }
    }

    #[test]
    fn undefined_wide_arithmetic_keeps_a_value_and_an_unproved_domain() {
        for (op, left, right) in [
            (MachineBinaryOp::Multiply, i128::MAX, 2),
            (MachineBinaryOp::Divide, i128::MIN, -1),
            (MachineBinaryOp::Remainder, i128::MIN, -1),
            (MachineBinaryOp::Divide, 1, 0),
            (MachineBinaryOp::Remainder, 1, 0),
        ] {
            let path = apply(
                op,
                &value(MachineIntegerType::Int128, left),
                &value(MachineIntegerType::Int128, right),
                &ExecutionFacts::default(),
                &[],
            )
            .unwrap();
            assert!(matches!(
                path.outcome,
                CExpressionOutcome::Value(CValue::Int128(_))
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
                let logical = apply(op, &left, &right, &ExecutionFacts::default(), &[]).unwrap();
                let execute = match op {
                    MachineBinaryOp::Multiply => apply_c_multiply,
                    MachineBinaryOp::Divide => apply_c_divide,
                    MachineBinaryOp::Remainder => apply_c_remainder,
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
