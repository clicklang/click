//! The supported 128-bit logical operators retain their mathematical source
//! and domain. Operand equalities cannot replace that source during lowering.
use super::*;

pub(super) fn apply(
    op: MachineBinaryOp,
    a: MachineIntegerType,
    left: MachineOperandView<'_>,
    b: MachineIntegerType,
    right: MachineOperandView<'_>,
    budget: &SpecEvaluation<'_>,
) -> Option<PreparedExpression> {
    use MachineIntegerType as T;
    let destination = match op {
        MachineBinaryOp::Multiply
            if (a == T::Int128 || b == T::Int128) && a != T::UInt128 && b != T::UInt128 =>
        {
            T::Int128
        }
        MachineBinaryOp::Divide | MachineBinaryOp::Remainder
            if a == b && a.format().bits() == 128 =>
        {
            a
        }
        _ => return None,
    };
    let left = left.observe(a)?;
    let right = right.observe(b)?;
    let mut obligations = Vec::new();
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
        if SpecDivision::of(budget) == SpecDivision::CDefined {
            require(Proposition::ConditionIs(
                ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(0)),
                false,
            ));
        }
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
    let value = if let Some(term) = result.as_const().and_then(|constant| {
        crate::kernel::machine_integer::range::constant_word(destination, constant)
    }) {
        KernelTermImport::default().machine(destination, &term)
    } else {
        let integer = KernelTermImport::default().integer(&result.into());
        KernelTerm::integer_to_machine(destination, integer).expect("Integer source")
    };
    Some(PreparedExpression { value, obligations })
}
