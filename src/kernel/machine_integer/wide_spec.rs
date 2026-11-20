//! Definedness and mathematical results for 128-bit specification arithmetic.
use crate::kernel::eval::SpecDivision;
use crate::kernel::{
    ConditionTerm, IntegerTerm, MachineBinaryOp, MachineIntegerType, ProofObligation, Proposition,
};

pub(in crate::kernel) fn result_type(
    op: MachineBinaryOp,
    a: MachineIntegerType,
    b: MachineIntegerType,
) -> Option<MachineIntegerType> {
    use MachineIntegerType as T;
    match op {
        MachineBinaryOp::Multiply
            if (a == T::Int128 || b == T::Int128) && a != T::UInt128 && b != T::UInt128 =>
        {
            Some(T::Int128)
        }
        MachineBinaryOp::Divide | MachineBinaryOp::Remainder
            if a == b && a.format().bits() == 128 =>
        {
            Some(a)
        }
        _ => None,
    }
}

pub(in crate::kernel) fn result_and_domain(
    op: MachineBinaryOp,
    division: SpecDivision,
    destination: MachineIntegerType,
    left: IntegerTerm,
    right: IntegerTerm,
) -> (IntegerTerm, Option<ProofObligation>) {
    let mut domain = Vec::new();
    let mut require = |proposition: Proposition| {
        if !matches!(proposition.condition_native(), Some((ConditionTerm::Constant(actual), expected)) if actual == expected)
        {
            domain.push(proposition);
        }
    };
    let result = if op == MachineBinaryOp::Multiply {
        let product = IntegerTerm::multiply(left, right);
        let (min, max) = destination.format().bounds();
        require(Proposition::condition_is(
            ConditionTerm::integer_greater_equal(product.clone(), IntegerTerm::constant(min)),
            true,
        ));
        require(Proposition::condition_is(
            ConditionTerm::integer_less_equal(product.clone(), IntegerTerm::constant(max)),
            true,
        ));
        product
    } else {
        if division == SpecDivision::CDefined {
            require(Proposition::condition_is(
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
                    Box::new(Proposition::condition_is(min, false)),
                    Box::new(Proposition::condition_is(minus_one, false)),
                ));
            }
        }
        if op == MachineBinaryOp::Remainder {
            IntegerTerm::truncating_remainder(left, right)
        } else {
            IntegerTerm::truncating_quotient(left, right)
        }
    };
    let obligation = Proposition::arithmetic_domain(domain).map(|domain| {
        ProofObligation::evaluation_domain(domain)
            .with_context("wide arithmetic expression is defined")
    });
    (result, obligation)
}
