//! `arithmetic() using { ... }` on a linear `uint64` order goal.
//!
//! The arithmetic certificates read `int32` and `Integer` claims. A 64-bit
//! unsigned goal is proved through its exact Integer observations, by the
//! steps a proof would write by hand: each listed 64-bit order premise is
//! carried to Integer order by its bridge theorem, each sum or difference in
//! the premises and the goal is shown not to wrap and then observed term by
//! term, the Integer claim is proved by the Integer certificate, and the
//! bridge back concludes the goal. Every step is an `apply` of a standard
//! theorem or an Integer `arithmetic`, recorded as such, so the expansion is
//! that explicit script and nothing here is trusted.
use super::*;

/// The largest `uint64`, as the no-wrap guard of
/// `uint64_add_to_integer` writes it.
const UINT64_MAX: &str = "18446744073709551615";

/// `left < right` or `left <= right`, as the bridges state order. A
/// comparison written the other way round is read with its sides exchanged.
fn order_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression, bool, bool)> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let (lower, upper, strict, written_forward) = match operator {
        ComparisonOperator::LessThan => (left, right, true, true),
        ComparisonOperator::LessEqual => (left, right, false, true),
        ComparisonOperator::GreaterThan => (right, left, true, false),
        ComparisonOperator::GreaterEqual => (right, left, false, false),
        _ => return None,
    };
    Some((lower.clone(), upper.clone(), strict, written_forward))
}

fn order(lower: ContractExpression, upper: ContractExpression, strict: bool) -> ClickProposition {
    ClickProposition::Comparison {
        left: lower,
        operator: if strict {
            ComparisonOperator::LessThan
        } else {
            ComparisonOperator::LessEqual
        },
        right: upper,
    }
}

/// The exact Integer observation of a `uint64` expression. A literal is
/// written as the Integer it is: the Integer certificate reads a premise as
/// it is spelled, and `to_integer(2u64)` spelled out is an atom to it.
fn to_integer(expression: &ContractExpression) -> ContractExpression {
    if let ContractExpression::CFragment(CExpression::Value(CValue::UInt64(value))) = expression
        && let Some(constant) = value.uint64_as_const()
    {
        return ContractExpression::IntegerLiteral(constant.to_string());
    }
    ContractExpression::Call {
        name: "to_integer".to_string(),
        arguments: vec![expression.clone()],
    }
}

/// The sums and differences inside `expression`, innermost first.
fn collect_operations(expression: &ContractExpression, operations: &mut Vec<ContractExpression>) {
    if let ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) =
        expression
    {
        collect_operations(left, operations);
        collect_operations(right, operations);
        if !operations.contains(expression) {
            operations.push(expression.clone());
        }
    }
}

fn have(proposition: ClickProposition, proof: Vec<ProofStep>) -> ProofStep {
    ProofStep::Have {
        proposition,
        proof: Box::new(ProofCertificate::from_validated_steps(proof)),
    }
}

fn apply(name: &str, arguments: Vec<ContractExpression>, premise: ClickProposition) -> ProofStep {
    ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: name.to_string(),
            arguments,
        },
        premises: vec![premise],
    }
}

impl<'a> Proof<'a> {
    /// Closes a `uint64` order goal from the listed premises through their
    /// Integer observations. `Err(None)` is any other goal, which is left
    /// to the certificate families; `Err(Some(reason))` is a `uint64` order
    /// goal this route could not prove, with the step that stopped it.
    pub(in crate::surface::proof) fn try_wide_arithmetic_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<Self, Option<String>> {
        let unsigned_order = |proposition: &Proposition| {
            matches!(
                proposition,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector64UnsignedLessThan(..)
                        | ConditionTerm::Bitvector64UnsignedLessEqual(..)
                        | ConditionTerm::Bitvector64UnsignedGreaterThan(..)
                        | ConditionTerm::Bitvector64UnsignedGreaterEqual(..),
                    true
                )
            )
        };
        if !self.goal().is_some_and(unsigned_order) {
            return Err(None);
        }
        let describe = crate::surface::diagnostics::describe_contract_expression;
        let (goal_lower, goal_upper, goal_strict, goal_forward) = self
            .surface_goal()
            .and_then(order_parts)
            .ok_or_else(|| Some("the uint64 goal has no source spelling to read".to_string()))?;
        if !goal_forward {
            return Err(Some(
                "a uint64 goal is read as `left < right` or `left <= right`; write it that way round"
                    .to_string(),
            ));
        }

        let mut proof = self.clone();
        // The Integer facts established so far, each an exact premise of
        // the Integer steps that follow.
        let mut facts = Vec::new();
        let mut operations = Vec::new();
        for premise in surface_premises {
            let kernel = self
                .lower_cited_surface_proposition(premise, "`arithmetic using` premise")
                .map_err(|error| Some(error.message().to_string()))?;
            if !unsigned_order(&kernel) {
                // An Integer premise is used as it is written.
                facts.push(premise.clone());
                continue;
            }
            let (lower, upper, strict, forward) = order_parts(premise).ok_or(None)?;
            if !forward {
                return Err(Some(format!(
                    "a uint64 premise is read as `left < right` or `left <= right`; write `{}` that way round",
                    crate::surface::printing::source_click_proposition(premise)
                )));
            }
            let observed = order(to_integer(&lower), to_integer(&upper), strict);
            let bridge = if strict {
                "uint64_less_than_to_integer"
            } else {
                "uint64_less_equal_to_integer"
            };
            proof = proof
                .apply_step(have(
                    observed.clone(),
                    vec![apply(
                        bridge,
                        vec![lower.clone(), upper.clone()],
                        premise.clone(),
                    )],
                ))
                .map_err(|error| Some(error.message().to_string()))?;
            facts.push(observed);
            collect_operations(&lower, &mut operations);
            collect_operations(&upper, &mut operations);
        }
        collect_operations(&goal_lower, &mut operations);
        collect_operations(&goal_upper, &mut operations);

        // Each sum or difference is observed term by term once its guard,
        // that it does not wrap, follows from the facts before it.
        for operation in &operations {
            let (guard, bridge, left, right, observed) = match operation {
                ContractExpression::Add(left, right) => (
                    order(
                        ContractExpression::Add(
                            Box::new(to_integer(left)),
                            Box::new(to_integer(right)),
                        ),
                        ContractExpression::IntegerLiteral(UINT64_MAX.to_string()),
                        false,
                    ),
                    "uint64_add_to_integer",
                    left,
                    right,
                    ContractExpression::Add(
                        Box::new(to_integer(left)),
                        Box::new(to_integer(right)),
                    ),
                ),
                ContractExpression::Subtract(left, right) => (
                    order(to_integer(right), to_integer(left), false),
                    "uint64_subtract_to_integer",
                    left,
                    right,
                    ContractExpression::Subtract(
                        Box::new(to_integer(left)),
                        Box::new(to_integer(right)),
                    ),
                ),
                _ => unreachable!("only sums and differences are collected"),
            };
            proof = proof
                .apply_step(have(
                    guard.clone(),
                    vec![ProofStep::ArithmeticUsing(facts.clone())],
                ))
                .map_err(|_| {
                    Some(format!(
                        "the listed premises do not show that `{}` stays within uint64 (`{}`); a uint64 sum or difference that may wrap is not the sum or difference of its operands",
                        describe(operation),
                        crate::surface::printing::source_click_proposition(&guard)
                    ))
                })?;
            let equation = ClickProposition::Comparison {
                left: to_integer(operation),
                operator: ComparisonOperator::Equal,
                right: observed,
            };
            proof = proof
                .apply_step(have(
                    equation.clone(),
                    vec![apply(
                        bridge,
                        vec![left.as_ref().clone(), right.as_ref().clone()],
                        guard,
                    )],
                ))
                .map_err(|error| Some(error.message().to_string()))?;
            facts.push(equation);
        }

        let observed_goal = order(
            to_integer(&goal_lower),
            to_integer(&goal_upper),
            goal_strict,
        );
        proof = proof
            .apply_step(have(
                observed_goal.clone(),
                vec![ProofStep::ArithmeticUsing(facts)],
            ))
            .map_err(|_| {
                Some(format!(
                    "the goal's Integer reading `{}` does not follow from the listed premises' Integer readings by one Integer `arithmetic` step, which combines at most two order premises; state an intermediate fact with `have` first",
                    crate::surface::printing::source_click_proposition(&observed_goal)
                ))
            })?;
        let applied = proof
            .apply_step(apply(
                if goal_strict {
                    "uint64_less_than_of_to_integer"
                } else {
                    "uint64_less_equal_of_to_integer"
                },
                vec![goal_lower, goal_upper],
                observed_goal,
            ))
            .map_err(|error| Some(error.message().to_string()))?;
        if applied.is_complete() || applied.goal() != self.goal() {
            return Ok(applied);
        }
        applied
            .try_direct_logical_closure()
            .ok()
            .flatten()
            .ok_or_else(|| Some("the bridged goal did not close".to_string()))
    }
}
