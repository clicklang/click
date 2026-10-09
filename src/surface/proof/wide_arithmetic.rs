//! `arithmetic() using { ... }` on a linear `uint64` or `int64` order goal.
//!
//! The arithmetic certificates read `int32` and `Integer` claims. A 64-bit
//! goal is proved through its exact Integer observations, by the
//! steps a proof would write by hand: each listed 64-bit order premise is
//! carried to Integer order by its bridge theorem, each sum or difference in
//! the premises and the goal is shown to stay in range (an unsigned one does
//! not wrap, a signed one is defined) and then observed term by term, the Integer claim is proved by the Integer certificate, and the
//! bridge back concludes the goal. Every step is an `apply` of a standard
//! theorem or an Integer `arithmetic`, recorded as such, so the expansion is
//! that explicit script and nothing here is trusted.
use super::*;

/// The largest `uint64`, as the no-wrap guard of
/// `uint64_add_to_integer` writes it.
const UINT64_MAX: &str = "18446744073709551615";
/// The range of `int64`, as the definedness theorems write it.
const INT64_MIN: &str = "-9223372036854775808";
const INT64_MAX: &str = "9223372036854775807";

/// Which 64-bit integers a goal orders.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Carrier {
    UInt64,
    Int64,
}

impl Carrier {
    fn of(proposition: &Proposition) -> Option<Self> {
        match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64UnsignedLessThan(..)
                | ConditionTerm::Bitvector64UnsignedLessEqual(..)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(..)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(..),
                true,
            ) => Some(Self::UInt64),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64SignedLessThan(..)
                | ConditionTerm::Bitvector64SignedLessEqual(..)
                | ConditionTerm::Bitvector64SignedGreaterThan(..)
                | ConditionTerm::Bitvector64SignedGreaterEqual(..),
                true,
            ) => Some(Self::Int64),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::UInt64 => "uint64",
            Self::Int64 => "int64",
        }
    }

    /// The bridge theorem `<type>_<stem>`.
    fn theorem(self, stem: &str) -> String {
        format!("{}_{stem}", self.name())
    }
}

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
    if let ContractExpression::CFragment(CExpression::Value(CValue::Int64(value))) = expression
        && let Some(constant) = value.int64_as_const()
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

fn apply(
    name: &str,
    arguments: Vec<ContractExpression>,
    premises: Vec<ClickProposition>,
) -> ProofStep {
    ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: name.to_string(),
            arguments,
        },
        premises,
    }
}

impl<'a> Proof<'a> {
    /// Closes a `uint64` or `int64` order goal from the listed premises
    /// through their Integer observations. `Err(None)` is any other goal,
    /// which is left to the certificate families; `Err(Some(reason))` is a
    /// 64-bit order goal this route could not prove, with the step that
    /// stopped it.
    pub(in crate::surface::proof) fn try_wide_arithmetic_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<Self, Option<String>> {
        // The caller wraps a refusal in the original arithmetic step's
        // diagnostic. Preserve bridge failures with raw summaries: rendering
        // their nested goals/premises here would embed a second diagnostic
        // inside that summary (and violate ClickError's debug invariant).
        let Some(carrier) = self.goal().and_then(Carrier::of) else {
            return Err(None);
        };
        let ty = carrier.name();
        let describe = crate::surface::diagnostics::describe_contract_expression;
        let spell = crate::surface::printing::source_click_proposition;
        let article = if carrier == Carrier::Int64 { "an" } else { "a" };
        let (goal_lower, goal_upper, goal_strict, goal_forward) = self
            .surface_goal()
            .and_then(order_parts)
            .ok_or_else(|| Some(format!("the {ty} goal has no source spelling to read")))?;
        if !goal_forward {
            return Err(Some(format!(
                "{article} {ty} goal is read as `left < right` or `left <= right`; write it that way round"
            )));
        }

        let mut proof = self.clone();
        // The Integer facts established so far, each an exact premise of
        // the Integer steps that follow.
        let mut facts = Vec::new();
        // What is still to be carried to Integer: a listed order premise,
        // or a sum or difference to observe term by term.
        enum Pending {
            Premise(
                ClickProposition,
                ContractExpression,
                ContractExpression,
                bool,
            ),
            Operation(ContractExpression),
        }
        let mut pending = Vec::new();
        let mut operations = Vec::new();
        for premise in surface_premises {
            let kernel = self
                .lower_cited_surface_proposition(premise, "`arithmetic using` premise")
                .map_err(|error| {
                    Some(format!(
                        "the premise `{}` could not be read: {}",
                        spell(premise),
                        error.raw_summary()
                    ))
                })?;
            if Carrier::of(&kernel) != Some(carrier) {
                // An Integer premise is used as it is written.
                facts.push(premise.clone());
                continue;
            }
            let (lower, upper, strict, forward) = order_parts(premise).ok_or(None)?;
            if !forward {
                return Err(Some(format!(
                    "{article} {ty} premise is read as `left < right` or `left <= right`; write `{}` that way round",
                    spell(premise)
                )));
            }
            collect_operations(&lower, &mut operations);
            collect_operations(&upper, &mut operations);
            pending.push(Pending::Premise(premise.clone(), lower, upper, strict));
        }
        collect_operations(&goal_lower, &mut operations);
        collect_operations(&goal_upper, &mut operations);
        pending.extend(operations.into_iter().map(Pending::Operation));

        // Each item is tried against the facts so far, and the passes repeat
        // while one succeeds: a sum is observed once the facts keep it in
        // range, and a premise over a signed sum once that sum is defined.
        // At most one pass per item, so the attempts are quadratic in the
        // listed premises and the operations written in them.
        let literal = |text: &str| ContractExpression::IntegerLiteral(text.to_string());
        let mut stuck = None;
        while !pending.is_empty() {
            let mut remaining = Vec::new();
            let mut progressed = false;
            let mut stuck_on_operation = false;
            stuck = None;
            for item in pending {
                let attempt = match &item {
                    Pending::Premise(premise, lower, upper, strict) => {
                        let observed = order(to_integer(lower), to_integer(upper), *strict);
                        let bridge = carrier.theorem(if *strict {
                            "less_than_to_integer"
                        } else {
                            "less_equal_to_integer"
                        });
                        proof
                            .apply_step(have(
                                observed.clone(),
                                vec![apply(
                                    &bridge,
                                    vec![lower.clone(), upper.clone()],
                                    vec![premise.clone()],
                                )],
                            ))
                            .map(|proof| (proof, observed))
                            .map_err(|error| {
                                format!(
                                    "the premise `{}` could not be carried to Integer order: {}",
                                    spell(premise),
                                    error.raw_summary()
                                )
                            })
                    }
                    Pending::Operation(operation) => {
                        let (left, right, subtract) = match operation {
                            ContractExpression::Add(left, right) => (left, right, false),
                            ContractExpression::Subtract(left, right) => (left, right, true),
                            _ => unreachable!("only sums and differences are collected"),
                        };
                        let exact = if subtract {
                            ContractExpression::Subtract(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        } else {
                            ContractExpression::Add(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        };
                        let out_of_range = |guard: &ClickProposition| {
                            format!(
                                "the listed premises do not show that `{}` stays within {ty} (`{}`); {article} {ty} sum or difference that may leave its range is not the sum or difference of its operands",
                                describe(operation),
                                spell(guard)
                            )
                        };
                        let arguments = vec![left.as_ref().clone(), right.as_ref().clone()];
                        let stem = if subtract { "subtract" } else { "add" };
                        let prove = |proof: &Self, proposition: &ClickProposition| {
                            proof
                                .apply_step(have(
                                    proposition.clone(),
                                    vec![ProofStep::ArithmeticUsing(facts.clone())],
                                ))
                                .map_err(|error| {
                                    format!(
                                        "{}: {}",
                                        out_of_range(proposition),
                                        error.raw_summary()
                                    )
                                })
                        };
                        // What the observation bridge requires.
                        let required = match carrier {
                            // An unsigned sum does not exceed the type; an
                            // unsigned difference does not go below zero.
                            Carrier::UInt64 => {
                                let guard = if subtract {
                                    order(to_integer(right), to_integer(left), false)
                                } else {
                                    order(exact.clone(), literal(UINT64_MAX), false)
                                };
                                prove(&proof, &guard).map(|proof| (proof, guard))
                            }
                            // A signed operation is defined when its exact
                            // value is in the type's range, by both bounds.
                            Carrier::Int64 => {
                                let lower = ClickProposition::Comparison {
                                    left: exact.clone(),
                                    operator: ComparisonOperator::GreaterEqual,
                                    right: literal(INT64_MIN),
                                };
                                let upper = order(exact.clone(), literal(INT64_MAX), false);
                                let defined = ClickProposition::Defined {
                                    expression: operation.clone(),
                                };
                                prove(&proof, &lower)
                                    .and_then(|proof| prove(&proof, &upper))
                                    .and_then(|proof| {
                                        let bridge = apply(
                                            &carrier.theorem(&format!(
                                                "{stem}_defined_by_integer_bounds"
                                            )),
                                            arguments.clone(),
                                            vec![lower.clone(), upper.clone()],
                                        );
                                        // The bridge concludes that this
                                        // operation does not overflow. Where
                                        // an operand is itself a sum, being
                                        // defined also says that sum is,
                                        // which is a fact by now, and
                                        // `assumption` joins the two.
                                        proof
                                            .apply_step(have(defined.clone(), vec![bridge.clone()]))
                                            .or_else(|_| {
                                                proof.apply_step(have(
                                                    defined.clone(),
                                                    vec![bridge, ProofStep::Assumption],
                                                ))
                                            })
                                            .map_err(|error| {
                                                format!(
                                                    "{}: {}",
                                                    out_of_range(&upper),
                                                    error.raw_summary()
                                                )
                                            })
                                    })
                                    .map(|proof| (proof, defined))
                            }
                        };
                        required.and_then(|(proof, requirement)| {
                            let equation = ClickProposition::Comparison {
                                left: to_integer(operation),
                                operator: ComparisonOperator::Equal,
                                right: exact.clone(),
                            };
                            proof
                                .apply_step(have(
                                    equation.clone(),
                                    vec![apply(
                                        &carrier.theorem(&format!("{stem}_to_integer")),
                                        arguments.clone(),
                                        vec![requirement],
                                    )],
                                ))
                                .map(|proof| (proof, equation))
                                .map_err(|error| {
                                    format!(
                                        "`{}` could not be observed term by term: {}",
                                        describe(operation),
                                        error.raw_summary()
                                    )
                                })
                        })
                    }
                };
                match attempt {
                    Ok((next, fact)) => {
                        proof = next;
                        facts.push(fact);
                        progressed = true;
                    }
                    Err(reason) => {
                        // Operations come before the premises that need
                        // them, so the first one left is the one to name.
                        if stuck.is_none()
                            || (matches!(item, Pending::Operation(_)) && !stuck_on_operation)
                        {
                            stuck_on_operation = matches!(item, Pending::Operation(_));
                            stuck = Some(reason);
                        }
                        remaining.push(item);
                    }
                }
            }
            pending = remaining;
            if !progressed {
                break;
            }
        }
        if !pending.is_empty() {
            return Err(Some(stuck.unwrap_or_else(|| {
                "the listed premises could not be carried to Integer order".to_string()
            })));
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
            .map_err(|error| {
                Some(format!(
                    "the goal's Integer reading `{}` does not follow from the listed premises' Integer readings by one Integer `arithmetic` step, which combines at most two order premises; state an intermediate fact with `have` first: {}",
                    spell(&observed_goal),
                    error.raw_summary()
                ))
            })?;
        let applied = proof
            .apply_step(apply(
                &carrier.theorem(if goal_strict {
                    "less_than_of_to_integer"
                } else {
                    "less_equal_of_to_integer"
                }),
                vec![goal_lower, goal_upper],
                vec![observed_goal],
            ))
            .map_err(|error| {
                Some(format!(
                    "the Integer claim could not be carried back: {}",
                    error.raw_summary()
                ))
            })?;
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
