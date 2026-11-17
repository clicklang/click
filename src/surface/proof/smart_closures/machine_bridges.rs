//! Ordinary observation and conditional bridges from explicitly selected facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Decide only whether this local rule can consume the selected context.
    /// Discovery does not borrow omitted bounds or guards from ambient facts.
    pub(in crate::surface::proof) fn known_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("known_bridge_using");
        let Some(goal) = input.goal() else {
            return Ok(false);
        };
        let readings =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal);
        let check = |available: &dyn Fn(&Proposition) -> bool| {
            crate::kernel::proof::fact_reasoning::known_bridge_leaf(goal, &available)
                || readings.iter().any(|reading| {
                    crate::kernel::proof::fact_reasoning::known_bridge_leaf(reading, &available)
                })
        };
        let mut selected = Vec::with_capacity(premises.len());
        for premise in premises {
            let kernel =
                input.lower_cited_surface_proposition(premise, "observation bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(false);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        Ok(check(&|p| facts.pure_known_available(p)))
    }
}

fn integer_parts(
    proposition: &Proposition,
) -> Option<(
    &crate::kernel::SharedIntegerTerm,
    &crate::kernel::SharedIntegerTerm,
)> {
    match proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(a, b)
            | ConditionTerm::IntegerLessThan(a, b)
            | ConditionTerm::IntegerEqual(a, b),
            true,
        ) => Some((a, b)),
        Proposition::ConditionIs(
            ConditionTerm::IntegerGreaterEqual(a, b) | ConditionTerm::IntegerGreaterThan(a, b),
            true,
        ) => Some((b, a)),
        _ => None,
    }
}

fn number(value: impl Into<BigInt>) -> ContractExpression {
    super::super::surface_synthesis::integer_typed_expression(surface_signed_integer_literal(
        &value.into(),
    ))
}
fn observe(value: ContractExpression) -> ContractExpression {
    ContractExpression::Call {
        name: "to_integer".into(),
        arguments: vec![value],
    }
}
fn compare(
    left: ContractExpression,
    operator: ComparisonOperator,
    right: ContractExpression,
) -> ClickProposition {
    ClickProposition::Comparison {
        left,
        operator,
        right,
    }
}
fn le(left: ContractExpression, right: ContractExpression) -> ClickProposition {
    compare(left, ComparisonOperator::LessEqual, right)
}
fn eq(left: ContractExpression, right: ContractExpression) -> ClickProposition {
    compare(left, ComparisonOperator::Equal, right)
}
fn mul(left: ContractExpression, right: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(left), Box::new(right))
}
fn add(left: ContractExpression, right: ContractExpression) -> ContractExpression {
    ContractExpression::Add(Box::new(left), Box::new(right))
}
fn neg(value: ContractExpression) -> ContractExpression {
    ContractExpression::Negate(Box::new(value))
}
fn application(
    name: &str,
    arguments: Vec<ContractExpression>,
    premises: Vec<ClickProposition>,
) -> ProofStep {
    ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}

// Follow only the value explicitly named by this expression. Retained point
// wrappers are put on its operand, never replaced by a different point.
fn written_operands(
    input: &Proof<'_>,
    expression: &ContractExpression,
) -> Option<(ContractExpression, ContractExpression)> {
    written_operands_inner(input, expression, &mut std::collections::HashSet::new())
}
fn written_operands_inner(
    input: &Proof<'_>,
    expression: &ContractExpression,
    aliases: &mut std::collections::HashSet<String>,
) -> Option<(ContractExpression, ContractExpression)> {
    match expression {
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            written_operands_inner(input, arguments.first()?, aliases)
        }
        ContractExpression::Binding(name) => {
            if !aliases.insert(name.clone()) {
                return None;
            }
            written_operands_inner(input, input.local_binding(name)?, aliases)
        }
        ContractExpression::CUnary { operand, .. } => {
            written_operands_inner(input, operand, aliases)
        }
        ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right) => {
            Some((left.as_ref().clone(), right.as_ref().clone()))
        }
        ContractExpression::At {
            selector,
            expression,
        } => {
            let (left, right) = written_operands_inner(input, expression, aliases)?;
            Some((
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(left),
                },
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(right),
                },
            ))
        }
        ContractExpression::Old(expression) => {
            let (left, right) = written_operands_inner(input, expression, aliases)?;
            Some((
                ContractExpression::Old(Box::new(left)),
                ContractExpression::Old(Box::new(right)),
            ))
        }
        _ => None,
    }
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Replace the widened uint32-sum shortcut with its ordinary observation
    /// identity and selected Integer proof. Native widening is value preserving;
    /// the sum's int64 range follows from its operands' uint32 type ranges.
    pub(in crate::surface::proof) fn try_widened_unsigned_sum_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_widened_unsigned_sum_using");
        let (Some(goal), Some(surface)) = (input.goal(), input.surface_goal()) else {
            return Ok(None);
        };
        let Proposition::ConditionIs(condition, _) = goal else {
            return Ok(None);
        };
        if crate::kernel::PureFactContext::new()
            .widened_unsigned_sum_bound_premises(condition)
            .is_none()
            || signed_intervals::has_retained_read_source(surface)
            || premises
                .iter()
                .any(signed_intervals::has_retained_read_source)
        {
            return Ok(None);
        }
        for source in premises {
            let kernel = input.lower_cited_surface_proposition(source, "widened sum premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
        }
        // Only the goal's operations need identities; unrelated cited
        // expressions must not introduce extra overflow obligations.
        let identities = operation_identities(machine_observations(goal, &[]));
        let observed = observed_native_surface_comparison(goal, surface);
        let mut written =
            written_integer_observations(premises.iter().chain(std::iter::once(&observed)));
        // A returned scalar can name the entire sum without writing either
        // widening. Raise its two operands from the retained program state.
        // No read identities, program points, or version points are changed.
        if let Some(view) = input.premise_fixed_state_view() {
            let _recorded = super::super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                view.fixed_state.recorded_states,
            );
            let query =
                crate::kernel::machine_integer::comparison::comparison_view(condition, true)
                    .expect("recognized widened sum comparison");
            let (_, _, operands) = query.operands[0]
                .operand_view()
                .binary()
                .expect("recognized widened sum operation");
            for operand in operands {
                let operand = operand.retain(MachineIntegerType::Int64);
                let root = operand.shared_operand().ok_or_else(|| {
                    input.step_error("widened unsigned sum operand has no shared term")
                })?;
                let source = super::super::surface_synthesis::raise_kernel_term(
                    root,
                    view.parameter_binding,
                    view.fixed_state.state,
                    &BTreeMap::new(),
                )
                .ok_or_else(|| {
                    input.step_error(
                        "cannot raise a widened unsigned sum operand from its retained source",
                    )
                })?;
                written.push(observe(source));
            }
        }
        let identities = identities.iter().collect::<Vec<_>>();
        let Ok((proof, established)) =
            Self::prove_operation_identities(input, &identities, &written, Some(premises))?
        else {
            return Ok(None);
        };
        let mut sources = premises.to_vec();
        sources.extend(established.into_iter().map(|(_, source)| source));
        Self::try_integer_composition_using(&proof, &sources)
    }

    /// Prove one explicitly bounded shift or mask through local observation
    /// facts. The arithmetic in this route uses only the ordinary emitter.
    pub(in crate::surface::proof) fn try_machine_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_machine_bridge_using");
        use crate::kernel::IntegerTerm as I;
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        let has_root = |value: &crate::kernel::SharedIntegerTerm| matches!(value.as_ref(), I::Machine(machine) if machine.operand_view().binary().is_some_and(|(_, op, _)| matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight | MachineBinaryOp::BitwiseAnd)));
        let mut roots =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal);
        if roots.is_empty() {
            roots.push(goal.clone());
        }
        if !roots
            .iter()
            .any(|root| integer_parts(root).is_some_and(|(a, b)| has_root(a) || has_root(b)))
        {
            return Ok(None);
        }
        let Some(written_goal) = input.surface_goal() else {
            return Ok(None);
        };
        let observed_goal = observed_native_surface_comparison(goal, written_goal);
        let Some(canonical) = integer_composition::canonical_surface(&observed_goal) else {
            return Ok(None);
        };
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = canonical
        else {
            return Ok(None);
        };
        let lowered = input.lower_integer_surface_proposition(
            &compare(left.clone(), operator, right.clone()),
            "machine bridge goal",
        )?;
        let mut readings =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(&lowered);
        if readings.is_empty() {
            readings.push(lowered);
        }
        let Some((ka, kb)) = readings
            .iter()
            .filter_map(integer_parts)
            .find(|(a, b)| has_root(a) || has_root(b))
        else {
            return Ok(None);
        };
        for source in premises {
            let kernel = input.lower_cited_surface_proposition(source, "machine bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
        }
        for (term, surface) in [(ka, &left), (kb, &right)] {
            let I::Machine(machine) = term.as_ref() else {
                continue;
            };
            let Some((format, op, [lhs, rhs])) = machine.operand_view().binary() else {
                continue;
            };
            if format.format().bits() != machine.ty().format().bits() {
                continue;
            }
            let format = machine.ty();
            let mut commuted = false;
            let mut amount =
                if matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight) {
                    crate::kernel::machine_integer::bounds::constant_shift_count(rhs)
                        .map(BigInt::from)
                } else {
                    rhs.literal()
                        .and_then(|n| format.constant_from_term(&n))
                        .map(|n| n.to_integer())
                };
            if amount.is_none() && op == MachineBinaryOp::BitwiseAnd {
                commuted = true;
                amount = lhs
                    .literal()
                    .and_then(|n| format.constant_from_term(&n))
                    .map(|n| n.to_integer());
            }
            let Some(amount) = amount else {
                continue;
            };
            let Some((left, right)) = written_operands(input, surface) else {
                continue;
            };
            let source = if commuted { right } else { left };
            let source = observe(ContractExpression::CUnary {
                operand: Box::new(source),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(int32(0))),
                    target_type: format.program_type(),
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            });
            let observed = surface.clone();
            let mut proof = input.clone();
            let mut cited = premises.to_vec();
            // Every new fact is retained by the ordinary have driver.
            let known = |proof: &mut Proof<'a>,
                         cited: &mut Vec<ClickProposition>,
                         claim: ClickProposition|
             -> Result<(), ClickError> {
                *proof = proof
                    .driver()
                    .apply_step(super::super::wide_arithmetic::have(
                        claim.clone(),
                        vec![ProofStep::Known],
                    ))?;
                cited.push(claim);
                Ok(())
            };
            match op {
                MachineBinaryOp::BitwiseAnd if amount >= BigInt::zero() => {
                    known(&mut proof, &mut cited, le(number(0), observed.clone()))?;
                    known(&mut proof, &mut cited, le(observed.clone(), number(amount)))?;
                    let nonnegative = le(number(0), source.clone());
                    let scope = proof.driver().open_have(nonnegative.clone())?;
                    if let Some(closed) = scope.driver().try_integer_composition_using(&cited)? {
                        proof = closed.join()?;
                        cited.push(nonnegative);
                        known(&mut proof, &mut cited, le(observed.clone(), source))?;
                    }
                }
                MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight => {
                    let Some(count) = amount.to_u32().filter(|n| *n < format.format().bits())
                    else {
                        continue;
                    };
                    let scale = BigInt::one() << count;
                    if op == MachineBinaryOp::ShiftLeft {
                        let (source_min, source_max) = format.format().bounds();
                        known(
                            &mut proof,
                            &mut cited,
                            le(number(source_min), source.clone()),
                        )?;
                        known(
                            &mut proof,
                            &mut cited,
                            le(source.clone(), number(source_max)),
                        )?;
                        let factor_bound = le(number(scale.clone()), number(scale.clone()));
                        known(&mut proof, &mut cited, factor_bound)?;
                        let exact = mul(number(scale.clone()), source.clone());
                        let (min, max) = format.format().bounds();
                        let mut bounds = Vec::new();
                        if format.format().is_signed() {
                            bounds.push(le(number(0), source.clone()));
                            bounds.push(le(
                                source.clone(),
                                number(format.format().bounds().1 >> count),
                            ));
                        }
                        bounds.extend([
                            le(number(min), exact.clone()),
                            le(exact.clone(), number(max)),
                        ]);
                        for bound in bounds {
                            let scope = proof.driver().open_have(bound.clone())?;
                            let closed = if matches!(bound, ClickProposition::Comparison { ref left, ref right, .. } if matches!(left,ContractExpression::Multiply(..)) || matches!(right, ContractExpression::Multiply(..)))
                            {
                                scope.driver().try_product_bound_using(&cited)?
                            } else {
                                scope.driver().try_integer_composition_using(&cited)?
                            };
                            let Some(closed) = closed else {
                                return Ok(None);
                            };
                            proof = closed.join()?;
                            cited.push(bound);
                        }
                        let identity = eq(observed.clone(), exact.clone());
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                identity.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        let lower = term == kb;
                        let endpoint = if lower { ka.as_const() } else { kb.as_const() };
                        if let Some(endpoint) = endpoint {
                            let endpoint = if operator == ComparisonOperator::LessThan {
                                if lower {
                                    endpoint + BigInt::one()
                                } else {
                                    endpoint - BigInt::one()
                                }
                            } else {
                                endpoint.clone()
                            };
                            let product_bound = if lower {
                                le(number(endpoint), exact.clone())
                            } else {
                                le(exact.clone(), number(endpoint))
                            };
                            let scope = proof.driver().open_have(product_bound.clone())?;
                            let Some(closed) = scope.driver().try_product_bound_using(&cited)?
                            else {
                                return Ok(None);
                            };
                            proof = closed.join()?;
                            proof = proof.driver().apply_step(ProofStep::Rewrite(identity))?;
                            if proof.focused_discharged() {
                                return Ok(Some(proof));
                            }
                            if let Ok(closed) = proof.driver().apply_step(ProofStep::Known) {
                                return Ok(Some(closed));
                            }
                            cited = vec![product_bound];
                        } else {
                            cited.push(identity);
                        }
                    } else {
                        let slack: BigInt = &scale - 1;
                        let scaled = mul(number(scale.clone()), observed.clone());
                        known(&mut proof, &mut cited, le(scaled.clone(), source.clone()))?;
                        known(
                            &mut proof,
                            &mut cited,
                            le(source, add(scaled, number(slack.clone()))),
                        )?;
                        // Integer rounding is explicit. For a lower bound,
                        // negate the quotient and the requested endpoint.
                        let lower = term == kb;
                        let endpoint = if lower { ka.as_const() } else { kb.as_const() };
                        let Some(endpoint) = endpoint else {
                            return Ok(None);
                        };
                        let endpoint = if operator == ComparisonOperator::LessThan {
                            if lower {
                                endpoint + BigInt::one()
                            } else {
                                endpoint - BigInt::one()
                            }
                        } else {
                            endpoint.clone()
                        };
                        let q = if lower {
                            neg(observed.clone())
                        } else {
                            observed.clone()
                        };
                        let bound = if lower { -&endpoint } else { endpoint.clone() };
                        let threshold = add(
                            mul(number(bound.clone()), number(scale.clone())),
                            number(slack.clone()),
                        );
                        let raw_scaled = if lower {
                            neg(mul(number(scale.clone()), observed.clone()))
                        } else {
                            mul(number(scale.clone()), observed.clone())
                        };
                        if crate::instrumentation::deadline_exceeded_with_work(
                            (bound.bits() as usize + 1).saturating_mul(scale.bits() as usize + 1),
                        ) {
                            return Ok(None);
                        }
                        let threshold_value = number(&bound * &scale + &slack);
                        let threshold_equality = eq(threshold.clone(), threshold_value.clone());
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                threshold_equality.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        let raw_bound = le(raw_scaled.clone(), threshold_value);
                        let scope = proof.driver().open_have(raw_bound.clone())?;
                        let Some(closed) = scope.driver().try_integer_composition_using(&cited)?
                        else {
                            return Ok(None);
                        };
                        proof = closed.join()?;
                        let commuted = eq(
                            mul(q.clone(), number(scale.clone())),
                            mul(number(scale.clone()), q.clone()),
                        );
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                commuted.clone(),
                                vec![application(
                                    "multiply_commutative",
                                    vec![q.clone(), number(scale.clone())],
                                    vec![],
                                )],
                            ))?;
                        if lower {
                            let negated =
                                eq(mul(number(scale.clone()), q.clone()), raw_scaled.clone());
                            proof =
                                proof
                                    .driver()
                                    .apply_step(super::super::wide_arithmetic::have(
                                        negated,
                                        vec![application(
                                            "multiply_negate",
                                            vec![number(scale.clone()), observed],
                                            vec![],
                                        )],
                                    ))?;
                        }
                        let scaled_bound = le(mul(q.clone(), number(scale.clone())), threshold);
                        // Congruence combines the two named equations when the
                        // quotient was negated; then one rewrite exposes raw_bound.
                        let equality = eq(mul(q.clone(), number(scale.clone())), raw_scaled);
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                equality.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                scaled_bound.clone(),
                                vec![
                                    ProofStep::Rewrite(equality),
                                    ProofStep::Rewrite(threshold_equality),
                                    ProofStep::Known,
                                ],
                            ))?;
                        let rounded = le(q.clone(), number(bound.clone()));
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                rounded.clone(),
                                vec![application(
                                    "round_down_le",
                                    vec![
                                        q,
                                        number(bound),
                                        number(scale.clone()),
                                        number(slack.clone()),
                                    ],
                                    vec![
                                        compare(
                                            number(0),
                                            ComparisonOperator::LessThan,
                                            number(scale.clone()),
                                        ),
                                        compare(
                                            number(slack),
                                            ComparisonOperator::LessThan,
                                            number(scale),
                                        ),
                                        scaled_bound,
                                    ],
                                )],
                            ))?;
                        cited.push(rounded);
                    }
                }
                _ => continue,
            }
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            if let Some(closed) = Self::try_integer_composition_using(&proof, &cited)? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }
}

// Numeric branch selection is one local equation followed by rewriting.
// Arithmetic after the rewrite remains in the ordinary Integer emitter.
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_conditional_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_conditional_bridge_using");
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        if integer_parts(goal).is_none()
            && !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal)
                .iter()
                .any(|reading| integer_parts(reading).is_some())
        {
            return Ok(None);
        }
        let Some(ClickProposition::Comparison { left, right, .. }) = input.surface_goal() else {
            return Ok(None);
        };
        if !matches!(left, ContractExpression::If { .. })
            && !matches!(right, ContractExpression::If { .. })
        {
            return Ok(None);
        }
        let mut selected = Vec::new();
        for source in premises {
            let kernel =
                input.lower_cited_surface_proposition(source, "conditional bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        for expression in [left, right] {
            let ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } = expression
            else {
                continue;
            };
            for (guard, arm) in [
                (condition.as_ref().clone(), then_branch),
                (ClickProposition::Not(condition.clone()), else_branch),
            ] {
                let lowered =
                    input.lower_cited_surface_proposition(&guard, "conditional bridge guard")?;
                if !facts.pure_known_available(&lowered) {
                    continue;
                }
                let equality = eq(expression.clone(), arm.as_ref().clone());
                let Ok(proof) = input
                    .driver()
                    .apply_step(super::super::wide_arithmetic::have(
                        equality.clone(),
                        vec![ProofStep::Known],
                    ))
                else {
                    continue;
                };
                let rewritten = proof.driver().apply_step(ProofStep::Rewrite(equality))?;
                if rewritten.focused_discharged() {
                    return Ok(Some(rewritten));
                }
                if Self::known_bridge_using(&rewritten, premises)?
                    || rewritten
                        .goal()
                        .is_some_and(crate::kernel::proof::fact_reasoning::computes_leaf)
                {
                    return rewritten.driver().apply_step(ProofStep::Known).map(Some);
                }
                if let Some(closed) = Self::try_integer_composition_using(&rewritten, premises)? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod widened_sum_tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    fn replay(source: &str, c: &[(&str, &str)], label: &str) {
        let expanded = expand_c_claim_source_by_label(source, c, label)
            .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, c))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }

    #[test]
    #[ignore = "nightly: widened unsigned sums with strict expansion replay"]
    fn widened_unsigned_sums_expand_without_normalize() {
        for (parameters, bounds, goal) in [
            (
                "a: uint32, b: uint32",
                "a <= 10u32; b <= 20u32;",
                "a as int64 + b as int64 <= 30i64",
            ),
            (
                "a: uint32, b: uint32",
                "",
                "a as int64 + b as int64 <= 8589934590i64",
            ),
            (
                "a: uint32, b: uint8",
                "a <= 4294967040u32;",
                "a as int64 + b as int64 <= 4294967295i64",
            ),
            (
                "a: uint8, b: uint8",
                "",
                "a as int64 + b as int64 <= 510i64",
            ),
            (
                "a: uint16, b: uint16",
                "",
                "a as int64 + b as int64 <= 131070i64",
            ),
            ("a: uint32", "a <= 10u32;", "a as int64 + 7i64 <= 17i64"),
            (
                "a: uint32, b: uint32",
                "a <= 10u32; b <= 20u32;",
                "to_integer(a as int64 + b as int64) <= 30",
            ),
            (
                "a: uint32, b: uint32",
                "31u32 <= a;",
                "not (a as int64 + b as int64 <= 30i64)",
            ),
        ] {
            let requires = bounds
                .split(';')
                .filter(|p| !p.trim().is_empty())
                .map(|p| format!("requires {p};"))
                .collect::<String>();
            for tactic in [format!("solve() using {{ {bounds} }};"), "solve();".into()] {
                let source = format!(
                    "theorem widened({parameters}) {{ {requires} ensures {goal} by {{ {tactic} }} }}"
                );
                replay(&source, &[], "widened.ensures_0");
            }
        }
        let c = "long add_byte(unsigned sum, unsigned char byte) { unsigned word = (unsigned)byte; long wide = (long)sum + (long)word; return wide; }";
        let source = r#"verifying "wide.c";
            int64 add_byte(uint32 sum, uint8 byte) {
                requires sum <= 4294967040u32;
                ensures result <= 4294967295i64 by {
                    step_until(function.exit);
                    solve() using { (byte as uint32) <= 255u32; sum <= 4294967040u32; };
                }
            }"#;
        replay(source, &[("wide.c", c)], "add_byte.ensures_0");
    }

    #[test]
    #[ignore = "nightly: widened unsigned sum refusal controls"]
    fn widened_unsigned_sums_require_the_selected_bounds() {
        for (bounds, goal, selected) in [
            (
                "requires a <= 10u32; requires b <= 20u32;",
                "a as int64 + b as int64 <= 30i64",
                "a <= 10u32;",
            ),
            (
                "requires a <= 10u32; requires b <= 20u32;",
                "a as int64 + b as int64 <= 29i64",
                "a <= 10u32; b <= 20u32;",
            ),
            ("", "a as int64 + b as int64 <= 8589934589i64", ""),
        ] {
            let source = format!(
                "theorem bad(a: uint32,b: uint32) {{ {bounds} ensures {goal} by {{ solve() using {{ {selected} }}; }} }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
        }
    }
}
