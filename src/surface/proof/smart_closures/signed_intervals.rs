//! Expand signed interval plans into ordinary facts and Integer laws.
//! The plan supplies topology and endpoints, never semantic authority.
use super::super::wide_arithmetic::to_integer;
use super::*;

#[derive(Clone)]
enum Value {
    Claim(ClickProposition),
    Interval {
        term: ContractExpression,
        lower: ClickProposition,
        upper: ClickProposition,
        lower_endpoint: i64,
    },
    Defined(ClickProposition),
}
impl Value {
    fn facts(&self) -> Vec<ClickProposition> {
        match self {
            Self::Claim(p) | Self::Defined(p) => vec![p.clone()],
            Self::Interval { lower, upper, .. } => vec![lower.clone(), upper.clone()],
        }
    }
    fn term(&self) -> Option<ContractExpression> {
        if let Self::Interval { term, .. } = self {
            Some(term.clone())
        } else {
            None
        }
    }
}
fn number(n: i64) -> ContractExpression {
    surface_signed_integer_literal(&BigInt::from(n))
}
fn le(a: ContractExpression, b: ContractExpression) -> ClickProposition {
    ClickProposition::Comparison {
        left: a,
        operator: ComparisonOperator::LessEqual,
        right: b,
    }
}
fn eq(a: ContractExpression, b: ContractExpression) -> ClickProposition {
    ClickProposition::Comparison {
        left: a,
        operator: ComparisonOperator::Equal,
        right: b,
    }
}
fn observed(term: &ContractExpression) -> ContractExpression {
    to_integer(&native_int32_split_operand(term.clone()))
}

fn add(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Add(Box::new(a), Box::new(b))
}
fn mul(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(a), Box::new(b))
}
fn truncating(name: &str, n: ContractExpression, d: ContractExpression) -> ContractExpression {
    ContractExpression::Call {
        name: name.into(),
        arguments: vec![n, d],
    }
}
fn apply(
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

/// History and memory reads keep the selected compatibility adapter while
/// scalar arithmetic is migrated independently of read/state transport.
pub(super) fn has_retained_read_source(proposition: &ClickProposition) -> bool {
    let expressions = match proposition {
        ClickProposition::Comparison { left, right, .. } => vec![left, right],
        ClickProposition::Defined { expression } => vec![expression],
        ClickProposition::And(a, b) | ClickProposition::Or(a, b) => {
            return has_retained_read_source(a) || has_retained_read_source(b);
        }
        ClickProposition::Not(p) => return has_retained_read_source(p),
        ClickProposition::At { .. } => return true,
        _ => return false,
    };
    let mut found = false;
    for expression in expressions {
        super::super::fixed_state_proofs::conversion_conditions::walk_written_expressions(
            expression,
            &mut |part| {
                found |= matches!(
                    part,
                    ContractExpression::At { .. }
                        | ContractExpression::Old(_)
                        | ContractExpression::Field { .. }
                        | ContractExpression::Index(..)
                        | ContractExpression::ArrayIndex { .. }
                        | ContractExpression::ProgramExpression(
                            ProgramExpression::Load(_) | ProgramExpression::TypedLoad { .. }
                        )
                );
            },
        );
    }
    found
}

/// Result range and native observation bridge for one signed int32 sum.
/// Retained operands keep their exact lowered identities in the ordinary proof.
pub(super) fn is_int32_addition_obligation(goal: &Proposition) -> bool {
    use crate::kernel::IntegerTerm;
    let int32_sum = |term: &IntegerTerm| {
        matches!(term, IntegerTerm::Add(a, b)
        if [a, b].iter().all(|operand| match operand.as_ref() {
            IntegerTerm::Machine(value) => value.ty() == MachineIntegerType::Int32,
            IntegerTerm::Constant(_) => true,
            _ => false,
        }))
    };
    let native_add = |term: &IntegerTerm| {
        matches!(term, IntegerTerm::Machine(value)
            if value.ty() == MachineIntegerType::Int32
                && matches!(value.operand_view().binary(),
                    Some((MachineIntegerType::Int32, crate::kernel::MachineBinaryOp::Add, _))))
    };
    let Some((condition, true)) = goal.condition_native() else {
        return false;
    };
    let at_limit = |endpoint: &IntegerTerm, limit: i32| {
        endpoint
            .as_const()
            .is_some_and(|n| n == &BigInt::from(limit))
    };
    let (left, right) = match condition {
        ConditionTerm::IntegerLessEqual(left, right) => (left, right),
        ConditionTerm::IntegerGreaterEqual(left, right) => (right, left),
        ConditionTerm::IntegerEqual(left, right) => {
            return (native_add(left) && int32_sum(right))
                || (native_add(right) && int32_sum(left));
        }
        _ => return false,
    };
    (at_limit(left, i32::MIN) && int32_sum(right)) || (int32_sum(left) && at_limit(right, i32::MAX))
}

/// The cast's destination and which written operand holds the original value.
fn bounded_cast_shape(goal: &Proposition) -> Option<(crate::kernel::MachineIntegerFormat, bool)> {
    use crate::kernel::machine_integer::conversion;
    let Some((ConditionTerm::IntegerEqual(a, b), true)) = goal.condition_native() else {
        return None;
    };
    for (cast, original, original_on_left) in [(a, b, false), (b, a, true)] {
        let format = conversion::cast(cast, original).or_else(|| {
            conversion::integer_conversion(cast)
                .filter(|(operand, _)| operand == original)
                .map(|(_, ty)| ty.format())
        });
        if let Some(format) = format {
            return Some((format, original_on_left));
        }
    }
    None
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Retain a native read's available domain or its recorded initialization.
    /// Observation identities themselves need only their outer range guards.
    pub(in crate::surface::proof) fn prepare_integer_read_domain(
        proof: &Proof<'a>,
        domain: ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prepare_integer_read_domain");
        let scope = proof.driver().open_have(domain)?;
        if let Ok(closed) = scope.driver().apply_step(ProofStep::Known).or_else(|_| {
            scope
                .driver()
                .apply_step(ProofStep::NormalizeUsing(Vec::new()))
        }) {
            return Ok(Some(closed.join()?));
        }
        Ok(None)
    }

    /// Discover connected bounds within the solve budget and replay the same
    /// proof as the selected form. The fast cast rule never searches facts.
    pub(in crate::surface::proof) fn try_bounded_cast_identity_closure(
        input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_bounded_cast_identity_closure");
        let (Some(goal), Some(surface)) = (input.goal(), input.surface_goal()) else {
            return Ok(None);
        };
        if bounded_cast_shape(goal).is_none() || has_retained_read_source(surface) {
            return Ok(None);
        }
        let Some(candidates) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        if candidates.len() > 64 {
            return Ok(None);
        }
        let Some(pairs) = Self::resolve_solve_premises(input, &candidates, &[]) else {
            return Ok(None);
        };
        let premises = pairs
            .into_iter()
            .map(|(_, source)| source)
            .collect::<Vec<_>>();
        Self::try_bounded_cast_identity_using(input, &premises)
    }

    /// Weaken the selected bounds to the exact destination range, then
    /// use the same local observation rule as a written known().
    pub(in crate::surface::proof) fn try_bounded_cast_identity_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_bounded_cast_identity_using");
        let (Some(goal), Some(ClickProposition::Comparison { left, right, .. })) =
            (input.goal(), input.surface_goal())
        else {
            return Ok(None);
        };
        let Some((format, original_on_left)) = bounded_cast_shape(goal) else {
            return Ok(None);
        };
        let source = if original_on_left { left } else { right };
        let (minimum, maximum) = format.bounds();
        let integer_literal = |value: &BigInt| {
            super::super::surface_synthesis::integer_typed_expression(
                surface_signed_integer_literal(value),
            )
        };
        let mut proof = input.clone();
        for bound in [
            le(integer_literal(&minimum), source.clone()),
            le(source.clone(), integer_literal(&maximum)),
        ] {
            let scope = proof.driver().open_have(bound)?;
            let Some(closed) = scope.driver().try_integer_composition_using(premises)? else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        proof.driver().apply_step(ProofStep::Known).map(Some)
    }

    /// Close one selected interval obligation through ordinary emitters only.
    /// This never re-enters signed interval planning or its compatibility rule.
    pub(in crate::surface::proof) fn try_interval_fact_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_interval_fact_using");
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        let mut selected = Vec::with_capacity(premises.len());
        for source in premises {
            let kernel = input.lower_cited_surface_proposition(source, "interval source")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        if crate::surface::planning::solve::computes_with_known(goal)
            || facts.pure_known_available(goal)
            || Self::known_bridge_using(input, premises)?
        {
            return input.driver().apply_step(ProofStep::Known).map(Some);
        }
        if let Some(closed) = Self::try_bounded_cast_identity_using(input, premises)? {
            return Ok(Some(closed));
        }
        // Native unsigned comparisons use their own observation, rather than
        // relabelling their bits int32. Transport a written cast explicitly.
        if matches!(goal, Proposition::ConditionIs(condition, _) if
            crate::kernel::machine_integer::comparison::structural_comparison_view(condition.native_compat())
                .is_some_and(|view| view.format == MachineIntegerType::UInt32))
            && let Some(surface @ ClickProposition::Comparison { left, right, .. }) =
                input.surface_goal()
        {
            let mut casts = Vec::new();
            for expression in [left, right] {
                let operand = match expression {
                    ContractExpression::CUnary {
                        operand,
                        lowered:
                            ProgramExpression::Cast {
                                target_type: crate::kernel::ProgramType::UInt32,
                                ..
                            },
                    } => Some(operand.as_ref().clone()),
                    ContractExpression::ProgramExpression(ProgramExpression::Cast {
                        expression,
                        target_type: crate::kernel::ProgramType::UInt32,
                        ..
                    }) => Some(ContractExpression::ProgramExpression(
                        expression.as_ref().clone(),
                    )),
                    _ => None,
                };
                if let Some(operand) = operand {
                    casts.push(eq(to_integer(expression), to_integer(&operand)));
                }
            }
            if !casts.is_empty() {
                let mut proof = input.clone();
                for identity in &casts {
                    let scope = proof.driver().open_have(identity.clone())?;
                    let Some(closed) = scope.driver().try_interval_fact_using(premises)? else {
                        return Ok(None);
                    };
                    proof = closed.join()?;
                }
                let observed_goal = observed_native_surface_comparison(goal, surface);
                let mut scope = proof.driver().open_have(observed_goal)?;
                for identity in casts {
                    scope = scope.driver().apply_step(ProofStep::Rewrite(identity))?;
                }
                let Some(closed) = scope.driver().try_integer_composition_using(premises)? else {
                    return Ok(None);
                };
                proof = closed.join()?;
                return proof.driver().apply_step(ProofStep::Known).map(Some);
            }
        }
        if let Some(closed) = Self::try_machine_bridge_using(input, premises)? {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_division_bound_using(input, premises)? {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_multiply_order_using(input, premises)? {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_product_bound_using(input, premises)? {
            return Ok(Some(closed));
        }
        Self::try_integer_composition_using(input, premises)
    }

    /// Prove a stated fact without any route back to a signed certificate.
    pub(in crate::surface::proof) fn ordinary_integer_fact(
        proof: &Proof<'a>,
        target: ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("ordinary_integer_fact");
        let mut atomic = Vec::new();
        let mut pending = premises.iter().rev().collect::<Vec<_>>();
        while let Some(premise) = pending.pop() {
            if let ClickProposition::And(a, b) = premise {
                pending.push(b);
                pending.push(a);
            } else {
                atomic.push(premise.clone());
            }
        }
        let premises = atomic.as_slice();
        let scope = proof.driver().open_have(target.clone())?;
        let retained =
            has_retained_read_source(&target) || premises.iter().any(has_retained_read_source);
        let addition = retained
            && scope
                .body()
                .goal()
                .is_some_and(is_int32_addition_obligation);
        let ordinary = || scope.driver().try_interval_fact_using(premises);
        if addition && let Some(closed) = attempt::candidate_outcome(ordinary())?.flatten() {
            return Ok(Some(closed.join()?));
        }
        if retained
            && let Some(closed) = {
                // An exact type range can be computed even when its operand
                // is written at a program point. Use the goal-local check
                // before the history and retained-read compatibility rule.
                let body = scope.body();
                let step = if body
                    .goal()
                    .is_some_and(crate::surface::planning::solve::computes_with_known)
                    && premises.iter().all(|source| {
                        body.lower_cited_surface_proposition(source, "interval source")
                            .is_ok_and(|premise| {
                                body.facts().listed_premise_available(&premise, &[], false)
                            })
                    }) {
                    ProofStep::Known
                } else {
                    ProofStep::NormalizeUsing(premises.to_vec())
                };
                attempt::candidate_outcome(scope.driver().apply_step(step))?
            }
            && closed.is_complete()
        {
            return Ok(Some(closed.join()?));
        }
        if !addition && let Some(closed) = ordinary()? {
            return Ok(Some(closed.join()?));
        }
        // A visible initialized read is not necessarily a stored pure fact.
        // Publish its domain before lowering
        // arithmetic premises or using the read as a theorem argument.
        let mut prepared = proof.clone();
        for written in written_integer_observations_with_entry(
            std::iter::once(&target).chain(premises.iter()),
            false,
        ) {
            let Some(expression) = integer_composition::observed_argument(&written) else {
                continue;
            };
            let domain = ClickProposition::Defined { expression };
            let Ok(kernel) =
                prepared.lower_cited_surface_proposition(&domain, "Integer read domain")
            else {
                continue;
            };
            if matches!(kernel, Proposition::MemoryReadDefined { .. })
                && !prepared
                    .facts()
                    .listed_premise_available(&kernel, &[], false)
            {
                let Some(next) = Self::prepare_integer_read_domain(&prepared, domain)? else {
                    return Ok(None);
                };
                prepared = next;
            }
        }
        let mut scope = prepared.driver().open_have(target)?;
        if let Some(closed) = scope.driver().try_interval_fact_using(premises)? {
            return Ok(Some(closed.join()?));
        }
        // These are the exact observation identities the plan published.
        // Rewrite the outermost recent operation first, leaving child values
        // opaque so their selected interval endpoints still name them directly.
        for premise in premises.iter().rev() {
            if let ClickProposition::Comparison {
                left: ContractExpression::Call { name, .. },
                operator: ComparisonOperator::Equal,
                ..
            } = premise
                && name == "to_integer"
            {
                scope = scope
                    .driver()
                    .apply_step(ProofStep::Rewrite(premise.clone()))?;
                if let Some(closed) = scope.driver().try_interval_fact_using(premises)? {
                    return Ok(Some(closed.join()?));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::surface::proof) fn apply_signed_interval_composition(
        proof: &Proof<'a>,
        certificate: &SignedIntervalPlan,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_signed_interval_composition");
        let mut proof = proof.clone();
        let mut values = Vec::<Value>::new();
        let mut identities = Vec::new();
        let last_interval = certificate.nodes.iter().rposition(|node| {
            crate::instrumentation::record_deterministic_work(1);
            matches!(
                node,
                SignedArithmeticStep::IntervalFromAffine { .. }
                    | SignedArithmeticStep::IntervalFromAffineDirect { .. }
                    | SignedArithmeticStep::IntervalAtom { .. }
                    | SignedArithmeticStep::IntervalIntersect { .. }
                    | SignedArithmeticStep::IntervalAdd { .. }
                    | SignedArithmeticStep::IntervalSubtract { .. }
                    | SignedArithmeticStep::IntervalMultiply { .. }
                    | SignedArithmeticStep::IntervalAddBounded { .. }
                    | SignedArithmeticStep::IntervalRemainder { .. }
                    | SignedArithmeticStep::IntervalRemainderAdd { .. }
                    | SignedArithmeticStep::IntervalShiftLeft { .. }
                    | SignedArithmeticStep::IntervalArithmeticShiftRight { .. }
                    | SignedArithmeticStep::IntervalBitwiseAnd { .. }
                    | SignedArithmeticStep::IntervalNarrowedCast { .. }
            )
        });
        for (node_index, node) in certificate.nodes.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            let mut inputs = Vec::new();
            let mut refs = Vec::new();
            use SignedArithmeticStep::*;
            let claim = match node {
                Premise { proposition, .. } => {
                    values.push(Value::Claim(proposition.clone()));
                    continue;
                }
                DefinedPremise { term, .. } => {
                    let proposition = ClickProposition::Defined {
                        expression: term.clone(),
                    };
                    let scope = proof.driver().open_have(proposition.clone())?;
                    let closed = scope.driver().apply_step(ProofStep::Known)?;
                    proof = closed.join()?;
                    values.push(Value::Defined(proposition));
                    continue;
                }
                Trivial { result } | Int32Range { result } => Some(result.clone()),
                Scale { source, result, .. } | EqualityToLessEqual { source, result, .. } => {
                    refs.push(*source);
                    Some(result.clone())
                }
                Add {
                    left,
                    right,
                    result,
                } => {
                    refs.extend([*left, *right]);
                    Some(result.clone())
                }
                EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => {
                    refs.extend([*lower, *upper]);
                    Some(result.clone())
                }
                StrictFromDisequal {
                    bound,
                    disequal,
                    result,
                } => {
                    refs.extend([*bound, *disequal]);
                    Some(result.clone())
                }
                AffinePremise {
                    source,
                    left_evidence,
                    right_evidence,
                    result,
                } => {
                    refs.extend([*source, *left_evidence, *right_evidence]);
                    Some(result.clone())
                }
                AffineConclusion {
                    source,
                    evidence,
                    result,
                } => {
                    refs.extend([*source, *evidence]);
                    Some(result.clone())
                }
                AffineConclusionWithEvidence {
                    source,
                    left_evidence,
                    right_evidence,
                    result,
                } => {
                    refs.extend([*source, *left_evidence, *right_evidence]);
                    Some(result.clone())
                }
                IntervalCompare {
                    left,
                    right,
                    result,
                    ..
                } => {
                    refs.extend([*left, *right]);
                    Some(result.clone())
                }
                _ => None,
            };
            let interval = match node {
                IntervalFromAffine {
                    source,
                    term,
                    lower,
                    upper,
                }
                | IntervalFromAffineDirect {
                    source,
                    term,
                    lower,
                    upper,
                } => {
                    refs.push(*source);
                    Some((term.clone(), *lower, *upper))
                }
                IntervalAtom { term, lower, upper } => Some((term.clone(), *lower, *upper)),
                IntervalIntersect {
                    left,
                    right,
                    result,
                } => {
                    refs.extend([*left, *right]);
                    Some((values[*left].term().unwrap(), result.lower, result.upper))
                }
                IntervalAdd {
                    left,
                    right,
                    defined,
                    result,
                }
                | IntervalSubtract {
                    left,
                    right,
                    defined,
                    result,
                }
                | IntervalMultiply {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    refs.extend([*left, *right, *defined]);
                    let (a, b) = (
                        Box::new(values[*left].term().unwrap()),
                        Box::new(values[*right].term().unwrap()),
                    );
                    let term = match node {
                        IntervalAdd { .. } => ContractExpression::Add(a, b),
                        IntervalSubtract { .. } => ContractExpression::Subtract(a, b),
                        _ => ContractExpression::Multiply(a, b),
                    };
                    Some((term, result.lower, result.upper))
                }
                IntervalAddBounded {
                    left,
                    right,
                    result,
                } => {
                    refs.extend([*left, *right]);
                    Some((
                        ContractExpression::Add(
                            Box::new(values[*left].term().unwrap()),
                            Box::new(values[*right].term().unwrap()),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalRemainder {
                    operand,
                    divisor,
                    defined,
                    result,
                } => {
                    refs.extend([*operand, *defined]);
                    Some((
                        ContractExpression::Remainder(
                            Box::new(values[*operand].term().unwrap()),
                            Box::new(number(i64::from(*divisor))),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalRemainderAdd {
                    operand,
                    remainder,
                    addend,
                    divisor,
                    result,
                } => {
                    refs.extend([*operand, *remainder]);
                    Some((
                        ContractExpression::Remainder(
                            Box::new(ContractExpression::Add(
                                Box::new(values[*operand].term().unwrap()),
                                Box::new(number(i64::from(*addend))),
                            )),
                            Box::new(number(i64::from(*divisor))),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalShiftLeft {
                    operand,
                    shift,
                    defined,
                    result,
                } => {
                    refs.extend([*operand, *defined]);
                    Some((
                        ContractExpression::ShiftLeft(
                            Box::new(values[*operand].term().unwrap()),
                            Box::new(number(i64::from(*shift))),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalArithmeticShiftRight {
                    operand,
                    shift,
                    result,
                } => {
                    refs.push(*operand);
                    Some((
                        ContractExpression::ShiftRight(
                            Box::new(values[*operand].term().unwrap()),
                            Box::new(number(i64::from(*shift))),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalBitwiseAnd {
                    operand,
                    mask,
                    result,
                } => {
                    refs.push(*operand);
                    Some((
                        ContractExpression::BitwiseAnd(
                            Box::new(values[*operand].term().unwrap()),
                            Box::new(number(i64::from(*mask as i32))),
                        ),
                        result.lower,
                        result.upper,
                    ))
                }
                IntervalNarrowedCast {
                    operand,
                    destination,
                    result,
                    ..
                } => {
                    refs.push(*operand);
                    Some((
                        ContractExpression::CUnary {
                            operand: Box::new(values[*operand].term().unwrap()),
                            lowered: crate::kernel::program_expression::cast(
                                ProgramExpression::Value(crate::kernel::int32(0)),
                                destination.program_type(),
                            ),
                        },
                        result.lower,
                        result.upper,
                    ))
                }
                _ => None,
            };
            for index in refs {
                inputs.extend(values[index].facts());
            }
            if let Some(claim) = claim {
                if let Some(scope) =
                    attempt::candidate_outcome(proof.driver().open_have(claim.clone()))?
                    && let Some(closed) = scope.driver().try_interval_fact_using(&inputs)?
                {
                    proof = closed.join()?;
                    values.push(Value::Claim(claim));
                    continue;
                }
                inputs.extend(identities.iter().cloned());
                let Some(next) = Self::ordinary_integer_fact(&proof, claim.clone(), &inputs)?
                else {
                    return Ok(None);
                };
                proof = next;
                values.push(Value::Claim(claim));
            } else if let Some((term, lo, hi)) = interval {
                if let IntervalNarrowedCast { operand, .. } = node {
                    let identity = eq(observed(&term), observed(&values[*operand].term().unwrap()));
                    let Some(next) = Self::ordinary_integer_fact(
                        &proof,
                        identity.clone(),
                        &values[*operand].facts(),
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = next;
                    inputs.push(identity.clone());
                    identities.push(identity);
                }
                if let IntervalRemainderAdd {
                    operand,
                    remainder,
                    addend,
                    divisor,
                    ..
                } = node
                {
                    let base = values[*operand].term().unwrap();
                    let old_remainder = values[*remainder].term().unwrap();
                    let k = number(i64::from(*addend));
                    let d = number(i64::from(*divisor));
                    let sum = add(base.clone(), k.clone());
                    let n = add(observed(&base), k.clone());
                    let exact_bounds = [
                        le(number(i64::from(i32::MIN)), n.clone()),
                        le(n.clone(), number(i64::from(i32::MAX))),
                    ];
                    for bound in &exact_bounds {
                        let Some(next) = Self::ordinary_integer_fact(
                            &proof,
                            bound.clone(),
                            &values[*operand].facts(),
                        )?
                        else {
                            return Ok(None);
                        };
                        proof = next;
                    }
                    let sum_identity = eq(observed(&sum), n.clone());
                    let Some(next) =
                        Self::ordinary_integer_fact(&proof, sum_identity.clone(), &exact_bounds)?
                    else {
                        return Ok(None);
                    };
                    proof = next;

                    let positive = le(number(1), d.clone());
                    let nonzero = ClickProposition::Comparison {
                        left: observed(&d),
                        operator: ComparisonOperator::NotEqual,
                        right: number(0),
                    };
                    for guard in [positive.clone(), nonzero.clone()] {
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                guard,
                                vec![ProofStep::Known],
                            ))?;
                    }
                    let math_old =
                        truncating("truncating_remainder", observed(&base), observed(&d));
                    let math_new = truncating("truncating_remainder", observed(&sum), observed(&d));
                    let mut observations = Vec::new();
                    for (dividend, native, mathematical) in [
                        (base.clone(), old_remainder.clone(), math_old.clone()),
                        (sum.clone(), term.clone(), math_new.clone()),
                    ] {
                        let domain = ClickProposition::Defined {
                            expression: native.clone(),
                        };
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                domain.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        let identity = eq(observed(&native), mathematical);
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                identity.clone(),
                                vec![apply(
                                    "int32_remainder_to_integer",
                                    vec![dividend, d.clone()],
                                    vec![domain, nonzero.clone()],
                                )],
                            ))?;
                        observations.push(identity);
                    }
                    let Value::Interval {
                        lower_endpoint: old_lo,
                        ..
                    } = &values[*remainder]
                    else {
                        return Ok(None);
                    };
                    let shift = (*old_lo + i64::from(*addend)).div_euclid(i64::from(*divisor));
                    let adjustment = i64::from(*addend) - shift * i64::from(*divisor);
                    let q = truncating("truncating_quotient", observed(&base), d.clone());
                    let translated_q = add(q.clone(), number(shift));
                    let residue = add(observed(&old_remainder), number(adjustment));
                    let original = eq(
                        observed(&base),
                        add(mul(q.clone(), d.clone()), math_old.clone()),
                    );
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            original.clone(),
                            vec![apply(
                                "truncation_identity",
                                vec![observed(&base), d.clone()],
                                vec![nonzero.clone()],
                            )],
                        ))?;
                    let expanded_product = eq(
                        mul(translated_q.clone(), d.clone()),
                        add(mul(q.clone(), d.clone()), mul(number(shift), d.clone())),
                    );
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            expanded_product.clone(),
                            vec![apply(
                                "multiply_add",
                                vec![q.clone(), number(shift), d.clone()],
                                vec![nonzero.clone()],
                            )],
                        ))?;
                    let expanded_sum_rhs =
                        add(add(mul(q.clone(), d.clone()), math_old.clone()), k.clone());
                    let expanded_sum = eq(n.clone(), expanded_sum_rhs.clone());
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            expanded_sum,
                            vec![apply(
                                "equal_add",
                                vec![
                                    observed(&base),
                                    add(mul(q.clone(), d.clone()), math_old.clone()),
                                    k.clone(),
                                    k,
                                ],
                                vec![original, nonzero.clone()],
                            )],
                        ))?;
                    let residue_algebra = eq(
                        add(
                            add(mul(q.clone(), d.clone()), mul(number(shift), d.clone())),
                            add(math_old.clone(), number(adjustment)),
                        ),
                        expanded_sum_rhs,
                    );
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            residue_algebra.clone(),
                            vec![ProofStep::Known],
                        ))?;
                    let reconstruction = eq(
                        n.clone(),
                        add(mul(translated_q.clone(), d.clone()), residue.clone()),
                    );
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            reconstruction.clone(),
                            vec![
                                ProofStep::Rewrite(expanded_product),
                                ProofStep::Rewrite(observations[0].clone()),
                                ProofStep::Rewrite(residue_algebra),
                                ProofStep::Known,
                            ],
                        ))?;
                    let guards = vec![
                        nonzero,
                        positive,
                        le(number(0), n.clone()),
                        le(number(0), residue.clone()),
                        le(
                            residue.clone(),
                            ContractExpression::Subtract(Box::new(d.clone()), Box::new(number(1))),
                        ),
                        reconstruction,
                    ];
                    for guard in &guards[2..5] {
                        let Some(next) =
                            Self::ordinary_integer_fact(&proof, guard.clone(), &inputs)?
                        else {
                            return Ok(None);
                        };
                        proof = next;
                    }
                    let mathematical = eq(
                        truncating("truncating_remainder", n.clone(), d.clone()),
                        residue.clone(),
                    );
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            mathematical,
                            vec![apply(
                                "nonnegative_remainder_from_reconstruction",
                                vec![n, d, translated_q, residue.clone()],
                                guards,
                            )],
                        ))?;
                    let translated = eq(observed(&term), residue);
                    proof = proof
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            translated.clone(),
                            vec![
                                ProofStep::Rewrite(observations[1].clone()),
                                ProofStep::Rewrite(sum_identity),
                                ProofStep::Known,
                            ],
                        ))?;
                    inputs.push(translated.clone());
                    identities.push(translated);
                }
                // Prove the exact Integer range from the children's bounds,
                // then publish the native observation identity. Endpoint proofs
                // rewrite that identity and use ordinary Integer laws.
                let exact = match &term {
                    ContractExpression::Add(a, b) => Some(ContractExpression::Add(
                        Box::new(observed(a)),
                        Box::new(observed(b)),
                    )),
                    ContractExpression::Subtract(a, b) => Some(ContractExpression::Subtract(
                        Box::new(observed(a)),
                        Box::new(observed(b)),
                    )),
                    ContractExpression::Multiply(a, b) => Some(ContractExpression::Multiply(
                        Box::new(observed(a)),
                        Box::new(observed(b)),
                    )),
                    _ => None,
                };
                if let Some(exact) = exact {
                    let bounds = [
                        le(number(i64::from(i32::MIN)), exact.clone()),
                        le(exact.clone(), number(i64::from(i32::MAX))),
                    ];
                    for bound in &bounds {
                        let Some(next) =
                            Self::ordinary_integer_fact(&proof, bound.clone(), &inputs)?
                        else {
                            return Ok(None);
                        };
                        proof = next;
                    }
                    let identity = eq(observed(&term), exact);
                    let Some(next) =
                        Self::ordinary_integer_fact(&proof, identity.clone(), &bounds)?
                    else {
                        return Ok(None);
                    };
                    proof = next;
                    inputs.push(identity.clone());
                    identities.push(identity);
                }
                // The final operation can close the original goal directly
                // from its children's bounds. Avoid publishing an unused
                // pair of native endpoints and then restating that same goal.
                if last_interval == Some(node_index)
                    && let Some(closed) = Self::try_interval_fact_using(&proof, &inputs)?
                {
                    return Ok(Some(closed));
                }
                let lower = le(number(lo), observed(&term));
                let upper = le(observed(&term), number(hi));
                for bound in [&lower, &upper] {
                    let Some(next) = Self::ordinary_integer_fact(&proof, bound.clone(), &inputs)?
                    else {
                        return Ok(None);
                    };
                    proof = next;
                }
                values.push(Value::Interval {
                    term,
                    lower,
                    upper,
                    lower_endpoint: lo,
                });
            }
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
        }
        if proof.surface_goal().is_some_and(|goal| {
            !matches!(
                surface_comparison_with_anchored_operands(goal),
                ClickProposition::Comparison { .. }
            )
        }) && let Ok(closed) = proof.driver().apply_step(ProofStep::Known)
        {
            return Ok(Some(closed));
        }
        let Some(target) = proof.surface_goal().cloned() else {
            return Ok(Some(proof.driver().apply_step(ProofStep::Known)?));
        };
        let mut premises = values[certificate.conclusion].facts();
        premises.extend(identities);
        let scope = Self::ordinary_integer_fact(&proof, target, &premises)?;
        let Some(scope) = scope else {
            return Ok(None);
        };
        Ok(Some(scope.driver().apply_step(ProofStep::Known)?))
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };
    fn check(parameters: &str, requires: &str, goal: &str) {
        let source = format!(
            "theorem migrated({parameters}) {{ {requires} ensures {goal} by {{ solve() using {{ {} }}; }} }}",
            requires.replace("requires ", "")
        );
        let expanded = expand_c_claim_source_by_label(&source, &[], "migrated.ensures_0")
            .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("solve("), "{expanded}");
        assert!(!expanded.contains("normalize("), "{source}\n{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn signed_interval_addition_expands_ordinary() {
        check(
            "x: int32, y: int32",
            "requires x < y;",
            "to_integer(x + 1) <= to_integer(y)",
        );
    }
    #[test]
    fn signed_interval_product_expands_ordinary() {
        check(
            "x: int32",
            "requires 0 <= x; requires x <= 10; requires defined(x * x);",
            "to_integer((x * x) as int32) <= 100",
        );
    }
    #[test]
    fn signed_interval_mask_expands_ordinary() {
        check("x: int32", "", "(x & 255) <= 255");
    }
    #[test]
    fn native_interval_observations_survive_fresh_replay() {
        check(
            "x: int32",
            "requires 0 <= x; requires x <= 100; requires defined(x << 2);",
            "to_integer((x << 2) as int32) <= 400",
        );
        check(
            "x: int32",
            "requires -100 <= x; requires x <= -1;",
            "to_integer((x >> 2) as int32) <= -1",
        );
    }
    #[test]
    #[ignore = "nightly: complete signed interval expansion and fresh replay"]
    fn signed_interval_operations_expand_and_replay_without_certificates() {
        let mut failures = Vec::new();
        for (requirements, goal) in [
            (
                "requires 0 <= x; requires x <= 100;",
                "to_integer(x + 1) <= to_integer(x + 2)",
            ),
            ("requires 0 <= x;", "to_integer(x - 1) < to_integer(x)"),
            (
                "requires 0 <= x; requires x <= 10;",
                "to_integer((x + x) as int32) <= 20",
            ),
            (
                "requires 0 <= x; requires x <= 100; requires defined(x % 7);",
                "to_integer((x % 7) as int32) <= 6",
            ),
            (
                "requires 0 <= x; requires x <= 100; requires 0 <= x % 8; requires x % 8 <= 2;",
                "to_integer(((x + 1) % 8) as int32) <= 3",
            ),
            (
                "requires 0 <= x; requires x <= 100; requires 6 <= x % 8; requires x % 8 <= 7;",
                "to_integer(((x + 3) % 8) as int32) <= 2",
            ),
            (
                "requires 8 <= x; requires x <= 100; requires 2 <= x % 8; requires x % 8 <= 3;",
                "1 <= to_integer(((x + -1) % 8) as int32)",
            ),
            (
                "requires -10 <= x; requires x <= 10;",
                "to_integer(x as int8) == to_integer(x)",
            ),
            (
                "requires 0 <= x; requires x <= 100;",
                "(x as uint32) <= 100u32",
            ),
        ] {
            if std::panic::catch_unwind(|| check("x: int32", requirements, goal)).is_err() {
                failures.push(goal);
            }
        }
        for (parameters, requirements, goal) in [
            (
                "a: int32, b: int32",
                "requires a == b + 1; requires 0 <= b; requires b <= 100;",
                "to_integer(a - 1) == to_integer(b)",
            ),
            (
                "a: int64",
                "requires a > -9223372036854775808i64;",
                "defined(-a)",
            ),
        ] {
            if std::panic::catch_unwind(|| check(parameters, requirements, goal)).is_err() {
                failures.push(goal);
            }
        }
        assert!(failures.is_empty(), "{failures:?}");
    }
    #[test]
    fn signed_interval_migration_rejects_missing_evidence_and_undefined_operations() {
        for source in [
            "theorem rejected(x: int32,y: int32) {requires 0<=x; requires x<=10; requires 0<=y; requires y<=10; ensures defined(x+y) by {solve() using {0<=x;0<=y;};}}",
            "theorem rejected(x: int32,y: int32) {requires defined(x+y); ensures defined(x+y) by {solve() using {};}}",
            "theorem rejected(a: int32,b: int32) {requires 0<=a; requires 0<=b; requires defined(a+b); ensures 0<=to_integer(a+b) by {solve() using {0<=a;0<=b;};}}",
            "theorem rejected(x: int32) {requires x==1; ensures defined(x+1) by {solve() using {x==1;defined(x+2147483647);};}}",
            "theorem rejected(x: int32,y: int32) {requires x<=y; ensures to_integer(x+1)<=to_integer(y) by {solve() using {x<=y;};}}",
            "theorem rejected(x: int64) {requires x==9223372036854775807i64; ensures defined(x+1i64) by {solve() using {x==9223372036854775807i64;};}}",
            "theorem rejected(x: int32) {requires x == -1; ensures defined(x << 1) by {solve() using {x == -1;};}}",
            "theorem rejected(x: int32) {requires x == -2147483648; ensures defined(x % -1) by {solve() using {x == -2147483648;};}}",
        ] {
            crate::surface::parse(source).unwrap();
            assert!(
                verify_c_sources(source, &[]).is_err(),
                "accepted missing evidence: {source}"
            );
        }
    }
    #[test]
    #[ignore = "nightly: C field-read definedness expansion and replay"]
    fn signed_definedness_over_a_produced_read_expands_ordinary() {
        let c = "struct pool { int32 used; int32 capacity; }; void init(struct pool* pool, int32 capacity) { pool->capacity = capacity; } void f(struct pool* pool) { init(pool, 1); }";
        let source = r#"
resource control(pool: struct pool*) { owns *pool; }
verifying "read.c";
void init(struct pool* pool,int32 capacity) {
    consumes *pool;
    produces control(pool);
    ensures pool->capacity == capacity;
    ensures defined(pool->capacity);
} by {step(); fold(control(pool));}
void f(struct pool* pool) {consumes *pool; produces control(pool);}
by {step(); have defined(pool->capacity - 1) by solve();}
"#;
        let mut expanded = source.to_owned();
        for function in ["init", "f"] {
            expanded = crate::surface::expand_c_claim_source(
                &expanded,
                &[("read.c", c)],
                function,
                crate::surface::ContractProofClaim::Grouped,
            )
            .unwrap();
        }
        without_implicit_solve(|| verify_c_sources(&expanded, &[("read.c", c)]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn signed_definedness_32_expands_ordinary() {
        check(
            "x: int32, y: int32",
            "requires 0 <= x; requires x <= 10; requires 0 <= y; requires y <= 20;",
            "defined(x + y)",
        );
    }
    #[test]
    fn signed_definedness_64_expands_ordinary() {
        check(
            "x: int64, y: int64",
            "requires 0i64 <= x; requires x <= 10i64; requires 0i64 <= y; requires y <= 20i64;",
            "defined(x - y)",
        );
    }
    #[test]
    #[ignore = "nightly: grouped struct-field expansion and strict replay"]
    fn signed_unfolded_struct_field_expands_and_replays_with_scalar_reads() {
        let c = "struct pair { int32 low; int32 high; }; void bump(struct pair* pair) { pair->low = pair->low + 1; }";
        let source = r#"
            predicate ordered_pair(pair: struct pair*) { 0 <= pair->low and pair->low <= pair->high }
            verifying "bump.c";
            void bump(struct pair* pair) {
                requires ordered_pair(pair);
                requires pair->low < pair->high;
                owns *pair;
                ensures ordered_pair(pair);
            } by { unfold(ordered_pair(pair)); step_until(function.exit); solve(); }
        "#;
        let expanded = crate::surface::expand_c_claim_source(
            source,
            &[("bump.c", c)],
            "bump",
            crate::surface::ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|error| panic!("{}", error.message()));
        without_implicit_solve(|| verify_c_sources(&expanded, &[("bump.c", c)]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}

#[cfg(test)]
mod bounded_cast_tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    #[test]
    #[ignore = "nightly: bounded cast expansion and strict replay matrix"]
    fn bounded_cast_identities_expand_as_explicit_range_proofs() {
        for (ty, lower, upper, identity) in [
            (
                "int32",
                "1 <= to_integer(x)",
                "to_integer(x) <= 100",
                "to_integer(x as uint32) == to_integer(x)",
            ),
            (
                "uint64",
                "1u64 <= x",
                "x <= 100u64",
                "to_integer(x) == to_integer(x as uint32)",
            ),
            (
                "int64",
                "-100 <= to_integer(x)",
                "to_integer(x) <= 100",
                "to_integer(x as int8) == to_integer(x)",
            ),
            (
                "uint32",
                "0 <= to_integer(x)",
                "to_integer(x) <= 4294967295",
                "to_integer(x as uint64) == to_integer(x)",
            ),
        ] {
            for tactic in [
                format!("solve() using {{ {lower}; {upper}; }};"),
                "solve();".into(),
            ] {
                let source = format!(
                    "theorem cast_identity(x: {ty}) {{ requires {lower}; requires {upper}; ensures {identity} by {{ {tactic} }} }}"
                );
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "cast_identity.ensures_0")
                        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
                assert!(expanded.contains("known()"), "{expanded}");
                assert!(!expanded.contains("normalize("), "{expanded}");
                assert!(!expanded.contains("solve("), "{expanded}");
                without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
            }
        }

        for source in [
            "theorem omitted(x: int64) { requires 1 <= to_integer(x); requires to_integer(x) <= 100; ensures to_integer(x as uint32) == to_integer(x) by { solve() using { to_integer(x) <= 100; }; } }",
            "theorem wraps(x: uint64) { requires 0u64 <= x; requires x <= 4294967296u64; ensures to_integer(x as uint32) == to_integer(x) by { solve() using { 0u64 <= x; x <= 4294967296u64; }; } }",
        ] {
            crate::surface::parse(source).expect("bounded cast refusal should parse");
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}
