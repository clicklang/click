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

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Prove a stated fact without any route back to a signed certificate.
    pub(in crate::surface::proof) fn ordinary_integer_fact(
        proof: &Proof<'a>,
        target: ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("ordinary_integer_fact");
        let scope = proof.driver().open_have(target.clone())?;
        if let Ok(closed) = scope
            .driver()
            .apply_step(ProofStep::NormalizeUsing(premises.to_vec()))
        {
            if closed.is_complete() {
                return Ok(Some(closed.join()?));
            }
        }
        let Some(closed) = scope.driver().try_integer_composition_using(premises)? else {
            #[cfg(test)]
            eprintln!("ordinary interval link missing: {target:?}; from {premises:?}");
            return Ok(None);
        };
        Ok(Some(closed.join()?))
    }

    pub(in crate::surface::proof) fn apply_signed_interval_composition(
        proof: &Proof<'a>,
        certificate: &SignedInt32Certificate,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_signed_interval_composition");
        let mut proof = proof.clone();
        let mut values = Vec::<Value>::new();
        let mut identities = Vec::new();
        for node in &certificate.nodes {
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
                inputs.extend(identities.iter().cloned());
                let Some(next) = Self::ordinary_integer_fact(&proof, claim.clone(), &inputs)?
                else {
                    return Ok(None);
                };
                proof = next;
                values.push(Value::Claim(claim));
            } else if let Some((term, lo, hi)) = interval {
                // Materialize the exact operation's bounds before observing
                // it, so no implicit solver can supply an overflow guard.
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
                    // Existing definedness is already these exact two bounds;
                    // otherwise Integer composition establishes them.
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
                    identities.push(identity.clone());
                    inputs.push(identity);
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
                values.push(Value::Interval { term, lower, upper });
            }
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
        }
        let Some(target) = proof.surface_goal().cloned() else {
            return Ok(None);
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
        assert!(
            !expanded.contains("arithmetic_certificate"),
            "{source}\n{expanded}"
        );
        assert!(!expanded.contains("solve("), "{expanded}");
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
}

#[cfg(test)]
#[test]
#[ignore = "temporary migration driver"]
fn generate_signed_library_proofs() {
    use crate::surface::expand_c_claim_source_by_label;
    let original = std::fs::read_to_string("library/integer.click").unwrap();
    let mut result = original.clone();
    let mut spans = Vec::new();
    for (start, _) in original.match_indices("arithmetic_certificate signed_int32 {") {
        let decl = original[..start].rfind("\ntheorem ").unwrap() + 1;
        let name = original[decl + 8..].split('(').next().unwrap();
        let mut end = start + original[start..].find('{').unwrap() + 1;
        let mut depth = 1;
        while depth > 0 {
            match original.as_bytes()[end] {
                b'{' => depth += 1,
                b'}' => depth -= 1,
                _ => {}
            }
            end += 1;
        }
        let premises = original[start..end]
            .split(';')
            .filter_map(|line| {
                line.split_once("premise ")
                    .and_then(|(_, s)| s.split_once(':'))
                    .and_then(|(_, s)| s.split_once("=>"))
                    .map(|(s, _)| s.trim())
            })
            .collect::<Vec<_>>()
            .join("; ");
        let mut decl_end = decl + original[decl..].find('{').unwrap() + 1;
        depth = 1;
        while depth > 0 {
            match original.as_bytes()[decl_end] {
                b'{' => depth += 1,
                b'}' => depth -= 1,
                _ => {}
            }
            decl_end += 1;
        }
        let source = format!(
            "{}solve() using {{ {premises}; }};{}",
            &original[decl..start],
            &original[end..decl_end]
        );
        let expanded = expand_c_claim_source_by_label(&source, &[], &format!("{name}.ensures_0"))
            .unwrap_or_else(|e| panic!("{name}: {}", e.message()));
        assert!(
            !expanded.contains("arithmetic_certificate"),
            "{name}: {expanded}"
        );
        spans.push((decl, decl_end, expanded));
    }
    for (start, end, replacement) in spans.into_iter().rev() {
        result.replace_range(start..end, &replacement);
    }
    std::fs::write("/workspace/work/signed-integer-library.click", result).unwrap();
}
