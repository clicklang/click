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

/// A complete domain made only of established arithmetic range guards.
/// Historical/read initialization obligations are deliberately stronger.
pub(super) fn arithmetic_domain_only(domain: &Proposition) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if crate::kernel::machine_integer::definedness::range_domain_query(domain).is_some() {
        return true;
    }
    match domain {
        Proposition::And(a, b) => arithmetic_domain_only(a) && arithmetic_domain_only(b),
        Proposition::ConditionIs(ConditionTerm::Constant(value), expected) => value == expected,
        _ => false,
    }
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
        if let Ok(closed) = scope
            .driver()
            .apply_step(ProofStep::NormalizeUsing(premises.to_vec()))
            && closed.is_complete()
        {
            return Ok(Some(closed.join()?));
        }
        // A visible initialized read is not necessarily a stored pure fact.
        // Publish its domain through the simple normalizer before lowering
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
        let scope = prepared.driver().open_have(target.clone())?;
        if let Ok(closed) = scope
            .driver()
            .apply_step(ProofStep::NormalizeUsing(premises.to_vec()))
            && closed.is_complete()
        {
            return Ok(Some(closed.join()?));
        }
        let result = scope.driver().try_integer_composition_using(premises);
        let Some(closed) = result? else {
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
        let mut pending_identities = Vec::<([ClickProposition; 2], ClickProposition)>::new();
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
                let scope = proof.driver().open_have(claim.clone())?;
                if let Ok(closed) = scope
                    .driver()
                    .apply_step(ProofStep::NormalizeUsing(inputs.clone()))
                    && closed.is_complete()
                {
                    proof = closed.join()?;
                    values.push(Value::Claim(claim));
                    continue;
                }
                // Observation identities are needed only when a claim crosses
                // an operation boundary. Endpoint-only plans use their stated
                // intervals directly, without expanding unused affine bridges.
                for (bounds, identity) in pending_identities.drain(..) {
                    for bound in &bounds {
                        let scope = proof.driver().open_have(bound.clone())?;
                        proof = scope.driver().apply_step(ProofStep::Known)?.join()?;
                    }
                    let Some(next) =
                        Self::ordinary_integer_fact(&proof, identity.clone(), &bounds)?
                    else {
                        return Ok(None);
                    };
                    proof = next;
                    identities.push(identity);
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
                    operand, addend, ..
                } = node
                {
                    let exact = ContractExpression::Add(
                        Box::new(observed(&values[*operand].term().unwrap())),
                        Box::new(number(i64::from(*addend))),
                    );
                    for bound in [
                        le(number(i64::from(i32::MIN)), exact.clone()),
                        le(exact, number(i64::from(i32::MAX))),
                    ] {
                        let Some(next) =
                            Self::ordinary_integer_fact(&proof, bound, &values[*operand].facts())?
                        else {
                            return Ok(None);
                        };
                        proof = next;
                    }
                }
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
                    // State only the outer operation's ordinary range pair.
                    // Rebuilding definedness of every nested operand here
                    // repeats the growing domain tree at each interval node.
                    let range = ClickProposition::And(
                        Box::new(bounds[0].clone()),
                        Box::new(bounds[1].clone()),
                    );
                    let scope = proof.driver().open_have(range)?;
                    if let Ok(closed) = scope
                        .driver()
                        .apply_step(ProofStep::NormalizeUsing(inputs.clone()))
                        && closed.is_complete()
                    {
                        proof = closed.join()?;
                    } else {
                        for bound in &bounds {
                            let Some(next) =
                                Self::ordinary_integer_fact(&proof, bound.clone(), &inputs)?
                            else {
                                return Ok(None);
                            };
                            proof = next;
                        }
                    }
                    // Retain the complete native domain once its constituent
                    // range facts are established. Subsequent observations can
                    // reuse it instead of rebuilding nested argument domains.
                    let domain = ClickProposition::Defined {
                        expression: term.clone(),
                    };
                    let kernel =
                        proof.lower_cited_surface_proposition(&domain, "native interval domain")?;
                    if arithmetic_domain_only(&kernel) {
                        let scope = proof.driver().open_have(domain)?;
                        proof = scope.driver().apply_step(ProofStep::Known)?.join()?;
                    }
                    pending_identities.push((bounds, eq(observed(&term), exact)));
                }
                // The final operation can close the original goal directly
                // from its children's bounds. Avoid publishing an unused
                // pair of native endpoints and then restating that same goal.
                if last_interval == Some(node_index)
                    && let Ok(closed) = proof
                        .driver()
                        .apply_step(ProofStep::NormalizeUsing(inputs.clone()))
                    && closed.focused_discharged()
                {
                    return Ok(Some(closed));
                }
                let lower = le(number(lo), observed(&term));
                let upper = le(observed(&term), number(hi));
                let pair = ClickProposition::And(Box::new(lower.clone()), Box::new(upper.clone()));
                let scope = proof.driver().open_have(pair)?;
                if let Ok(closed) = scope
                    .driver()
                    .apply_step(ProofStep::NormalizeUsing(inputs.clone()))
                    && closed.is_complete()
                {
                    proof = closed.join()?;
                } else {
                    for bound in [&lower, &upper] {
                        let Some(next) =
                            Self::ordinary_integer_fact(&proof, bound.clone(), &inputs)?
                        else {
                            return Ok(None);
                        };
                        proof = next;
                    }
                }
                values.push(Value::Interval { term, lower, upper });
            }
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
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
                "requires -10 <= x; requires x <= 10;",
                "to_integer(x as int8) == to_integer(x)",
            ),
            (
                "requires 0 <= x; requires x <= 100;",
                "(x as uint32) <= 100u32",
            ),
        ] {
            check("x: int32", requirements, goal);
        }
        check(
            "a: int32, b: int32",
            "requires a == b + 1; requires 0 <= b; requires b <= 100;",
            "to_integer(a - 1) == to_integer(b)",
        );
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
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
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
            } by { unfold(ordered_pair); step_until(function.exit); solve(); }
        "#;
        let expanded = crate::surface::expand_c_claim_source(
            source,
            &[("bump.c", c)],
            "bump",
            crate::surface::ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[("bump.c", c)]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}
