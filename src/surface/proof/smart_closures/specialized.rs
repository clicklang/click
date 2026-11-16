//! Ordinary selected-premise proofs for the specialized arithmetic planner.
//! Plans select explicit inputs; only ordinary steps establish their results.
use super::*;

fn multiply(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(a), Box::new(b))
}

/// Select one mathematical distributivity rewrite in written source. Native
/// observations, calls, reads and other opaque expressions are never opened.
fn distribution(
    expression: &ContractExpression,
) -> Option<(ContractExpression, ContractExpression)> {
    use ContractExpression as E;
    match expression {
        E::Add(a, b) | E::Subtract(a, b) | E::Multiply(a, b) => {
            if let Some(step) = distribution(a).or_else(|| distribution(b)) {
                return Some(step);
            }
            if !matches!(expression, E::Multiply(..)) {
                return None;
            }
            for (sum, factor, left) in [(a, b, true), (b, a, false)] {
                let (p, q, subtract) = match sum.as_ref() {
                    E::Add(p, q) => (p, q, false),
                    E::Subtract(p, q) => (p, q, true),
                    _ => continue,
                };
                let product = |x: &E| {
                    if left {
                        multiply(x.clone(), factor.as_ref().clone())
                    } else {
                        multiply(factor.as_ref().clone(), x.clone())
                    }
                };
                let (u, v) = (Box::new(product(p)), Box::new(product(q)));
                return Some((
                    expression.clone(),
                    if subtract {
                        E::Subtract(u, v)
                    } else {
                        E::Add(u, v)
                    },
                ));
            }
            None
        }
        E::Negate(inner) => distribution(inner),
        E::At {
            selector,
            expression,
        } => distribution(expression).map(|(a, b)| {
            (
                E::At {
                    selector: selector.clone(),
                    expression: Box::new(a),
                },
                E::At {
                    selector: selector.clone(),
                    expression: Box::new(b),
                },
            )
        }),
        E::Old(inner) => {
            distribution(inner).map(|(a, b)| (E::Old(Box::new(a)), E::Old(Box::new(b))))
        }
        _ => None,
    }
}

pub(super) fn needs_distribution(goal: &ClickProposition) -> bool {
    matches!(goal, ClickProposition::Comparison {left,right,..}
        if distribution(left).is_some() || distribution(right).is_some())
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn apply_specialized_composition(
        proof: &Proof<'a>,
        plan: &SpecializedCompositionPlan,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_specialized_composition");
        // Current specialized plans consist of one primitive rule. This is a
        // syntax adapter for that planner, not an interpreter for authored
        // compatibility certificates.
        let [node] = plan.nodes.as_slice() else {
            return Ok(None);
        };
        use SpecialArithmeticNode::*;
        let (indices, result, polynomial) = match node {
            IntegerProductBounds { bounds, result }
            | IntegerDivisionBounds { bounds, result }
            | IntegerMultiplyOrder { bounds, result }
            | IntegerQuotientBound { bounds, result }
            | IntegerBoundExclusion { bounds, result }
            | IntegerRelationTransport { bounds, result }
            | IntegerQuotientShift { bounds, result }
            | IntegerCastIdentity { bounds, result }
            | IntegerOperationIdentity { bounds, result }
            | UnsignedSumBound { bounds, result } => (bounds.clone(), result, false),
            IntegerPolynomialIdentity { result, .. } => (Vec::new(), result, true),
            PointerTranslation {
                relation,
                bounds,
                result,
            } => (
                std::iter::once(*relation)
                    .chain(bounds.iter().copied())
                    .collect(),
                result,
                false,
            ),
            PointerAlignment { premise, result } => {
                (premise.iter().copied().collect(), result, false)
            }
            PointerWordEquality {
                relation,
                alignments,
                result,
            } => (
                std::iter::once(*relation)
                    .chain(alignments.iter().copied())
                    .collect(),
                result,
                false,
            ),
            PointerWordFromAlignment { alignments, result } => (alignments.clone(), result, false),
            FloatReflexive { finite, result } => (vec![*finite], result, false),
            SignedDefined { width, .. } => {
                return Self::try_signed_definedness_bounds(proof, *width, plan.premises.clone());
            }
        };
        let Some(premises) = indices
            .iter()
            .map(|i| plan.premises.get(*i).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        let scope = proof.driver().open_have(result.clone())?;
        if !polynomial {
            // Select a rule using only its explicit inputs. Ordinary normalize
            // may use the ambient equality graph; restricted solve must not
            // turn an inapplicable rule candidate into an ambient proof.
            let selected = premises
                .iter()
                .map(|premise| {
                    proof.lower_cited_surface_proposition(premise, "specialized arithmetic input")
                })
                .collect::<Result<Vec<_>, _>>()?;
            let Some(goal) = scope.body().goal() else {
                return Ok(None);
            };
            if crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                goal,
                &selected,
                &crate::kernel::proof::ProofFacts::from_ordered(&selected),
            )
            .is_err()
            {
                return Ok(None);
            }
        }
        if let Ok(closed) = scope
            .driver()
            .apply_step(ProofStep::NormalizeUsing(premises))
            && closed.is_complete()
        {
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }
        if !polynomial {
            return Ok(None);
        }
        let mut body = scope;
        // Each rewrite runs under the ordinary smart work budget and the
        // explicit rewrite-count bound below. Each distribution is written
        // and checked separately. Never
        // put a cross product of monomials in a simple normalization check.
        for _ in 0..4096 {
            let Some(ClickProposition::Comparison { left, right, .. }) = body.body().surface_goal()
            else {
                return Ok(None);
            };
            let Some((from, to)) = distribution(left).or_else(|| distribution(right)) else {
                let closed = body.driver().apply_step(ProofStep::Normalize)?;
                return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
            };
            let equality = ClickProposition::Comparison {
                left: from,
                operator: ComparisonOperator::Equal,
                right: to,
            };
            let nested = body.driver().open_have(equality.clone())?;
            let checked = nested.driver().apply_step(ProofStep::Normalize)?;
            body = body.join_nested(checked)?;
            body = body.driver().apply_step(ProofStep::Rewrite(equality))?;
            if body.is_complete() {
                return Ok(Some(body.join()?.driver().apply_step(ProofStep::Known)?));
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::without_implicit_solve;
    use crate::surface::*;

    fn replay(parameters: &str, requirements: &str, goal: &str, listed: &str) {
        let source = format!(
            "theorem specialized({parameters}) {{ {requirements} ensures {goal} by {{ solve() using {{ {listed} }}; }} }}"
        );
        let expanded = expand_c_claim_source_by_label(&source, &[], "specialized.ensures_0")
            .unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    fn polynomial_distribution_expands_into_ordinary_rewrites() {
        replay(
            "a: Integer, b: Integer",
            "",
            "(a + b) * (a - b) == a * a - b * b",
            "",
        );
    }
    #[test]
    #[ignore = "nightly: specialized arithmetic expansion and strict fresh replay matrix"]
    fn specialized_rules_expand_and_replay_without_certificates() {
        replay(
            "a: Integer, b: Integer, f: Integer",
            "requires a <= b; requires f <= 0;",
            "b * f <= a * f",
            "a <= b; f <= 0;",
        );
        replay(
            "n: Integer, d: Integer, b: Integer",
            "requires d != 0; requires 1 <= d; requires b * d <= n;",
            "b <= truncating_quotient(n,d)",
            "b * d <= n; 1 <= d;",
        );
        replay(
            "x: Integer, k: Integer",
            "requires 0 <= x; requires 0 <= k;",
            "truncating_quotient(x + 3 * k,3) == truncating_quotient(x,3) + k",
            "0 <= x; 0 <= k;",
        );
        replay(
            "p: int32*, word: uint64",
            "requires aligned(p,8);",
            "(((word & 7) | address(p)) & 3) == (word & 3)",
            "aligned(p,8);",
        );
        replay(
            "x: Integer, y: Integer",
            "requires -5 <= x; requires x <= 7; requires 2 <= y; requires y <= 4;",
            "truncating_quotient(x,y) <= 3",
            "-5 <= x; x <= 7; 2 <= y; y <= 4;",
        );
    }
    #[test]
    fn specialized_normalization_refuses_missing_evidence_and_false_identities() {
        for source in [
            "theorem bad(a: Integer,b: Integer,f: Integer) { requires a <= b; ensures b*f <= a*f by { normalize() using { a <= b; }; } }",
            "theorem bad(x: Integer,k: Integer) { requires 0 <= k; ensures truncating_quotient(x + 3*k,3) == truncating_quotient(x,3)+k by { normalize() using { 0 <= k; }; } }",
            "theorem bad(a: Integer,b: Integer) { ensures (a+b)*(a-b) == a*a+b*b by { solve(); } }",
            "theorem bad(p: int32*, q: int32*, r: int32*) { requires p == q; requires q == r; ensures p == r by { solve() using { p == q; }; } }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod historical_read_tests {
    use crate::surface::*;
    #[test]
    #[ignore = "nightly: global entry observation identity and strict replay"]
    fn historical_global_observations_expand_from_range_guards() {
        let c = "int32 counter = 3; int32 bump() { counter = counter + 1; return counter; }";
        let source = r#"verifying "counter.c";
            int32 bump() {
                requires counter < 1000; owns counter;
                ensures result == old(counter) + 1;
            } by {
                step_until(function.exit);
                solve();
            }"#;
        let expanded = expand_c_claim_source(
            source,
            &[("counter.c", c)],
            "bump",
            ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[("counter.c", c)]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
    #[test]
    #[ignore = "nightly: historical loop measure expansion and strict replay"]
    fn historical_loop_measure_expands_and_replays_ordinary() {
        let c = "struct box { int32 len; }; int32 drain(struct box* box) { while (box->len > 0) { box->len = box->len - 1; } return box->len; }";
        let source = r#"verifying "drain.c";
            int32 drain(struct box* box) {
                owns box->len;
                requires box->len >= 0;
                ensures result == 0;
            } by {
                loop {
                    decreases box->len;
                    invariant 0 <= box->len;
                    initialize by solve();
                    preserve by {
                        have 0 <= to_integer(box->len - 1);
                        step();
                    }
                }
                step();
                solve();
            }"#;
        let expanded = expand_c_claim_source(
            source,
            &[("drain.c", c)],
            "drain",
            ContractProofClaim::Grouped,
        )
        .unwrap_or_else(|e| panic!("{}", e.message()));
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[("drain.c", c)]))
            .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
    }
}
