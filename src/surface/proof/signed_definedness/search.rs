//! Discovery adapters over the existing persistent proof.
use super::*;
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Build and try the selected signed-definedness certificate inside search.
    /// The driver applies the same explicit certificate primitive used by replay.
    fn try_signed_definedness_certificate(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_definedness_certificate");
        let Some(surface_goal) = search_input.surface_goal() else {
            return Ok(None);
        };
        let certificate = ArithmeticCertificate::special(SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::SignedDefined {
                width,
                bounds: (0..premises.len()).collect(),
                result: surface_goal.clone(),
            }],
            premises,
            conclusion: 0,
        });
        let Some(proof) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::ArithmeticCertificate(certificate)),
        )?
        else {
            return Ok(None);
        };
        Ok(proof.focused_discharged().then_some(proof))
    }

    /// `solve` on an `int32` or `int64` definedness goal: cite the constant
    /// bounds the context indexes under each operand.
    pub(in crate::surface::proof) fn try_signed_definedness_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_definedness_closure");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some((surface_left, surface_right)) =
            search_input.signed_definedness_surface_operands()
        else {
            return Ok(None);
        };
        let interval_query = crate::kernel::machine_integer::definedness::interval_query_form(goal);
        let goal = interval_query.as_ref().unwrap_or(goal);
        let Some((width, left, right, _)) = signed_definedness_operands(goal) else {
            // `defined(a + b)` over operands that carry definedness of their
            // own lowers to a conjunction; its outermost operation is the
            // overflow conjunct no other conjunct takes as an operand.
            for (width, left, right) in outermost_overflow_conjuncts(goal) {
                let operands = [(left, surface_left), (right, surface_right)];
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_signed_definedness_with_operand_definedness(search_input, width, operands)?
                {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_signed_definedness_after_operand_substitution(search_input, width, operands)?
                {
                    return Ok(Some(closed));
                }
            }
            return Ok(None);
        };
        let premises = crate::kernel::search::ProofSearch::signed_operand_bound_premises(
            search_input,
            width,
            [(left, surface_left), (right, surface_right)],
        );
        if let Some(closed) =
            Self::try_signed_definedness_certificate(search_input, width, premises)?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_signed_definedness_after_operand_substitution(
            search_input,
            width,
            [(left, surface_left), (right, surface_right)],
        )
    }

    /// The constant bounds the context indexes under each operand, spelled
    /// through the operand's spelling in the goal.
    pub(in crate::surface::proof) fn signed_operand_bound_premises(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        operands: [(&MachineTerm, &ContractExpression); 2],
    ) -> Vec<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("signed_operand_bound_premises");
        let assumptions = search_input.facts().assumptions();
        let mut premises = Vec::new();
        for (term, surface) in operands {
            for fact in assumptions.signed_constant_bound_facts(width, term) {
                let Some(spelled) = spell_signed_bound(width, &fact, term, surface) else {
                    continue;
                };
                if !premises.contains(&spelled) {
                    premises.push(spelled);
                }
            }
        }
        premises
    }

    /// A definedness goal that lowers to a conjunction with its operands'
    /// own definedness, such as `defined(pool->capacity - 1)` over a read
    /// through a resource view: each written operand's `defined(..)` is
    /// proved as a `have` by `solve` and cited beside the operands' bounds,
    /// which the `int32_defined` / `int64_defined` rule accepts for the
    /// conjuncts beyond the operation's overflow.
    pub(in crate::surface::proof) fn try_signed_definedness_with_operand_definedness(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        operands: [(&MachineTerm, &ContractExpression); 2],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_definedness_with_operand_definedness");
        let mut premises = crate::kernel::search::ProofSearch::signed_operand_bound_premises(
            search_input,
            width,
            operands,
        );
        if premises.is_empty() {
            return Ok(None);
        }
        let mut proof = search_input.clone();
        for (term, surface) in operands {
            if signed_width_constant(width, term).is_some() {
                continue;
            }
            let defined = ClickProposition::Defined {
                expression: surface.clone(),
            };
            if premises.contains(&defined) {
                continue;
            }
            let Ok(scope) = proof.driver().open_have(defined.clone()) else {
                return Ok(None);
            };
            let Some(scope) = (scope).driver().try_solve_closure()? else {
                return Ok(None);
            };
            proof = scope.join()?;
            premises.push(defined);
        }
        Self::try_signed_definedness_certificate(&proof, width, premises)
    }

    /// An operand whose summands are fixed by exact constant equalities,
    /// such as a count `A + n` with `A == 0`, is first restated without
    /// them: `count == n` is proved as a `have` by `solve`, `defined(n + 1)`
    /// as a `have` from the bounds of `n`, and the goal, rewritten by the
    /// first, closes from both. Each summand is a keyed lookup; nothing
    /// scans the context.
    pub(in crate::surface::proof) fn try_signed_definedness_after_operand_substitution(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        operands: [(&MachineTerm, &ContractExpression); 2],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_signed_definedness_after_operand_substitution",
        );
        let Some(ClickProposition::Defined { expression }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let assumptions = search_input.facts().assumptions();
        let mut proof = search_input.clone();
        let mut equalities = Vec::new();
        let mut restated = Vec::new();
        for (term, surface) in operands {
            let simpler = substitute_constant_summands(width, term, &|summand| {
                assumptions
                    .signed_constant_bound_facts(width, summand)
                    .iter()
                    .find_map(|fact| exact_constant_of(width, fact, summand))
            })
            .and_then(|substituted| search_input.synthesize_machine_term_here(&substituted));
            let Some(simpler) = simpler else {
                restated.push(surface.clone());
                continue;
            };
            let equality = ClickProposition::Comparison {
                left: surface.clone(),
                operator: ComparisonOperator::Equal,
                right: simpler.clone(),
            };
            if equalities.contains(&equality) {
                restated.push(simpler);
                continue;
            }
            let Ok(scope) = proof.driver().open_have(equality.clone()) else {
                return Ok(None);
            };
            let Some(scope) = (scope).driver().try_solve_closure()? else {
                return Ok(None);
            };
            proof = scope.join()?;
            equalities.push(equality);
            restated.push(simpler);
        }
        if equalities.is_empty() {
            return Ok(None);
        }
        let [left, right]: [ContractExpression; 2] = restated
            .try_into()
            .expect("one restated spelling per operand");
        let defined = ClickProposition::Defined {
            expression: match expression {
                ContractExpression::Subtract(_, _) => {
                    ContractExpression::Subtract(Box::new(left), Box::new(right))
                }
                _ => ContractExpression::Add(Box::new(left), Box::new(right)),
            },
        };
        let Ok(scope) = proof.driver().open_have(defined) else {
            return Ok(None);
        };
        let Some(scope) = (scope).driver().try_signed_definedness_closure()? else {
            return Ok(None);
        };
        let mut proof = scope.join()?;
        for equality in equalities {
            let Ok(rewritten) = proof.driver().apply_step(ProofStep::Rewrite(equality)) else {
                return Ok(None);
            };
            proof = rewritten;
        }
        if proof.is_complete() {
            return Ok(Some(proof));
        }
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))
    }

    /// `solve() using { .. }` on an `int32` or `int64` definedness goal: cite
    /// exactly the listed premises that bound an operand by a constant.
    pub(in crate::surface::proof) fn try_restricted_signed_definedness_closure(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_signed_definedness_closure");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        use crate::kernel::proof::arithmetic_special::{
            signed_constant_bound_on_view, signed_definedness_query,
        };
        let Some((width, operands, _)) = signed_definedness_query(goal) else {
            return Ok(None);
        };
        let premises = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                signed_constant_bound_on_view(width, kernel, operands[0].operand_view()).is_some()
                    || signed_constant_bound_on_view(width, kernel, operands[1].operand_view())
                        .is_some()
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        Self::try_signed_definedness_certificate(search_input, width, premises)
    }
}
