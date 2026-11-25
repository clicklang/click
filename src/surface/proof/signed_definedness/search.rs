//! Discovery adapters over the existing persistent proof.
use super::*;
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Prove the exact result bounds through ordinary Integer laws.
    pub(in crate::surface::proof) fn try_signed_definedness_bounds(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        premises: Vec<SurfaceProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_definedness_bounds");
        let Some((left, right)) = search_input.signed_definedness_surface_operands() else {
            return Ok(None);
        };
        let Some(SurfaceProposition::Defined { expression }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let observe = |term: &SurfaceTerm| super::super::wide_arithmetic::to_integer(term);
        let exact = match expression {
            SurfaceTerm::Add(..) => {
                SurfaceTerm::Add(Box::new(observe(left)), Box::new(observe(right)))
            }
            SurfaceTerm::Subtract(..) => {
                SurfaceTerm::Subtract(Box::new(observe(left)), Box::new(observe(right)))
            }
            _ => return Ok(None),
        };
        let (minimum, maximum) = match width {
            SignedDefinedWidth::Int32 => (i64::from(i32::MIN), i64::from(i32::MAX)),
            SignedDefinedWidth::Int64 => (i64::MIN, i64::MAX),
        };
        let le = |a, b| SurfaceProposition::Comparison {
            left: a,
            operator: ComparisonOperator::LessEqual,
            right: b,
        };
        let mut proof = search_input.clone();
        let mut listed = premises;
        // Establish both read operands before deriving bounds: initialized
        // resource reads have explicit domains independent of overflow.
        for operand in [left, right] {
            let domain = SurfaceProposition::Defined {
                expression: operand.clone(),
            };
            let kernel = proof.lower_cited_surface_proposition(&domain, "signed operand domain")?;
            if matches!(kernel, Proposition::MemoryReadDefined { .. }) {
                let Some(next) = Self::prepare_integer_read_domain(&proof, domain.clone())? else {
                    return Ok(None);
                };
                proof = next;
                listed.push(domain);
            }
        }
        for operand in [left, right] {
            for range in [
                le(signed_literal(minimum), observe(operand)),
                le(observe(operand), signed_literal(maximum)),
            ] {
                let Some(next) = Self::ordinary_integer_fact(&proof, range.clone(), &[])? else {
                    return Ok(None);
                };
                proof = next;
                listed.push(range);
            }
        }
        for bound in [
            le(signed_literal(minimum), exact.clone()),
            le(exact, signed_literal(maximum)),
        ] {
            let Some(next) = Self::ordinary_integer_fact(&proof, bound, &listed)? else {
                return Ok(None);
            };
            proof = next;
        }
        let closed = proof.driver().apply_step(ProofStep::Known)?;
        Ok(closed.focused_discharged().then_some(closed))
    }

    /// `solve` on an `int32` or `int64` definedness goal: cite the constant
    /// bounds the context indexes under each operand.
    pub(in crate::surface::proof) fn try_signed_definedness_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_definedness_closure");
        // Unary negation has the same exact domain as subtraction from
        // zero. Retain that ordinary domain proof rather than invoking the
        // signed interval compatibility checker.
        if let Some(SurfaceProposition::Defined {
            expression: SurfaceTerm::Negate(operand),
        }) = search_input.surface_goal()
        {
            let domain = SurfaceProposition::Defined {
                expression: SurfaceTerm::Subtract(Box::new(signed_literal(0)), operand.clone()),
            };
            let scope = search_input.driver().open_have(domain)?;
            if let Some(closed) = scope.driver().try_signed_definedness_closure()? {
                return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
            }
            return Ok(None);
        }
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
        if let Some(closed) = Self::try_signed_definedness_bounds(search_input, width, premises)? {
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
        operands: [(&MachineTerm, &SurfaceTerm); 2],
    ) -> Vec<SurfaceProposition> {
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
    /// which also discharge the read requirements beyond the exact-result
    /// range of the outer operation.
    pub(in crate::surface::proof) fn try_signed_definedness_with_operand_definedness(
        search_input: &Proof<'a>,
        width: SignedDefinedWidth,
        operands: [(&MachineTerm, &SurfaceTerm); 2],
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
            let defined = SurfaceProposition::Defined {
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
        Self::try_signed_definedness_bounds(&proof, width, premises)
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
        operands: [(&MachineTerm, &SurfaceTerm); 2],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_signed_definedness_after_operand_substitution",
        );
        let Some(SurfaceProposition::Defined { expression }) = search_input.surface_goal() else {
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
            let equality = SurfaceProposition::Comparison {
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
        let [left, right]: [SurfaceTerm; 2] = restated
            .try_into()
            .expect("one restated spelling per operand");
        let defined = SurfaceProposition::Defined {
            expression: match expression {
                SurfaceTerm::Subtract(_, _) => {
                    SurfaceTerm::Subtract(Box::new(left), Box::new(right))
                }
                _ => SurfaceTerm::Add(Box::new(left), Box::new(right)),
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

    /// `close() using { .. }` on an `int32` or `int64` definedness goal: cite
    /// exactly the listed premises that bound an operand by a constant.
    pub(in crate::surface::proof) fn try_restricted_signed_definedness_closure(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, SurfaceProposition)],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_signed_definedness_closure");
        // Negation shares subtraction-from-zero's domain. Keep the selected
        // premises when proving that ordinary subtraction domain.
        if let Some(SurfaceProposition::Defined {
            expression: SurfaceTerm::Negate(operand),
        }) = search_input.surface_goal()
        {
            let domain = SurfaceProposition::Defined {
                expression: SurfaceTerm::Subtract(Box::new(signed_literal(0)), operand.clone()),
            };
            let scope = search_input.driver().open_have(domain)?;
            let Some(closed) = scope
                .driver()
                .try_restricted_signed_definedness_closure(premise_pairs)?
            else {
                return Ok(None);
            };
            return Ok(Some(closed.join()?.driver().apply_step(ProofStep::Known)?));
        }
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if matches!(search_input.context.as_ref(), ProofContext::Pure(_))
            && let Some(tactics) = plan_int32_increment_definedness_theorem(goal, premise_pairs)
            && let Some(closed) = attempt::candidate_outcome(
                search_input.driver().try_generated_linear_script(&tactics),
            )?
            .flatten()
        {
            return Ok(Some(closed));
        }
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
        Self::try_signed_definedness_bounds(search_input, width, premises)
    }
}
