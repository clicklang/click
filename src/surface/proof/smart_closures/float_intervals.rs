//! Ordinary proofs of products and quotients from selected floating-point bounds.
use super::super::surface_certificates::surface_strict_parts;
use super::*;
use crate::kernel::proof::arithmetic_special::{
    FloatBoundWeakening, float_corner_bound_weakening, float_positive_product_bound,
};
use crate::kernel::{FloatBinaryOperator, KernelFloatType};

fn literal(format: KernelFloatType, bits: u64) -> ContractExpression {
    ContractExpression::ProgramExpression(match format {
        KernelFloatType::Float32 => crate::kernel::program_expression::float32_literal(bits as u32),
        KernelFloatType::Float64 => crate::kernel::program_expression::float64_literal(bits),
    })
}

fn finite(expression: &ContractExpression) -> ClickProposition {
    ClickProposition::FloatClassification {
        expression: expression.clone(),
        classification: syntax::CFloatClassification::Finite,
    }
}

fn less(left: ContractExpression, right: ContractExpression) -> ClickProposition {
    ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::LessThan,
        right,
    }
}

fn corner_order(
    operator: FloatBinaryOperator,
    plan: &FloatBoundWeakening,
    left: &ContractExpression,
    right: &ContractExpression,
) -> ClickProposition {
    let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
    let corner = match operator {
        FloatBinaryOperator::Multiply => ContractExpression::Multiply(left, right),
        FloatBinaryOperator::Divide => ContractExpression::Divide(left, right),
        _ => unreachable!("finite product or quotient"),
    };
    let bound = literal(plan.format, plan.actual_endpoint);
    let (left, right) = if plan.lower {
        (bound, corner)
    } else {
        (corner, bound)
    };
    ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::LessEqual,
        right,
    }
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    fn resolve_float_interval_bound(
        input: &Proof<'a>,
        bound: &Proposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<(ClickProposition, (ContractExpression, ContractExpression))> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_float_interval_bound");
        let surface = Self::resolve_solve_premises_unmeasured(
            input,
            std::slice::from_ref(bound),
            introduced_surfaces,
        )
        .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
        .or_else(|| input.structural_proposition_candidate(bound))?;
        let parts = surface_nonstrict_parts(&surface_comparison_with_anchored_operands(&surface))?;
        Some((surface, parts))
    }

    fn try_apply_float_interval_bound(
        input: &Proof<'a>,
        plan: &FloatBoundWeakening,
        name: &str,
        arguments: Vec<ContractExpression>,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_apply_float_interval_bound");
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: format!("click::float_order::{name}"),
                arguments,
            },
            premises,
        };
        let Some(proof) = attempt::candidate_outcome(input.driver().apply_step(
            super::super::wide_arithmetic::have(intermediate.clone(), vec![application]),
        ))?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, plan, intermediate)
    }

    pub(in crate::surface::proof) fn try_positive_float_product_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 2],
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_positive_float_product_bound");
        let Some(plan) = float_positive_product_bound(goal, bounds) else {
            return Ok(None);
        };
        let [Some((first, (a, x))), Some((second, (b, y)))] = bounds
            .each_ref()
            .map(|bound| Self::resolve_float_interval_bound(input, bound, introduced_surfaces))
        else {
            return Ok(None);
        };
        let zero = literal(plan.format, 0);
        let premises = vec![
            first,
            second,
            finite(&a),
            finite(&b),
            less(zero.clone(), a.clone()),
            less(zero, b.clone()),
        ];
        let name = match plan.format {
            KernelFloatType::Float32 => "float32_positive_product_lower",
            KernelFloatType::Float64 => "float64_positive_product_lower",
        };
        Self::try_apply_float_interval_bound(input, &plan, name, vec![x, y, a, b], premises)
    }

    pub(in crate::surface::proof) fn try_float_corner_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 4],
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_corner_bound");
        let Some((plan, operator)) = float_corner_bound_weakening(goal, bounds) else {
            return Ok(None);
        };
        let [
            Some((first, (a, x))),
            Some((second, (b, y))),
            Some((third, (_, c))),
            Some((fourth, (_, d))),
        ] = bounds
            .each_ref()
            .map(|bound| Self::resolve_float_interval_bound(input, bound, introduced_surfaces))
        else {
            return Ok(None);
        };
        let mut premises = vec![
            first,
            second,
            third,
            fourth,
            finite(&a),
            finite(&b),
            finite(&c),
            finite(&d),
        ];
        use FloatBinaryOperator::{Divide, Multiply};
        let advanced = if operator == Divide {
            let zero = literal(plan.format, 0);
            let sign = ClickProposition::Or(
                Box::new(less(zero.clone(), b.clone())),
                Box::new(less(d.clone(), zero)),
            );
            // Selected applications cite the disjunction itself. Retain it
            // even when the two literal comparisons decide its truth.
            let Some(proof) = attempt::candidate_outcome(input.driver().apply_step(
                super::super::wide_arithmetic::have(sign.clone(), vec![ProofStep::Known]),
            ))?
            else {
                return Ok(None);
            };
            premises.push(sign);
            Some(proof)
        } else {
            None
        };
        for (left, right) in [(&a, &b), (&a, &d), (&c, &b), (&c, &d)] {
            premises.push(corner_order(operator, &plan, left, right));
        }
        let name = match (operator, plan.format, plan.lower) {
            (Multiply, KernelFloatType::Float32, true) => "float32_product_lower",
            (Multiply, KernelFloatType::Float32, false) => "float32_product_upper",
            (Multiply, KernelFloatType::Float64, true) => "float64_product_lower",
            (Multiply, KernelFloatType::Float64, false) => "float64_product_upper",
            (Divide, KernelFloatType::Float32, true) => "float32_quotient_lower",
            (Divide, KernelFloatType::Float32, false) => "float32_quotient_upper",
            (Divide, KernelFloatType::Float64, true) => "float64_quotient_lower",
            (Divide, KernelFloatType::Float64, false) => "float64_quotient_upper",
            _ => unreachable!("finite product or quotient"),
        };
        let bound = literal(plan.format, plan.actual_endpoint);
        Self::try_apply_float_interval_bound(
            advanced.as_ref().unwrap_or(input),
            &plan,
            name,
            vec![x, y, a, b, c, d, bound],
            premises,
        )
    }

    pub(in crate::surface::proof) fn try_float_reciprocal_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_reciprocal_bound");
        use crate::kernel::proof::arithmetic_special::float_reciprocal_bound_weakening;
        let Some((plan, numerator, strict)) = float_reciprocal_bound_weakening(source, goal) else {
            return Ok(None);
        };
        let comparison = surface_comparison_with_anchored_operands(source_surface);
        let parts = if strict {
            surface_strict_parts(&comparison)
        } else {
            surface_nonstrict_parts(&comparison)
        };
        let Some((bound, divisor)) = parts else {
            return Ok(None);
        };
        let float = match plan.format {
            KernelFloatType::Float32 => "float32",
            KernelFloatType::Float64 => "float64",
        };
        let mut proof = input.clone();
        let premise = if strict {
            let nonstrict = ClickProposition::Comparison {
                left: bound.clone(),
                operator: ComparisonOperator::LessEqual,
                right: divisor.clone(),
            };
            let application = ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: format!("click::float_order::{float}_lt_to_le"),
                    arguments: vec![bound.clone(), divisor.clone()],
                },
                premises: vec![source_surface.clone()],
            };
            let Some(next) = attempt::candidate_outcome(proof.driver().apply_step(
                super::super::wide_arithmetic::have(nonstrict.clone(), vec![application]),
            ))?
            else {
                return Ok(None);
            };
            proof = next;
            nonstrict
        } else {
            source_surface.clone()
        };
        let numerator = literal(plan.format, numerator);
        let zero = literal(plan.format, 0);
        let premises = vec![
            finite(&numerator),
            less(zero.clone(), numerator.clone()),
            less(zero, bound.clone()),
            premise,
        ];
        let direction = if plan.lower { "lower" } else { "upper" };
        Self::try_apply_float_interval_bound(
            &proof,
            &plan,
            &format!("{float}_reciprocal_{direction}"),
            vec![numerator, divisor, bound],
            premises,
        )
    }
}
