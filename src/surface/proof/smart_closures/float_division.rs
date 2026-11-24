//! Ordinary proofs of selected positive reciprocal bounds.
use super::super::surface_certificates::surface_strict_parts;
use super::*;
use crate::kernel::KernelFloatType;

fn literal(format: KernelFloatType, bits: u64) -> ContractExpression {
    use crate::kernel::program_expression::{float32_literal, float64_literal};
    ContractExpression::ProgramExpression(match format {
        KernelFloatType::Float32 => float32_literal(bits as u32),
        KernelFloatType::Float64 => float64_literal(bits),
    })
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
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
        let Some(intermediate) = proof.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let numerator = literal(plan.format, numerator);
        let positive = |right| ClickProposition::Comparison {
            left: literal(plan.format, 0),
            operator: ComparisonOperator::LessThan,
            right,
        };
        let finite = ClickProposition::FloatClassification {
            expression: numerator.clone(),
            classification: syntax::CFloatClassification::Finite,
        };
        let direction = if plan.lower { "lower" } else { "upper" };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: format!("click::float_order::{float}_reciprocal_{direction}"),
                arguments: vec![numerator.clone(), divisor, bound.clone()],
            },
            premises: vec![finite, positive(numerator), positive(bound), premise],
        };
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            super::super::wide_arithmetic::have(intermediate.clone(), vec![application]),
        ))?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, &plan, intermediate)
    }
}
