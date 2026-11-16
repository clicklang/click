//! Explicit logical proofs used to publish selected solver premises.
use super::*;

fn disjunction_proof(
    proof: &Proof<'_>,
    source: &Proposition,
) -> Result<(ClickProposition, Vec<ProofTactic>), ClickError> {
    if let Proposition::Or(left, right) = source {
        let (left, left_body) = disjunction_proof(proof, left)?;
        let (right, right_body) = disjunction_proof(proof, right)?;
        let surface = ClickProposition::Or(Box::new(left), Box::new(right));
        let body = vec![ProofTactic::Cases(ProofCases::from_binary(
            &surface, left_body, right_body,
        ))];
        return Ok((surface, body));
    }
    let surface = proof.spelled_goal_for_search(source).ok_or_else(|| {
        proof.step_error("selected disjunction leaf has no retained Surface spelling")
    })?;
    let opposite = match source {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(inner) => inner.as_ref().clone(),
        other => Proposition::Not(Box::new(other.clone())),
    };
    // Each leaf is assumed by its case arm. Cite that assumption when an
    // exact opposite is already held, rather than asking `known` to derive
    // a conclusion from an inconsistent branch.
    let body = if proof.facts().holds_contradiction_fact(&opposite) {
        vec![ProofTactic::Contradiction(surface.clone())]
    } else {
        vec![ProofTactic::Known]
    };
    Ok((surface, body))
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Establish one selected fact through ordinary explicit proof syntax.
    /// A failed candidate leaves the immutable input untouched. There is no
    /// recursive solve call: each candidate is known, one implication
    /// application, or cases with known/contradiction leaves, under the current work budget.
    pub(in crate::surface::proof) fn publish_selected_fact(
        search_input: &Proof<'a>,
        surface: &ClickProposition,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("publish_selected_fact");
        let publish = |body: Vec<ProofTactic>| -> Result<Option<Proof<'a>>, ClickError> {
            let Some(scope) =
                attempt::candidate_outcome(search_input.driver().open_have(surface.clone()))?
            else {
                return Ok(None);
            };
            let closed = if matches!(body.as_slice(), [ProofTactic::Known]) {
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            } else {
                attempt::candidate_outcome(scope.driver().try_authoritative_linear_script(&body))?
                    .flatten()
            };
            let Some(closed) = closed else {
                return Ok(None);
            };
            let Some(added) = attempt::candidate_outcome(closed.join())? else {
                return Ok(None);
            };
            // Extraction also closed a goal established by the selected fact.
            // Retain an ordinary explicit closer for that case.
            if (added
                .goal()
                .is_some_and(|goal| added.facts().contains(goal))
                || added.surface_goal() == Some(surface))
                && let Some(closed) =
                    attempt::candidate_outcome(added.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
            Ok(Some(added))
        };
        if let Some(proof) = publish(vec![ProofTactic::Known])? {
            return Ok(proof);
        }
        // Excluded middle needs no disjunction premise. An ordinary `if`
        // proves it from its two checked assumptions, whereas `cases`
        // requires the disjunction to have been established already.
        if let Some((left, _)) = crate::surface::split_case_disjunction(surface)
            && let Some(proof) = publish(vec![ProofTactic::If(ProofIf {
                condition: left,
                ensuring: None,
                then_tactics: vec![ProofTactic::Known],
                else_tactics: vec![ProofTactic::Known],
            })])?
        {
            return Ok(proof);
        }
        let goal = search_input.lower_cited_surface_proposition(surface, "selected fact")?;
        for source in crate::kernel::search::implication_candidates(search_input.facts(), &goal) {
            check_verification_deadline()?;
            let fact = search_input
                .spelled_goal_for_search(&source)
                .ok_or_else(|| {
                    search_input.step_error("selected implication has no retained Surface spelling")
                })?;
            let (premises, _) = crate::surface::proof::driver::fact_application_parts(&fact);
            let application = ProofTactic::ApplyFactUsing { fact, premises };
            if let Some(proof) = publish(vec![application.clone(), ProofTactic::Known])? {
                return Ok(proof);
            }
            // A partial implication conclusion is proved by introducing its
            // remaining antecedents before applying the complete source chain.
            let (remaining, _) = crate::surface::proof::driver::fact_application_parts(surface);
            if !remaining.is_empty() {
                let mut body = vec![ProofTactic::Intro; remaining.len()];
                body.extend([application, ProofTactic::Known]);
                if let Some(proof) = publish(body)? {
                    return Ok(proof);
                }
            }
        }
        for source in crate::kernel::search::connected_disjunction_candidates(
            search_input.facts().assumptions(),
            &goal,
        ) {
            check_verification_deadline()?;
            let (_, body) = disjunction_proof(search_input, &source)?;
            if let Some(proof) = publish(body)? {
                return Ok(proof);
            }
        }
        Err(search_input.step_error(format!(
            "could not establish selected fact with known, implication application, or cases: {}",
            crate::surface::printing::source_click_proposition(surface),
        )))
    }
}
