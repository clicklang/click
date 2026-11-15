//! Search exposes historical endpoint equalities as ordinary, explicit facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Discover already recorded footprint separations only in smart search.
    /// The resulting proof applies explicit preservation at each endpoint;
    /// replay neither enumerates facts nor follows memory history.
    pub(in crate::surface::proof) fn try_recorded_footprint_preservation(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_recorded_footprint_preservation");
        if preservation_read(source, target).is_none() {
            return Ok(None);
        }
        let Some(spellings) = search_input.context_surface_propositions() else {
            return Ok(None);
        };
        let mut premises = Vec::new();
        for fact in search_input.facts().propositions() {
            check_verification_deadline()?;
            crate::instrumentation::record_deterministic_work(1);
            let Proposition::ResourceSeparate { left, .. } = fact else {
                continue;
            };
            if !matches!(left.as_ref(), crate::kernel::Resource::Footprint(_)) {
                continue;
            }
            let premise = spellings.surface(fact)?;
            if preservation_separation_matches(source, target, premise)
                && !premises.contains(premise)
            {
                premises.push(premise.clone());
            }
        }
        let Some(steps) = statement_preservation_steps(source, target, &premises) else {
            return Ok(None);
        };
        attempt::candidate_outcome(
            search_input
                .driver()
                .apply_ordinary_transport_steps(target, steps),
        )
    }

    pub(in crate::surface::proof) fn try_history_indexed_equalities(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_history_indexed_equalities");
        if search_input.surface_goal() != Some(target)
            || old_reflexive_transport_source(target).as_ref() != Some(source)
        {
            return Ok(None);
        }
        let ClickProposition::Comparison {
            left: read,
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Old(old),
        } = target
        else {
            return Ok(None);
        };
        if read != old.as_ref()
            || !matches!(
                contract_expression_as_program_expression(read),
                Some(ProgramExpression::Index(..))
            )
        {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_snapshots;
        let mut proof = search_input.clone();
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let exit = SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: region.clone(),
                kind: ProgramPointKind::Exit,
            });
            if records.get(&exit).is_none() {
                continue;
            }
            let at = |selector| ContractExpression::At {
                selector,
                expression: Box::new(read.clone()),
            };
            let equality = ClickProposition::Comparison {
                left: at(exit),
                operator: ComparisonOperator::Equal,
                right: at(selector.clone()),
            };
            // Expose the selected endpoint terms to ordinary equality reasoning.
            // No premise or memory history is reconstructed during replay.
            let candidate = (|| {
                let scope = proof
                    .driver()
                    .open_have_with_goal_observations(equality, true)?;
                scope.driver().apply_step(ProofStep::Known)?.join()
            })();
            if let Some(unchanged) = attempt::candidate_outcome(candidate)? {
                proof = unchanged;
            }
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }
}
