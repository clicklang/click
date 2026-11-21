//! Search exposes historical endpoint equalities as ordinary, explicit facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Name the individual effects that a selected indexed read survived.
    /// Every proposed footprint separation and preservation is checked in
    /// an ordinary have. The final equality checks the goal's actual points.
    pub(in crate::surface::proof) fn try_indexed_read_preservation(
        search_input: &Proof<'a>,
        point_limit: usize,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_read_preservation");
        let Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        }) = search_input.surface_goal()
        else {
            return Ok(None);
        };
        let current = match (left, right) {
            (
                current,
                ContractExpression::Old(saved)
                | ContractExpression::At {
                    expression: saved, ..
                },
            )
            | (
                ContractExpression::Old(saved)
                | ContractExpression::At {
                    expression: saved, ..
                },
                current,
            ) if current == saved.as_ref() => current,
            _ => return Ok(None),
        };
        let Some(ProgramExpression::Index(base, index)) =
            contract_expression_as_program_expression(current)
        else {
            return Ok(None);
        };
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let kept = ResourceSubject::SavedMemory {
            base: ContractExpression::ProgramExpression(*base),
            start: ContractExpression::ProgramExpression(*index),
            end: None,
        };
        let have = |proposition, step| ProofStep::Have {
            proposition,
            proof: Box::new(
                ProofCertificate::from_steps(vec![step]).expect("an ordinary preservation step"),
            ),
        };
        let mut proof = search_input.clone();
        for (selector, _) in records.recent(point_limit) {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ (CodeRegionRef::Region(_) | CodeRegionRef::Path(_)),
                kind: ProgramPointKind::Exit,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(footprint)) = records.footprint(region) else {
                continue;
            };
            if !footprint.complete || footprint.members.is_empty() {
                continue;
            }
            let separation = ClickProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: kept.clone(),
            };
            let at = |kind| ContractExpression::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: region.clone(),
                    kind,
                }),
                expression: Box::new(current.clone()),
            };
            let equality = ClickProposition::Comparison {
                left: at(ProgramPointKind::Exit),
                operator: ComparisonOperator::Equal,
                right: at(ProgramPointKind::Entry),
            };
            let candidate = (|| {
                let separated = proof
                    .driver()
                    .apply_step(have(separation.clone(), ProofStep::Known))?;
                separated
                    .driver()
                    .apply_step(have(equality, ProofStep::Preserve(separation)))
            })();
            if let Some(preserved) = attempt::candidate_outcome(candidate)? {
                if preserved.focused_discharged() {
                    return Ok(Some(preserved));
                }
                if let Some(closed) =
                    attempt::candidate_outcome(preserved.driver().apply_step(ProofStep::Known))?
                {
                    return Ok(Some(closed));
                }
                proof = preserved;
            }
        }
        Ok(None)
    }

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
        if read != old.as_ref() {
            return if crate::surface::proposition_names_result(target) {
                Self::try_returned_index_preservation(search_input, target, old)
            } else {
                Ok(None)
            };
        }
        if !matches!(
            contract_expression_as_program_expression(read),
            Some(ProgramExpression::Index(..))
        ) {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let mut proof = search_input.clone();
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let exit = ProgramPointSelector::ProgramPoint(ProgramPointRef {
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

    /// Choose a recorded write and a stated separation for a returned indexed
    /// read. The selected write is checked again through its named footprint;
    /// the final `known` checks that this equality actually closes the result.
    fn try_returned_index_preservation(
        search_input: &Proof<'a>,
        target: &ClickProposition,
        read: &ContractExpression,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_returned_index_preservation");
        let Some(ProgramExpression::Index(base, index)) =
            contract_expression_as_program_expression(read)
        else {
            return Ok(None);
        };
        let kept = ResourceSubject::SavedMemory {
            base: ContractExpression::ProgramExpression(*base),
            start: ContractExpression::ProgramExpression(*index),
            end: None,
        };
        let (Some(view), Some(spellings)) = (
            search_input.premise_fixed_state_view(),
            search_input.context_surface_propositions(),
        ) else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let have = |proposition, step| ProofStep::Have {
            proposition,
            proof: Box::new(
                ProofCertificate::from_steps(vec![step]).expect("an ordinary preservation step"),
            ),
        };
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(recorded)) = records.footprint(region) else {
                continue;
            };
            let Some(written @ Resource::Memory(written_range)) = recorded.members.front() else {
                continue;
            };
            if !recorded.complete || recorded.members.len() != 1 {
                continue;
            }
            let footprint = ClickProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: kept.clone(),
            };
            let Some(lowered) = attempt::candidate_outcome(
                search_input.lower_surface_proposition_direct(&footprint, "preserved cell"),
            )?
            else {
                continue;
            };
            let mut split = &lowered;
            while let Proposition::And(stated, _) = split {
                split = stated;
            }
            let Proposition::ResourceSeparate { right, .. } = split else {
                continue;
            };
            let Some(candidates) = search_input
                .facts()
                .assumptions()
                .resource_separation_candidates(written, right)
            else {
                continue;
            };
            for candidate in candidates {
                check_verification_deadline()?;
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::ResourceSeparate { left, right } = candidate else {
                    continue;
                };
                let Some(mut surface) = spellings.recorded_requirement_surface(candidate) else {
                    continue;
                };
                while let ClickProposition::At { proposition, .. } = surface {
                    surface = proposition;
                }
                let ClickProposition::Separate {
                    left: left_surface,
                    right: right_surface,
                } = surface
                else {
                    continue;
                };
                let same_storage = |resource: &Resource| {
                    matches!(resource, Resource::Memory(range)
                        if range.base().base == written_range.base().base)
                };
                let covering = if same_storage(left) {
                    left_surface
                } else if same_storage(right) {
                    right_surface
                } else {
                    continue;
                };
                let separation = ClickProposition::Separate {
                    left: covering.clone(),
                    right: kept.clone(),
                };
                let at = |kind| ContractExpression::At {
                    selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: region.clone(),
                        kind,
                    }),
                    expression: Box::new(read.clone()),
                };
                let equality = ClickProposition::Comparison {
                    left: at(ProgramPointKind::Exit),
                    operator: ComparisonOperator::Equal,
                    right: at(ProgramPointKind::Entry),
                };
                let steps = vec![
                    have(separation.clone(), ProofStep::Known),
                    have(
                        footprint.clone(),
                        ProofStep::NormalizeUsing(vec![separation]),
                    ),
                    have(equality, ProofStep::Preserve(footprint.clone())),
                    ProofStep::Known,
                ];
                if let Some(proof) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_ordinary_transport_steps(target, steps),
                )? {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }
}
