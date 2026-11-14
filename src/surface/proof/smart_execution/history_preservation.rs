//! Search selects atomic footprints; replay applies ordinary separation laws.
use super::*;
use crate::kernel::PointerOffsetTerm;

fn indexed_cell(base: ProgramExpression, index: ProgramExpression) -> ResourceSubject {
    let address = ProgramExpression::AddressOf(Box::new(ProgramExpression::Index(
        Box::new(base),
        Box::new(index),
    )));
    let zero = ProgramExpression::Value(crate::kernel::int32(0));
    let one = ProgramExpression::Value(crate::kernel::int32(1));
    ResourceSubject::Memory(ContractSegment {
        state: ContractSegmentState::Current,
        base: address.clone(),
        start: zero.clone(),
        end: one.clone(),
        uninitialized: false,
        surface: ContractSegmentSurface::Range {
            base: ContractExpression::ProgramExpression(address),
            start: ContractExpression::ProgramExpression(zero),
            end: ContractExpression::ProgramExpression(one),
        },
    })
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_history_indexed_preservation(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_history_indexed_preservation");
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
            return Ok(None);
        }
        let Some(ProgramExpression::Index(base, index)) =
            contract_expression_as_program_expression(read)
        else {
            return Ok(None);
        };
        let cell = indexed_cell(*base.clone(), *index.clone());
        let base_cell = indexed_cell(
            *base.clone(),
            ProgramExpression::Value(crate::kernel::int32(0)),
        );
        let base_fact = search_input.lower_surface_proposition_direct(
            &ClickProposition::Contains {
                parent: base_cell.clone(),
                child: base_cell,
            },
            "indexed preservation base",
        )?;
        let mut atom = &base_fact;
        while let Proposition::And(left, _) = atom {
            atom = left;
        }
        let Proposition::ResourceContains { parent, .. } = atom else {
            return Ok(None);
        };
        let crate::kernel::Resource::Memory(base_range) = parent.as_ref() else {
            return Ok(None);
        };
        let base_pointer = base_range.base();
        let width = i64::from(base_range.element_width());
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_snapshots;
        let regions = records
            .iter()
            .filter_map(|(selector, state)| {
                let SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: region @ CodeRegionRef::Region(_),
                    kind: ProgramPointKind::Entry,
                }) = selector
                else {
                    return None;
                };
                Some((region.clone(), selector.clone(), state))
            })
            .collect::<Vec<_>>();
        let have =
            |proof: &Proof<'a>, goal, steps: Vec<ProofStep>| -> Result<Proof<'a>, ClickError> {
                let mut scope = proof
                    .driver()
                    .open_have_with_goal_observations(goal, true)?;
                for step in steps {
                    scope = scope.driver().apply_step(step)?;
                }
                scope.join()
            };
        let at =
            |selector: &SnapshotSelector, expression: ContractExpression| ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(expression),
            };
        let mut proof = search_input.clone();
        for (region, selector, before) in regions {
            check_verification_deadline()?;
            let Ok(crate::kernel::Resource::Footprint(footprint)) = records.footprint(&region)
            else {
                continue;
            };
            if !footprint.complete || footprint.members.len() != 1 {
                continue;
            }
            let Some(crate::kernel::Resource::Memory(changed)) = footprint.members.front() else {
                continue;
            };
            let point = |kind| {
                SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: region.clone(),
                    kind,
                })
            };
            let equality = ClickProposition::Comparison {
                left: at(&point(ProgramPointKind::Exit), read.clone()),
                operator: ComparisonOperator::Equal,
                right: at(&point(ProgramPointKind::Entry), read.clone()),
            };
            // Declarations and local bookkeeping can already leave this read
            // unchanged. State that equality directly before planning a write proof.
            if let Some(unchanged) = attempt::candidate_outcome(have(
                &proof,
                equality.clone(),
                vec![ProofStep::Assumption],
            ))? {
                proof = unchanged;
                continue;
            }
            let footprint_separation = ClickProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: cell.clone(),
            };
            let changed_subject =
                super::super::surface_synthesis::synthesize_surface_resource_subject(
                    &crate::kernel::Resource::Memory(changed.clone()),
                    view.parameter_binding,
                    before,
                    &BTreeMap::new(),
                )
                .ok_or_else(|| {
                    proof.step_error(format!(
                        "recorded write resource has no Surface spelling: {region:?}: {changed:?}"
                    ))
                })?;
            let direct_separation = ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(ClickProposition::Separate {
                    left: changed_subject,
                    right: cell.clone(),
                }),
            };
            let mut candidate = if let Some(scope) =
                attempt::candidate_outcome(proof.driver().open_have(direct_separation.clone()))?
                && let Some(closed) = scope.driver().try_solve_closure()?
            {
                Some((closed.join()?, direct_separation))
            } else {
                None
            };
            if candidate.is_none() && changed.base().block == base_pointer.block {
                let delta = if base_pointer.offset == PointerOffsetTerm::Constant(0) {
                    Some(&changed.base().offset)
                } else if let PointerOffsetTerm::Add(parent, delta) = &changed.base().offset {
                    (parent.as_ref() == &base_pointer.offset).then_some(delta.as_ref())
                } else {
                    None
                };
                if let Some(PointerOffsetTerm::Int32Scaled { value, byte_width }) = delta
                    && *byte_width == width
                {
                    let written_index =
                        super::super::surface_synthesis::synthesize_surface_machine_expression(
                            value.structural_value(),
                            view.parameter_binding,
                            before,
                        )
                        .ok_or_else(|| {
                            proof.step_error("recorded write index has no Surface spelling")
                        })?;
                    let Some(index_expression) =
                        contract_expression_as_program_expression(&written_index)
                    else {
                        return Err(proof.step_error("recorded write index is not expressible in its entry resource descriptor"));
                    };
                    let source_index = at(&selector, written_index);
                    let target_index = ContractExpression::ProgramExpression(*index.clone());
                    let distinct = ClickProposition::Comparison {
                        left: source_index.clone(),
                        operator: ComparisonOperator::NotEqual,
                        right: target_index.clone(),
                    };
                    if let Some(scope) =
                        attempt::candidate_outcome(proof.driver().open_have(distinct.clone()))?
                        && let Some(closed) = scope.driver().try_solve_closure()?
                    {
                        let distinct_proof = closed.join()?;
                        let separation = ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(ClickProposition::Separate {
                                left: indexed_cell(*base.clone(), index_expression),
                                right: cell.clone(),
                            }),
                        };
                        let application = ProofStep::ApplyTheoremUsing {
                            application: TheoremApplication {
                                name: "click::separation::elements".into(),
                                arguments: vec![
                                    at(
                                        &selector,
                                        ContractExpression::ProgramExpression(*base.clone()),
                                    ),
                                    source_index,
                                    target_index,
                                ],
                            },
                            premises: vec![distinct],
                        };
                        candidate = have(&distinct_proof, separation.clone(), vec![application])
                            .ok()
                            .map(|p| (p, separation));
                    }
                }
            }
            let Some((separated, premise)) = candidate else {
                continue;
            };
            let Some(separated) = attempt::candidate_outcome(have(
                &separated,
                footprint_separation.clone(),
                vec![ProofStep::NormalizeUsing(vec![premise])],
            ))?
            else {
                continue;
            };
            let result = have(
                &separated,
                equality,
                vec![ProofStep::Preserve(footprint_separation)],
            );
            #[cfg(test)]
            if let Err(ref error) = result {
                eprintln!("INDEXED PRESERVE {region:?}: {}", error.report());
            }
            if let Some(preserved) = attempt::candidate_outcome(result)? {
                proof = preserved;
            }
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Assumption))
    }
}
