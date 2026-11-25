//! Logical/execution/outcome splits, joins, and `have`/`with` scopes.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{
    constant_u64, int32_constant, int64_constant, uint32_constant, uint64_constant,
};

pub(in crate::surface::proof) struct CheckedBothSurfaceChild {
    surface: Option<SyntaxProposition>,
    introductions: Option<crate::kernel::LoweringIntroductions>,
}

impl<'a> Proof<'a> {
    fn recorded_surface_matches(&self, surface: &SyntaxProposition, target: &Proposition) -> bool {
        let matches = |map: &SurfacePropositionMap| {
            map.available_kernel_matching(surface, |kernel| {
                crate::kernel::proof::propositions_are_alpha_equal(kernel, target)
            })
            .is_some()
        };
        match self.context.as_ref() {
            ProofContext::Pure(context) => matches(&context.theorem_context.surface_requirements),
            ProofContext::FixedState(context) => matches(context.surface_propositions),
            ProofContext::Execution(_) => self
                .execution()
                .is_some_and(|execution| matches(&execution.presentation.surface_propositions)),
        }
    }

    /// Recovers a written body when the kernel obligation has a checked
    /// lowering guard in front of it. The generated display can re-lower a
    /// state expression at the current state, so its wrapper's consequent
    /// is not itself evidence. The obligation's recorded head chain proves
    /// the wrapper, while invariant-body assembly supplies the one declared
    /// Surface body whose lowering is exactly the guarded consequent.
    fn recorded_guard_surface_child(
        &self,
        surface: &SyntaxProposition,
        target: &Proposition,
        recorded: &BothChildPresentation,
    ) -> Option<CheckedBothSurfaceChild> {
        if !crate::kernel::proof::propositions_are_alpha_equal(&recorded.kernel, target) {
            return None;
        }
        let mut cursor = target;
        let mut antecedent = None;
        for introduction in recorded.introductions.iter() {
            match introduction {
                crate::kernel::LoweringIntroduction::PathFactGuard
                | crate::kernel::LoweringIntroduction::ObligationGuard => {
                    let Proposition::Implies(left, body) = cursor else {
                        return None;
                    };
                    antecedent.get_or_insert(left.as_ref());
                    cursor = body;
                }
                // This adapter is specifically for a lowering-inserted
                // wrapper. A written connective must be handled by the
                // ordinary Surface structural presentation instead.
                crate::kernel::LoweringIntroduction::WrittenImplication
                | crate::kernel::LoweringIntroduction::WrittenNegation
                | crate::kernel::LoweringIntroduction::ComparisonNegation
                | crate::kernel::LoweringIntroduction::WrittenUniversal { .. } => return None,
            }
        }
        let antecedent = antecedent?;

        match surface {
            SyntaxProposition::Implies(surface_antecedent, _) => {
                let lowered = self
                    .lower_surface_proposition(surface_antecedent, "`all` guard antecedent")
                    .ok()?;
                if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, antecedent) {
                    return None;
                }
            }
            _ => {
                let lowered = self
                    .lower_surface_proposition(surface, "`all` guarded body")
                    .ok()?;
                if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, cursor) {
                    return None;
                }
            }
        }

        let candidate = recorded.surface.as_ref()?.clone();
        let lowered = self
            .lower_surface_proposition(&candidate, "`all` recorded guarded body")
            .ok()?;
        if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, cursor) {
            return None;
        }
        Some(CheckedBothSurfaceChild {
            surface: Some(candidate),
            introductions: Some(recorded.introductions.iter().cloned().collect()),
        })
    }

    /// The children of a split with no usable whole source form. A loop
    /// bundle whose whole form could not be synthesized, or was synthesized
    /// at the wrong state, such as one with a member at the loop entry
    /// beside members at the iteration entry, still has one for each member
    /// alone; the smart closer attaches the same form to each leaf it
    /// closes. Only a member is spelled: a conjunction child is split
    /// again, so spelling it here would synthesize the rest of the bundle
    /// once per member. Anything else keeps its children unspelled.
    fn bundle_member_surface_children(&self) -> [CheckedBothSurfaceChild; 2] {
        // A loop bundle member keeps its synthesized form. Any other child,
        // such as a conjunct of `defined(p->f + 1)` (the read's definedness
        // and the sum's bounds), raises canonically: a child without a
        // Surface goal cannot be searched as a goal of its own.
        let child = |kernel: Option<&Proposition>| CheckedBothSurfaceChild {
            surface: kernel.and_then(|kernel| {
                (!matches!(kernel, Proposition::And(..)))
                    .then(|| self.synthesized_bundle_member_surface(kernel))
                    .flatten()
                    .or_else(|| self.conjunct_goal_spelling(kernel))
            }),
            introductions: None,
        };
        match self.goal() {
            Some(Proposition::And(left, right)) => [child(Some(left)), child(Some(right))],
            _ => [child(None), child(None)],
        }
    }

    /// Whether the focused goal is a loop bundle, whose source form, if any,
    /// was synthesized by the closer rather than written.
    fn goal_is_synthesized_bundle(&self) -> bool {
        self.execution_context()
            .is_some_and(|context| context.constants.invariant_body_context.is_some())
    }

    /// Computes the Surface spellings that may travel across a checked
    /// `both` split.  Lowering can insert a conjunct (notably an existential
    /// witness guard), so the written proposition is not necessarily shaped
    /// like the kernel conjunction.  A child is retained only when its
    /// candidate lowers alpha-equivalently to that actual kernel child.
    ///
    /// This is deliberately output-sized: there are at most two candidates
    /// and two kernel children.  It never searches ambient facts or treats a
    /// conjunct as a guard merely because it looks like one.
    pub(in crate::surface::proof) fn checked_both_surface_children(
        &self,
    ) -> Result<[CheckedBothSurfaceChild; 2], ClickError> {
        let Some(surface) = self.surface_goal() else {
            return Ok(self.bundle_member_surface_children());
        };
        let goal = self.goal();
        let sequence = goal.and_then(crate::kernel::retained_sequence_equality_view);
        let Some(Proposition::And(left, right)) = sequence.as_ref().or(goal) else {
            return Err(
                self.step_error("`all` presentation correspondence requires a kernel conjunction")
            );
        };
        if matches!(surface, SyntaxProposition::Defined { .. }) {
            // `defined` names this entire ordinary domain. Its children are
            // the kernel conjunction's propositions, not source operands.
            return Ok(self.bundle_member_surface_children());
        }
        let witness_refinement_kernel = self
            .proposition_obligation()
            .and_then(|goal| goal.presentation.witness_refinement_kernel.as_ref());
        let kernel_children = [left.as_ref(), right.as_ref()];
        if let Some((surface_left, surface_right)) = surface_logical_children(surface, true) {
            // A written conjunction has ordered Surface children.  Preserve
            // that order even when the children are alpha-equal (and reject
            // a reversal), rather than treating it as an unordered match.
            let mut children = [None, None];
            let mut lowered_children = [None, None];
            for (index, candidate) in [&surface_left, &surface_right].into_iter().enumerate() {
                let Ok(lowered) =
                    self.lower_surface_proposition(candidate, "`all` presentation child")
                else {
                    continue;
                };
                lowered_children[index] = Some(lowered.clone());
                if !crate::kernel::proof::propositions_are_alpha_equal(
                    &lowered,
                    kernel_children[index],
                ) {
                    continue;
                }
                children[index] = Some(candidate.clone());
            }
            if children.iter().all(Option::is_some) {
                return Ok(children.map(|surface| CheckedBothSurfaceChild {
                    surface,
                    introductions: None,
                }));
            }
            // A fully lowerable reversal is a definite correspondence error;
            // do not let a set-like fallback silently swap written children.
            if lowered_children.iter().all(Option::is_some)
                && crate::kernel::proof::propositions_are_alpha_equal(
                    lowered_children[0].as_ref().unwrap(),
                    kernel_children[1],
                )
                && crate::kernel::proof::propositions_are_alpha_equal(
                    lowered_children[1].as_ref().unwrap(),
                    kernel_children[0],
                )
            {
                return Err(self.step_error(
                    "`all` cannot preserve its written conjunction: child order does not match",
                ));
            }
            if let Some(records) = self
                .proposition_obligation()
                .and_then(|goal| goal.presentation.both_children.as_deref())
            {
                let mut checked = [
                    children[0].clone().map(|surface| CheckedBothSurfaceChild {
                        surface: Some(surface),
                        introductions: None,
                    }),
                    children[1].clone().map(|surface| CheckedBothSurfaceChild {
                        surface: Some(surface),
                        introductions: None,
                    }),
                ];
                for index in 0..2 {
                    if checked[index].is_none() {
                        let surface_child = if index == 0 {
                            &surface_left
                        } else {
                            &surface_right
                        };
                        checked[index] = self.recorded_guard_surface_child(
                            surface_child,
                            kernel_children[index],
                            &records[index],
                        );
                    }
                }
                if checked.iter().all(|child| child.is_some()) {
                    return Ok(checked.map(Option::unwrap));
                }
            }
            if let Ok(children) = self.checked_whole_surface_child(surface, kernel_children) {
                return Ok(children.map(|surface| CheckedBothSurfaceChild {
                    surface,
                    introductions: None,
                }));
            }
            if witness_refinement_kernel.is_some_and(|recorded| {
                crate::kernel::proof::propositions_are_alpha_equal(
                    recorded,
                    &Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    ),
                )
            }) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            // Refinement obligations are assembled by the kernel producer.
            // A generated child can lower to a reduced form (for example a
            // reflexive address comparison becomes true). Keep matching
            // spellings and let unspelled children retain their kernel goals.
            if self
                .proposition_obligation()
                .is_some_and(|goal| goal.generated_surface)
            {
                return Ok(children.map(|surface| CheckedBothSurfaceChild {
                    surface,
                    introductions: None,
                }));
            }
            // A synthesized bundle form that does not mean the goal is a
            // spelling miss, not a written claim; spell the members alone.
            if self.goal_is_synthesized_bundle() {
                return Ok(self.bundle_member_surface_children());
            }
            // The refusal is right whenever it fires: the text does not mean
            // the goal. What it must say is which text, since a smart closer
            // renders a bundle the user never wrote, and where the text and
            // the goal part, since a wrong rendering and a comparison that
            // misses are repaired in different places.
            let rendered = crate::surface::printing::source_click_proposition(surface);
            let mismatch = (0..2)
                .filter(|index| children[*index].is_none())
                .map(|index| {
                    let side = if index == 0 { "left" } else { "right" };
                    match &lowered_children[index] {
                        Some(lowered) => format!(
                            "its {side} conjunct lowers to `{}` but the goal's is `{}`",
                            self.render_diagnostic_proposition(lowered),
                            self.render_diagnostic_proposition(kernel_children[index])
                        ),
                        None => format!("its {side} conjunct does not lower here"),
                    }
                })
                .collect::<Vec<_>>()
                .join("; ");
            return Err(self.step_error(format!(
                "`all` cannot split this goal: its source form, `{rendered}`, does not lower back to it; {mismatch}"
            )));
        }

        // A non-conjunct written body can be the semantic child of a
        // lowering-inserted guard.  It must match exactly one child: duplicate
        // kernel children are intentionally rejected as ambiguous.
        let Ok(lowered) = self.lower_surface_proposition(surface, "`all` presentation child")
        else {
            let parent = Proposition::And(
                Box::new(kernel_children[0].clone()),
                Box::new(kernel_children[1].clone()),
            );
            if self.recorded_surface_matches(surface, &parent) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            if witness_refinement_kernel.is_some_and(|recorded| {
                crate::kernel::proof::propositions_are_alpha_equal(
                    recorded,
                    &Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    ),
                )
            }) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            return Err(self.step_error(
                "`all` cannot preserve its written goal: the candidate did not lower",
            ));
        };
        let matches = kernel_children
            .iter()
            .enumerate()
            .filter(|(_, child)| {
                crate::kernel::proof::propositions_are_alpha_equal(&lowered, child)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            if crate::kernel::proof::propositions_are_alpha_equal(
                &lowered,
                &Proposition::And(
                    Box::new(kernel_children[0].clone()),
                    Box::new(kernel_children[1].clone()),
                ),
            ) {
                // The written proposition accounts for the complete
                // conjunction, not either child.  The checked split still
                // proves both kernel obligations; no child spelling can be
                // installed without changing the written claim.
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            if witness_refinement_kernel.is_some_and(|recorded| {
                crate::kernel::proof::propositions_are_alpha_equal(
                    recorded,
                    &Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    ),
                )
            }) {
                // Substituting a witness can simplify arithmetic guards in
                // the surface spelling without changing the recorded kernel
                // goal. Keep that checked goal and omit a misleading child
                // spelling, just as when re-lowering the body fails above.
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            return Err(self.step_error(
                "`all` cannot preserve its written goal: the kernel child correspondence is ambiguous",
            ));
        }
        let mut children = [
            CheckedBothSurfaceChild {
                surface: None,
                introductions: None,
            },
            CheckedBothSurfaceChild {
                surface: None,
                introductions: None,
            },
        ];
        children[matches[0]].surface = Some(surface.clone());
        Ok(children)
    }

    pub(in crate::surface::proof) fn has_conjunctive_goal(&self) -> bool {
        self.goal().is_some_and(|goal| {
            matches!(goal, Proposition::And(..))
                || matches!(
                    crate::kernel::retained_sequence_equality_view(goal),
                    Some(Proposition::And(..))
                )
        })
    }

    fn checked_whole_surface_child(
        &self,
        surface: &SyntaxProposition,
        kernel_children: [&Proposition; 2],
    ) -> Result<[Option<SyntaxProposition>; 2], ClickError> {
        let lowered =
            match self.lower_surface_proposition(surface, "`all` presentation conjunction") {
                Ok(lowered) => lowered,
                Err(_) => {
                    let parent = Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    );
                    if self.recorded_surface_matches(surface, &parent) {
                        return Ok([None, None]);
                    }
                    return Err(self.step_error(format!(
                        "`all` cannot split this goal: its source form, `{}`, does not lower here",
                        crate::surface::printing::source_click_proposition(surface)
                    )));
                }
            };
        let matches = kernel_children
            .iter()
            .enumerate()
            .filter(|(_, child)| {
                crate::kernel::proof::propositions_are_alpha_equal(&lowered, child)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(self.step_error(
                "`all` cannot preserve its written conjunction: child order does not match",
            ));
        }
        let mut children = [None, None];
        children[matches[0]] = Some(surface.clone());
        Ok(children)
    }

    pub(in crate::surface::proof) fn split_focused_both(
        &self,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let surface_children = self.checked_both_surface_children()?;
        let (state, split, ids) = self
            .state
            .split_proposition_both(|parent, left| {
                let mut child = parent.clone();
                let selected = &surface_children[usize::from(!left)];
                child.surface = selected.surface.clone().map(Arc::new);
                child.introductions = selected
                    .introductions
                    .clone()
                    .map_or_else(GoalIntroductions::default, GoalIntroductions::recorded);
                child.both_children = None;
                child
            })
            .map_err(|message| self.step_error(message))?
            .into_parts();
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
        };
        successor.record_trace_split(
            &successor.node,
            ids,
            &[Vec::new(), Vec::new()],
            "all",
            ["left", "right"],
        );
        Ok((successor, split, ids))
    }

    pub(in crate::surface::proof) fn conjunction_checkpoint(
        &self,
        ids: [BranchId; 2],
    ) -> Result<ProofCheckpoint<'a>, ClickError> {
        let mut marker = self.checkpoint();
        for (slot, id) in marker.conjuncts.iter_mut().zip(ids) {
            let focused = self.focus_branch(id)?;
            *slot = focused
                .proposition_obligation()
                .and_then(|goal| goal.presentation.surface.clone());
            if slot.is_none()
                && let Some(kernel) = focused.goal()
            {
                if matches!(kernel, Proposition::And(..)) {
                    // Raise this subtree only if its certificate keeps the
                    // whole child as one arm. Flat certificates name leaves.
                    marker
                        .unspelled_conjuncts
                        .get_or_insert_with(|| Arc::new(self.clone()));
                } else {
                    *slot = focused.conjunct_goal_spelling(kernel).map(Arc::new);
                }
            }
        }
        Ok(marker)
    }

    pub(in crate::surface::proof) fn join_focused_both(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| {
            let mut conjuncts = marker.conjuncts.clone();
            if let Some(origin) = &marker.unspelled_conjuncts {
                for ((label, proof), id) in conjuncts.iter_mut().zip([&left, &right]).zip(ids) {
                    if label.is_none()
                        && !matches!(proof.steps(), [ProofStep::Both { .. }])
                        && let Ok(focused) = origin.focus_branch(id)
                        && let Some(goal @ Proposition::And(..)) = focused.goal()
                    {
                        *label = focused.conjunct_goal_spelling(goal).map(Arc::new);
                    }
                }
            }
            ProofStep::Both {
                conjuncts,
                left_proof: Box::new(left),
                right_proof: Box::new(right),
            }
        })
    }

    /// Splits the focused branch proposition goal into two labeled sibling case
    /// goals inside this same proof state.
    ///
    /// This is the in-`Proof` form of `cases`: the parent obligation's id is
    /// retired by the split, each arm owns the same claim under its exact
    /// disjunct in its own path-local context, and both siblings coexist in
    /// one goal collection — arms are proven by focusing each recorded id in
    /// turn on one lineage. The split marker node records this split
    /// instance; the join accepts only derivations that pass through it.
    pub(in crate::surface::proof) fn split_focused_cases(
        &self,
        disjunction: SyntaxProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        // The trace shows the disjunct each arm assumes.
        let traced_arms = crate::surface::proof_trace::enabled_for(self.claim_label()).then(|| {
            let view = crate::kernel::sequence_membership_view(&kernel);
            match view.as_ref().unwrap_or(&kernel) {
                Proposition::Or(left, right) => {
                    [vec![left.as_ref().clone()], vec![right.as_ref().clone()]]
                }
                _ => [Vec::new(), Vec::new()],
            }
        });
        let (state, split, ids) = self
            .state
            .split_proposition_cases(kernel)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`cases` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("`cases` requires a proposition goal")
                }
                PropositionSplitError::MissingDisjunction => self.step_error(format!(
                    "`cases` requires its exact disjunction as an available fact: `{}`",
                    crate::surface::diagnostics::describe_click_proposition(&disjunction)
                )),
                PropositionSplitError::ExpectedDisjunction => self.step_error(format!(
                    "`cases` requires a disjunction, got `{}`",
                    crate::surface::diagnostics::describe_click_proposition(&disjunction)
                )),
                PropositionSplitError::NonComplementaryCases => {
                    unreachable!("cases does not supply complementary branch facts")
                }
            })?
            .into_parts();
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            // The marker records the split instance in the lineage; its
            // identity is what the join verifies (identity rule 3).
            node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
        };
        if let Some(facts) = traced_arms {
            successor.record_trace_split(&successor.node, ids, &facts, "cases", ["left", "right"]);
        }
        Ok((successor, split, ids))
    }

    /// Splits the focused branch proposition goal under a condition and its exact
    /// surface negation inside this same proof state: the in-`Proof` form of
    /// proof `if`. Unlike `cases`, the condition need not be an available
    /// fact beforehand.
    pub(in crate::surface::proof) fn split_focused_if(
        &self,
        condition: SyntaxProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = SyntaxProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let traced_arms = crate::surface::proof_trace::enabled_for(self.claim_label())
            .then(|| [vec![then_fact.clone()], vec![else_fact.clone()]]);
        let (state, split, ids) = self
            .state
            .split_proposition_if(then_fact, else_fact)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`if` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("proof `if` requires a proposition goal")
                }
                PropositionSplitError::NonComplementaryCases => self.step_error(
                    "proof `if` condition and negation did not lower to complementary facts",
                ),
                PropositionSplitError::MissingDisjunction
                | PropositionSplitError::ExpectedDisjunction => {
                    unreachable!("proof if does not require a disjunction")
                }
            })?
            .into_parts();
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
        };
        if let Some(facts) = traced_arms {
            successor.record_trace_split(&successor.node, ids, &facts, "if", ["then", "else"]);
        }
        Ok((successor, split, ids))
    }

    /// Splits one retained execution frontier under an exhaustive proof-level
    /// condition. Both arms share the already-checked C state and receive only
    /// their respective logical polarity; subsequent statement steps remain
    /// independently checked on each sibling.
    pub(in crate::surface::proof) fn split_focused_execution_if(
        &self,
        condition: SyntaxProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        self.split_focused_execution_if_with_surface_condition(condition.clone(), condition)
    }

    /// The source-successor adapter has already checked that its written
    /// condition names the current C branch. Keep that checked logical case
    /// and its frozen C spelling separate, and retain the spelling before
    /// either arm executes instead of changing it after history is recorded.
    fn split_focused_execution_if_with_surface_condition(
        &self,
        condition: SyntaxProposition,
        surface_condition: SyntaxProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let else_surface = SyntaxProposition::Not(Box::new(condition.clone()));
        self.split_focused_execution_case_partition(
            [condition.clone(), else_surface],
            None,
            ProofCaseCondition::If(surface_condition),
            "proof `if`",
        )
    }

    /// Splits one retained execution frontier under `cases`: the arms take
    /// the two sides of the written disjunction, which must be an exact
    /// available fact. For more than two arms the left side is itself the
    /// disjunction of the earlier arms, split again inside the left arm.
    pub(in crate::surface::proof) fn split_focused_execution_disjunction(
        &self,
        disjunction: SyntaxProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let SyntaxProposition::Or(left, right) = &disjunction else {
            return Err(self.step_error(format!(
                "`cases` requires a disjunction, got `{}`",
                crate::surface::diagnostics::describe_click_proposition(&disjunction)
            )));
        };
        // The arms take the two sides of the disjunction as it lowered, so
        // they are exactly the sides of the available fact.
        let lowered = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        let Proposition::Or(left_fact, right_fact) = lowered else {
            return Err(self.step_error(format!(
                "`cases` disjunction `{}` did not lower to a disjunction",
                crate::surface::diagnostics::describe_click_proposition(&disjunction)
            )));
        };
        let arms = [left.as_ref().clone(), right.as_ref().clone()];
        self.split_focused_execution_case_partition(
            arms,
            Some([*left_fact, *right_fact]),
            ProofCaseCondition::Cases(disjunction),
            "`cases`",
        )
    }

    /// The shared split: each arm receives exactly its own case fact. For a
    /// proof `if` the facts are complementary; for `cases` the kernel
    /// requires their disjunction as an available fact.
    fn split_focused_execution_case_partition(
        &self,
        arm_surfaces: [SyntaxProposition; 2],
        arm_facts: Option<[Proposition; 2]>,
        case_condition: ProofCaseCondition,
        tactic: &str,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let parent_execution = branch_state
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let [then_surface, else_surface] = arm_surfaces;
        let [then_fact, else_fact] = match arm_facts {
            Some(facts) => facts,
            None => [
                self.lower_surface_proposition(&then_surface, &format!("{tactic} case"))?,
                self.lower_surface_proposition(&else_surface, &format!("{tactic} case"))?,
            ],
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution frontier has an execution context")
        };
        let arm_presentation =
            |surface_fact: SyntaxProposition, fact: &Proposition, value: bool| {
                let mut presentation = parent_execution.presentation.clone();
                presentation
                    .surface_propositions
                    .record_lowering(&surface_fact, fact)?;
                // An `if` records the polarity of its condition; each `cases`
                // arm records that its own disjunct holds, which stays true
                // where the disjuncts overlap.
                let (case_surface, case_value) = match &case_condition {
                    ProofCaseCondition::If(condition) => (condition.clone(), value),
                    ProofCaseCondition::Cases(_) => (surface_fact.clone(), true),
                };
                presentation.case_assumptions.push(CaseAssumption {
                    tactic_index: context.tactic_index,
                    condition: match &case_condition {
                        ProofCaseCondition::If(_) => then_surface.clone(),
                        ProofCaseCondition::Cases(_) => surface_fact.clone(),
                    },
                    value: match &case_condition {
                        ProofCaseCondition::If(_) => value,
                        ProofCaseCondition::Cases(_) => true,
                    },
                    fact: Some(fact.clone()),
                    match_arm: None,
                });
                // Record this checked case before its body opens nested cases.
                // Returned paths then share the already ordered prefix instead
                // of rebuilding every nested decision at each terminal join.
                presentation.branch_decisions.push(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::from(ExecutionBranchDecisions::key(
                        &case_surface,
                    )),
                    condition: case_surface,
                    value: case_value,
                });
                Ok(presentation)
            };
        let presentations = [
            arm_presentation(then_surface.clone(), &then_fact, true)?,
            arm_presentation(else_surface, &else_fact, false)?,
        ];
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_if(then_fact, else_fact, presentations)
            .map_err(|error| match error {
                FrontierSplitError::Completed => {
                    self.step_error(format!("{tactic} follows a completed proof"))
                }
                FrontierSplitError::NotFrontier => self.step_error(format!(
                    "{tactic} cannot advance C execution inside a proposition proof"
                )),
                FrontierSplitError::MissingExecution => {
                    self.step_error("execution-frontier proof lost its semantic state")
                }
                FrontierSplitError::NonComplementaryCases => match &case_condition {
                    ProofCaseCondition::If(_) => self.step_error(
                        "proof `if` condition and negation did not lower to complementary facts",
                    ),
                    ProofCaseCondition::Cases(disjunction) => self.step_error(format!(
                        "`cases` requires its exact disjunction as an available fact: `{}`",
                        crate::surface::diagnostics::describe_click_proposition(disjunction)
                    )),
                },
            })?
            .into_parts_with_facts();
        let then_branch = state
            .open_branches()
            .get(ids[0])
            .expect("the kernel returned its open then branch");
        let else_branch = state
            .open_branches()
            .get(ids[1])
            .expect("the kernel returned its open else branch");
        let then_facts = then_branch.state.facts.clone();
        let else_facts = else_branch.state.facts.clone();
        let then_execution = then_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains then execution");
        let else_execution = else_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains else execution");
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
        };
        successor.record_trace_branch(&successor.node, ids, &path_facts, &then_surface);
        let record = Box::new(ExecutionProofCaseSplitData {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            case_condition,
            base_facts: [then_facts, else_facts],
            base_executions: [then_execution, else_execution],
            path_facts,
            common_facts: branch_state.facts.clone(),
            parent_locals: self.state.locals().clone(),
            parent_execution: parent_execution.clone(),
            execution_start_state: parent_execution
                .core
                .frontier
                .execution_start_state(&parent_execution.core.state)
                .clone(),
        });
        Ok((successor, record))
    }

    /// Joins a completed in-`Proof` `if` split with one structured `If`
    /// step, under the same rules as [`Self::join_focused_cases`].
    pub(in crate::surface::proof) fn join_focused_if(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        condition: SyntaxProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::If {
            condition,
            ensuring: None,
            then_proof: Box::new(left),
            else_proof: Box::new(right),
        })
    }

    /// Joins a completed in-`Proof` case split: both recorded sibling goals
    /// must be discharged, the derivation must pass through the split's
    /// exact marker, and the retained certificate embeds each arm's steps
    /// partitioned by the per-step goal attribution recorded when they were
    /// applied — never inferred from final states.
    pub(in crate::surface::proof) fn join_focused_cases(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        disjunction: SyntaxProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::Cases {
            disjunction,
            left_proof: Box::new(left),
            right_proof: Box::new(right),
        })
    }

    /// Splits the steps recorded since `marker` into per-arm certificates by
    /// the goal attribution stamped on each node when it was applied. The
    /// derivation must pass through the split's exact marker (foreign splits
    /// of the same root collide numerically but fail pointer identity), and
    /// every step in the region must be attributed to one of the two
    /// recorded arms.
    pub(super) fn partition_steps_since(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
    ) -> Result<[Vec<ProofStep>; 2], ClickError> {
        let mut left_steps = Vec::new();
        let mut right_steps = Vec::new();
        let mut node = Some(self.node.clone());
        loop {
            let Some(current) = node else {
                return Err(self.step_error(format!(
                    "cannot join: the derivation did not pass through split {split:?}"
                )));
            };
            if Arc::ptr_eq(&current, &marker.node) {
                break;
            }
            if let Some(step) = &current.step {
                if current.focused_branch == ids[0] {
                    left_steps.push(step.as_ref().clone());
                } else if current.focused_branch == ids[1] {
                    right_steps.push(step.as_ref().clone());
                } else {
                    return Err(self.step_error(format!(
                        "cannot join: a step was attributed outside split {split:?}"
                    )));
                }
            }
            node = current.parent.clone();
        }
        left_steps.reverse();
        right_steps.reverse();
        Ok([left_steps, right_steps])
    }

    pub(super) fn join_focused_branch(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        step: impl FnOnce(ProofCertificate, ProofCertificate) -> ProofStep,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .join_closed_split(split, ids, marker.node.focused_branch)
            .map_err(|error| match error {
                ProofJoinError::ArmIncomplete(arm) => {
                    let name = ["left", "right"][arm];
                    self.step_error(format!("cannot join `cases`: {name} arm is incomplete"))
                }
                ProofJoinError::InvalidSplit => {
                    self.step_error(format!("cannot join: invalid split identity {split:?}"))
                }
            })?;
        let [left_steps, right_steps] = self.partition_steps_since(marker, split, ids)?;
        let parent = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `cases`: the split marker lost its root")
        })?;
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(
                &parent,
                marker.node.focused_branch,
                Arc::new(step(
                    ProofCertificate::from_steps(left_steps)?,
                    ProofCertificate::from_steps(right_steps)?,
                )),
            ),
        };
        if crate::surface::proof_trace::enabled_for(self.claim_label()) {
            let added = successor.state().added_facts();
            crate::surface::proof_trace::record_join(
                crate::surface::proof_trace::trace_node_key(&successor.node),
                crate::surface::proof_trace::TraceJoin {
                    marker: Arc::as_ptr(&marker.node) as usize,
                    arms: [
                        trace_arm_lineage(&self.node, &marker.node, ids[0]),
                        trace_arm_lineage(&self.node, &marker.node, ids[1]),
                    ],
                    facts: added
                        .iter()
                        .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                        .take(8)
                        .cloned()
                        .map(|fact| successor.checked_trace_fact(fact))
                        .collect(),
                    more_facts: added
                        .iter()
                        .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                        .count()
                        .saturating_sub(8),
                    continuation_arm: None,
                    arm_paths: None,
                    _retained: Box::new(self.node.clone()),
                },
            );
        }
        Ok(successor)
    }

    /// Selects the exact entry goal produced for one loop invariant. Known
    /// leading antecedents are consumed by exact lookup; all other connectives
    /// remain for the written body. The scope shares its phase's persistent
    /// facts and publishes only the goal its completed body actually proved.
    pub(in crate::surface::proof) fn begin_loop_entry_goal(
        &self,
        proposition: SyntaxProposition,
        obligation: &crate::kernel::ProofObligation,
    ) -> Result<ProofScope<'a>, ClickError> {
        let mut kernel = obligation.proposition();
        let mut stripped = 0;
        while let Proposition::Implies(antecedent, body) = kernel {
            if !self.facts().contains(antecedent) {
                break;
            }
            kernel = body;
            stripped += 1;
        }
        let introductions = obligation
            .introductions()
            .map(|record| record.get(stripped..).unwrap_or_default().to_vec());
        let mut body_surface = proposition.clone();
        // A range declaration also owes its native span bound. That goal
        // is the count comparison, not the loadability predicate; retaining
        // a theorem application must use a source spelling of the judgment
        // it actually checked. Build it from this declaration's endpoints
        // and validate it against the producer's exact obligation.
        if let SyntaxProposition::Loadable { segment } = &body_surface
            && let Some((_, start, end)) = segment.surface_range()
            && let Some((
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessEqual,
                    left: _,
                    right: limit,
                },
                true,
            )) = (kernel).condition_native()
            && let uint64_constant!(limit) = limit.as_ref()
        {
            // A zero-based span is stored as its end. Its spelling must
            // name that term, rather than introduce a new subtraction node.
            let starts_at_zero = matches!(
                start,
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(int32_constant!(0))
                        | ProgramValue::UInt32(uint32_constant!(0))
                        | ProgramValue::Int64(int64_constant!(0))
                        | ProgramValue::UInt64(uint64_constant!(0))
                ))
            ) || matches!(start, SyntaxTerm::IntegerLiteral(value) if value == "0");
            let candidate = SyntaxProposition::Comparison {
                left: if starts_at_zero {
                    end.clone()
                } else {
                    SyntaxTerm::Subtract(Box::new(end.clone()), Box::new(start.clone()))
                },
                operator: ComparisonOperator::LessEqual,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::UInt64(OldMachineTerm::uint64_constant(constant_u64(*limit))),
                )),
            };
            if self
                .lower_surface_proposition(&candidate, "loop span bound")
                .is_ok_and(|lowered| {
                    crate::kernel::proof::propositions_are_alpha_equal(&lowered, kernel)
                })
            {
                body_surface = candidate;
            }
        }
        let body = self.focus_fixed_state_goal_with_surface(kernel.clone(), Some(body_surface))?;
        let scope = ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Have {
                proposition,
                kernel: kernel.clone(),
            }),
            body,
            introduced_facts: Vec::new(),
            loop_entry_goal: Some((Arc::new(obligation.clone()), stripped)),
        };
        scope.with_reported_goal_introductions(kernel, introductions)
    }

    /// Open a nested proposition scope, reporting unmet lowering requirements
    /// through the ordinary obligation channel. This operation never schedules
    /// their proofs; the driver handles them at the original frontier.
    pub(in crate::surface::proof) fn begin_have(
        &self,
        proposition: SyntaxProposition,
        observed_spelling: bool,
    ) -> Result<ProofScope<'a>, ClickError> {
        #[cfg(test)]
        let _fast_operation = crate::kernel::search::FastOperationScope::enter("begin_have");
        #[cfg(test)]
        CHECKED_HAVE_OPERATIONS.with(|count| count.set(count.get() + 1));
        if self.state().open_branches().is_discharged() {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        match (self.focused_obligation(), self.context.as_ref()) {
            (Some(Obligation::Proposition(_) | Obligation::FunctionOutcome(_)), _) => {}
            (
                Some(Obligation::Frontier(_)),
                ProofContext::FixedState(_) | ProofContext::Execution(_),
            ) => {}
            _ => {
                return Err(
                    self.step_error("`have` requires a proposition or fixed-state proof context")
                );
            }
        }
        let (kernel, kernel_introductions) =
            self.lower_surface_goal_recording_introductions(&proposition, "`have` proposition")?;
        let proposition = if observed_spelling {
            crate::surface::proof::smart_closures::observed_native_arithmetic(&kernel, &proposition)
        } else {
            proposition
        };
        let (body_kernel, body_introductions) = (kernel.clone(), kernel_introductions);
        // Opening a frontier goal must not reconstruct an ambient composition
        // context. Its written proof establishes separation from selected
        // evidence; the direct held-resource observation below is independent.
        let at_frontier = matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        let resource_unfolded = self
            .execution()
            .is_some_and(|execution| execution.presentation.resource_unfolded);
        // The current partition can answer a selected owned-field query
        // directly. Try it before general reasoning over older compositions:
        // those may require expensive state/range transport even though
        // both current owners already establish this goal.
        let held_facts = if let Some(execution) = self.execution() {
            self.facts()
                .with_selected_held_resource_separation(&body_kernel, &execution.core.state)
        } else {
            self.facts().clone()
        };
        let body_facts = if !at_frontier || resource_unfolded {
            held_facts.with_selected_resource_separation(&body_kernel)
        } else {
            held_facts
        };
        let body_execution = self.branch_execution().cloned();
        // Outcome certification must see the assumptions that preceded this
        // scope, not the facts its checked premise-selection operations just
        // derived. Keep those selected facts in the successor below.
        let retain_outcome_root = self.focused_outcome_data().is_some();
        let body_context = BranchState {
            facts: if retain_outcome_root {
                self.facts().clone()
            } else {
                body_facts.clone()
            },
            execution: body_execution,
        };
        // An execution `have` borrows the current immutable frontier solely
        // as its proposition-lowering/theorem context, shared by identity on
        // the nested goal; a `have` stated at a function outcome borrows that
        // outcome's result-aware outcome proof data the same way. The nested goal
        // cannot publish a changed frontier or outcome: `join` restores the
        // exact root state. The named proposition is the scope
        // interface, independently of the steps used inside its body.

        let mut body_goal = match self.focused_outcome_data() {
            Some(outcome_data) => OpenBranch::surface_proposition_at_outcome(
                body_context,
                outcome_data.clone(),
                body_kernel.clone(),
                proposition.clone(),
            ),
            None => OpenBranch::surface_proposition_in(
                body_context,
                body_kernel.clone(),
                proposition.clone(),
            ),
        };
        if let Obligation::Proposition(body) = &mut body_goal.obligation
            && let Some(Obligation::Proposition(parent)) = self.focused_obligation()
        {
            body.surface_bindings = parent.surface_bindings.clone();
            body.introduced_antecedents = parent.introduced_antecedents.clone();
        }
        let selected_obligation = retain_outcome_root.then(|| body_goal.obligation.clone());
        let body_state = KernelProofObject::root(self.state().locals().clone(), body_goal);
        let body_state = if let Some(scope) = self.termination_scope() {
            body_state.with_termination_context(scope.clone())
        } else {
            body_state
        };
        let body_state = if let Some(obligation) = selected_obligation {
            body_state
                .replace_focused_obligation_and_facts(obligation, body_facts)
                .map_err(|_| self.step_error("selected have facts lost their proposition scope"))?
        } else {
            body_state
        };
        let body = Proof {
            site: self.site.nested(ProofStepBlock::Have),
            context: self.context.clone(),
            state: body_state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        };
        if crate::surface::proof_trace::enabled_for(self.claim_label()) {
            crate::surface::proof_trace::register_scope(
                Arc::as_ptr(&body.node) as usize,
                self.trace_lineage(self.claim_label())
                    .expect("trace enabled"),
                Box::new(self.node.clone()),
            );
        }
        let scope = ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Have {
                proposition,
                kernel,
            }),
            body,
            introduced_facts: Vec::new(),
            loop_entry_goal: None,
        };
        // The lowering result is also the checked report used by the
        // presentation adapter. Validate it against the fresh body's actual
        // kernel goal before installing its presentation-only metadata.
        scope.with_reported_goal_introductions(&body_kernel, body_introductions)
    }

    /// Opens one composite resource body as an execution scope. Entry is an
    /// audited representation transition, not a separately serialized
    /// `unfold`; the child Proof starts a fresh lineage and the eventual join
    /// records the child certificate inside one `Open` step.
    pub(in crate::surface::proof) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`with` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`with`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("`with` must begin before execution reaches function exit"));
        }
        let (state, introduced_facts, restoration) = if let ResourceClause::Named {
            binding,
            resource: definition,
        } = &resource
        {
            if let ResourceClause::Declared { name, .. } = definition.as_ref()
                && context
                    .resource_environment
                    .get(name)
                    .is_some_and(ResourceDefinition::is_authorized)
            {
                return Err(self.step_error(
                    "`with` on a named instance requires an ordinary composite resource",
                ));
            }
            let instance = execution
                .core
                .state
                .resource_instance_at_path(binding.instance()?, &binding.children)
                .ok_or_else(|| {
                    self.step_error(format!(
                        "`with` requires a held instance `{}`",
                        binding.name
                    ))
                })?;
            let transition =
                self.apply_instance_rewrite(binding, &resource, true, Some(instance), &[])?;
            let introduced = transition.added_facts.clone();
            let state = self.publish_checked_transition(transition)?;
            (
                state,
                introduced,
                OpenResourceRestoration::Named(Arc::new(instance.clone())),
            )
        } else {
            let before_facts = self.facts().clone();
            let checked = open_composite_resource_for_proof(
                context.resource_environment,
                &resource,
                context.parameter_binding(),
                (*execution.core.state).clone(),
                self.facts().clone(),
                &mut execution.presentation.surface_propositions,
                context.spec_definitions,
                context.claim_label,
                context.tactic_index,
            )?;
            execution
                .core
                .record_resource_rewrite(
                    context.function,
                    context.arguments,
                    &before_facts,
                    &checked.selected,
                    &checked.state,
                    &checked.facts,
                )
                .map_err(|message| {
                    self.step_error(format!(
                        "kernel rejected checked resource `with`: {message}"
                    ))
                })?;
            execution.core.state = checked.state.into();
            let introduced_facts = checked.added_facts.clone();
            let state = self
                .state
                .publish_checked_frontier_transition(
                    checked.facts,
                    execution,
                    checked.added_facts.clone(),
                    checked.added_facts,
                )
                .map_err(|error| self.execution_update_error("`with`", error))?;
            (
                state,
                introduced_facts,
                OpenResourceRestoration::Declared {
                    preserve_exposed_body: checked.body_was_already_exposed,
                },
            )
        };
        let body = Proof {
            site: self.site.nested(ProofStepBlock::Open),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: 0,
                split_branches: Vec::new(),
            }),
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Open {
                resource,
                source_index,
                restoration,
            }),
            body,
            introduced_facts,
            loop_entry_goal: None,
        })
    }
}

#[path = "../driver/branches.rs"]
mod driver;
