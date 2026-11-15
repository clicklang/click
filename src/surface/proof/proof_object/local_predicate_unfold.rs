use super::*;

impl Proof<'_> {
    /// One selected definition application. The resulting equivalence is an
    /// ordinary fact about these arguments at this state, never a policy for
    /// interpreting later propositions.
    pub(super) fn apply_local_predicate_unfold(
        &self,
        target: &ClickProposition,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let definitions = match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions,
            ProofContext::FixedState(context) => context.spec_definitions,
            ProofContext::Execution(context) => context.spec_definitions,
        };
        if let ClickProposition::PredicateCall { name, arguments } = target
            && definitions.predicates.get(name).is_none()
            && definitions.functions.get(name).is_some()
        {
            return self.apply_function_unfold(
                &ClickFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.clone(),
                },
                None,
            );
        }
        let mut names = BTreeSet::new();
        crate::surface::validation::collect_called_predicates(target, &mut names);
        if names.is_empty() {
            return Err(self.step_error("unfold requires a defined predicate application"));
        }
        let names = names.into_iter().collect::<Vec<_>>();
        let selected = if self.surface_goal() == Some(target)
            && self
                .goal()
                .is_some_and(|goal| contains_selected_kernel_predicate(goal, &names))
        {
            self.goal()
                .expect("a Surface goal has a kernel judgment")
                .clone()
        } else if matches!(target, ClickProposition::At { .. })
            && let Some(recorded) = self.execution().and_then(|execution| {
                execution
                    .presentation
                    .surface_propositions
                    .unique_kernel(target)
            })
            && self.facts().contains(recorded)
        {
            recorded.clone()
        } else {
            self.lower_surface_proposition_direct(target, "unfold application")?
        };
        let body_surface = self
            .unfold_goal_surface(definitions.predicates, target, &names)
            .map_err(|message| self.step_error(message))?;
        let body = unfold_predicates_in_proposition(
            definitions,
            &names,
            &selected,
            self.facts().assumptions(),
        )
        .map_err(|message| self.step_error(message))?;
        let equivalence = Proposition::And(
            Box::new(Proposition::Implies(
                Box::new(selected.clone()),
                Box::new(body.clone()),
            )),
            Box::new(Proposition::Implies(
                Box::new(body.clone()),
                Box::new(selected.clone()),
            )),
        );
        let mut facts = self.facts().with_kernel_checked_fact(equivalence.clone());
        let mut added = vec![equivalence];
        if self.facts().contains_quantified_identity(&selected) {
            facts = facts.with_kernel_checked_fact(body.clone());
            added.push(body.clone());
        }
        let equivalence_surface = ClickProposition::And(
            Box::new(ClickProposition::Implies(
                Box::new(target.clone()),
                Box::new(body_surface.clone()),
            )),
            Box::new(ClickProposition::Implies(
                Box::new(body_surface.clone()),
                Box::new(target.clone()),
            )),
        );
        let mut locals = self.state().locals().clone();
        locals
            .checked_lowerings
            .record_lowering(target, &selected)?;
        locals
            .checked_lowerings
            .record_lowering(&body_surface, &body)?;
        locals
            .checked_lowerings
            .record_lowering(&equivalence_surface, &added[0])?;
        let mut execution = self.execution().cloned();
        if let Some(execution) = &mut execution {
            execution
                .presentation
                .surface_propositions
                .record_lowering(&equivalence_surface, &added[0])?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(&body_surface, &body)?;
        }
        let mut state = self.refined_branch_state(facts);
        if let Some(execution) = execution {
            state.execution = Some(Arc::new(execution));
        }
        let branch = if let (Some(surface), Some(goal)) = (self.surface_goal(), self.goal()) {
            let (kernel, kernel_changed) =
                unfold_selected_kernel_goal(goal, &selected, &body, true);
            let already_open = surface == target
                && crate::kernel::proof::propositions_are_alpha_equal(goal, &body);
            if kernel_changed || already_open {
                let surface = if surface == target {
                    body_surface
                } else {
                    let mut surface = surface.clone();
                    let mut changed = false;
                    self.unfold_selected_surface_goal(
                        &mut surface,
                        &selected,
                        definitions.predicates,
                        &names,
                        &mut Vec::new(),
                        &mut BTreeSet::new(),
                        &mut changed,
                        true,
                    )?;
                    if !changed {
                        return Err(self.step_error(
                            "selected predicate occurrence has no matching Surface presentation",
                        ));
                    }
                    surface
                };
                self.refined_proposition(state, kernel, Some(surface), false)
            } else {
                self.focused_branch()
                    .expect("an open goal has a branch")
                    .with_state(state)
            }
        } else {
            self.focused_branch()
                .ok_or_else(|| self.step_error("unfold requires an open goal"))?
                .with_state(state)
        };
        Ok(CheckedFocusedTransition {
            locals,
            branch: Some(branch),
            added_facts: added.clone(),
            checked_facts: added,
        })
    }

    fn unfold_selected_surface_goal(
        &self,
        proposition: &mut ClickProposition,
        selected: &Proposition,
        predicates: &PredicateEnvironment,
        names: &[String],
        scopes: &mut Vec<ProgramPointSelector>,
        bound: &mut BTreeSet<String>,
        changed: &mut bool,
        root: bool,
    ) -> Result<(), ClickError> {
        // Only the root proposition or matching application leaves can be
        // selected. Never repeatedly lower or copy connective subtrees.
        let application = matches!(selected, Proposition::Predicate { .. })
            && matches!(proposition, ClickProposition::PredicateCall { name, .. } if names.contains(name));
        if root || application {
            let mut referenced = BTreeSet::new();
            if !bound.is_empty() {
                collect_click_proposition_referenced_names(proposition, &mut referenced);
            }
            if referenced.is_disjoint(bound) {
                let mut scoped = proposition.clone();
                for selector in scopes.iter().rev() {
                    scoped = ClickProposition::At {
                        selector: selector.clone(),
                        proposition: Box::new(scoped),
                    };
                }
                if self
                    .lower_surface_proposition_direct(&scoped, "unfold occurrence")
                    .is_ok_and(|value| {
                        crate::kernel::proof::propositions_are_alpha_equal(&value, selected)
                    })
                {
                    let mut body = self
                        .unfold_goal_surface(predicates, &scoped, names)
                        .map_err(|message| self.step_error(message))?;
                    for _ in scopes.iter() {
                        let ClickProposition::At { proposition, .. } = body else {
                            unreachable!("unfold retains explicit snapshots")
                        };
                        body = *proposition;
                    }
                    *proposition = body;
                    *changed = true;
                    return Ok(());
                }
            }
        }
        match proposition {
            ClickProposition::Value(expression) => {
                if !matches!(expression, ContractExpression::Proposition(_)) {
                    *expression = crate::surface::lambdas::reduce_head_fully(expression)
                        .map_err(|message| self.step_error(message))?
                        .into_owned();
                }
                if let ContractExpression::Proposition(body) = expression {
                    self.unfold_selected_surface_goal(
                        body, selected, predicates, names, scopes, bound, changed, false,
                    )?;
                }
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                self.unfold_selected_surface_goal(
                    left, selected, predicates, names, scopes, bound, changed, false,
                )?;
                self.unfold_selected_surface_goal(
                    right, selected, predicates, names, scopes, bound, changed, false,
                )?;
            }
            ClickProposition::Not(body) => self.unfold_selected_surface_goal(
                body, selected, predicates, names, scopes, bound, changed, false,
            )?,
            ClickProposition::At {
                selector,
                proposition,
            } => {
                scopes.push(selector.clone());
                self.unfold_selected_surface_goal(
                    proposition,
                    selected,
                    predicates,
                    names,
                    scopes,
                    bound,
                    changed,
                    false,
                )?;
                scopes.pop();
            }
            ClickProposition::ForAll { name, body, .. }
            | ClickProposition::Exists { name, body, .. } => {
                let inserted = bound.insert(name.clone());
                self.unfold_selected_surface_goal(
                    body, selected, predicates, names, scopes, bound, changed, false,
                )?;
                if inserted {
                    bound.remove(name);
                }
            }
            ClickProposition::RangeAll { item, body, .. }
            | ClickProposition::RangeAny { item, body, .. } => {
                let inserted = bound.insert(item.clone());
                self.unfold_selected_surface_goal(
                    body, selected, predicates, names, scopes, bound, changed, false,
                )?;
                if inserted {
                    bound.remove(item);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

// Substitute only exact selected judgments in the retained kernel goal. Source
// lowering never chooses the meaning of a goal that already has a judgment.
fn unfold_selected_kernel_goal(
    goal: &Proposition,
    selected: &Proposition,
    body: &Proposition,
    root: bool,
) -> (Proposition, bool) {
    fn rewrite(
        goal: &mut Proposition,
        selected: &Proposition,
        body: &Proposition,
        root: bool,
    ) -> bool {
        if (root
            || matches!(
                (&*goal, selected),
                (Proposition::Predicate { .. }, Proposition::Predicate { .. })
            ))
            && crate::kernel::proof::propositions_are_alpha_equal(goal, selected)
        {
            *goal = crate::kernel::clone_proposition_iteratively(body);
            return true;
        }
        match goal {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                let left_changed = rewrite(left, selected, body, false);
                let right_changed = rewrite(right, selected, body, false);
                left_changed || right_changed
            }
            Proposition::Not(inner)
            | Proposition::ForAll { body: inner, .. }
            | Proposition::Exists { body: inner, .. } => rewrite(inner, selected, body, false),
            _ => false,
        }
    }
    let mut result = crate::kernel::clone_proposition_iteratively(goal);
    let changed = rewrite(&mut result, selected, body, root);
    (result, changed)
}

fn contains_selected_kernel_predicate(proposition: &Proposition, names: &[String]) -> bool {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::Predicate { name, .. } => {
                if names.iter().any(|selected| {
                    name == selected
                        || name
                            .strip_prefix(selected)
                            .is_some_and(|suffix| suffix.starts_with("::<"))
                }) {
                    return true;
                }
            }
            Proposition::And(a, b) | Proposition::Or(a, b) | Proposition::Implies(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => pending.push(body),
            _ => {}
        }
    }
    false
}
