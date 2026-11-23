//! Structural hypotheses follow the checked declaration and ordinary match scopes.
use super::*;
use crate::surface::proof::pure_theorems::{
    PureStructuralInductionApplication, structural_induction_hypothesis_substitution,
};

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn uses_structural_induction(&self) -> bool {
        matches!(self.context.as_ref(), ProofContext::Pure(context)
            if context.induction_setup.as_ref().is_some_and(|setup| setup.structural_parameters.is_some()))
    }

    pub(in crate::surface::proof) fn structural_induction_setup(
        &self,
    ) -> Option<&PureStructuralInductionBranchSetup> {
        self.state().locals().structural_induction_setup.as_deref()
    }

    pub(in crate::surface::proof) fn restore_induction_scope_from(&self, parent: &Self) -> Self {
        let mut locals = self.state().locals().clone();
        locals.induction_active = parent.state().locals().induction_active;
        locals.structural_induction_setup =
            parent.state().locals().structural_induction_setup.clone();
        self.with_kernel_state(self.state.with_locals(locals))
    }

    /// Instantiates the selected theorem at one of this case's immediate
    /// recursive fields. Argument lowering reads the current lexical locals;
    /// a name rebound to a different value cannot acquire the old field's IH.
    pub(in crate::surface::proof) fn structural_induction_instance(
        &self,
        hypothesis: &str,
        arguments: &[ContractExpression],
    ) -> Result<PureStructuralInductionApplication, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("induction application requires a pure theorem proof"));
        };
        let setup = context
            .induction_setup
            .as_ref()
            .filter(|_| self.state().locals().induction_active)
            .ok_or_else(|| self.step_error("induction hypothesis is not active"))?;
        let parameters = setup
            .structural_parameters
            .as_ref()
            .ok_or_else(|| self.step_error("structural induction hypothesis is not active"))?;
        let case = self.structural_induction_setup().ok_or_else(|| {
            self.step_error(
                "structural induction hypothesis expects an immediate recursive field from a match",
            )
        })?;
        if hypothesis != setup.hypothesis || hypothesis != case.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        let argument = super::super::pure_theorems::structural_induction_descent_argument(
            case.parameter_index,
            arguments,
        )
        .ok_or_else(|| {
            self.step_error("structural induction hypothesis expects an immediate recursive field")
        })?;
        let name =
            super::super::pure_theorems::induction_argument_name(argument).ok_or_else(|| {
                self.step_error(
                    "structural induction hypothesis expects an immediate recursive field",
                )
            })?;
        let expected = case.algebraic_values.get(name).ok_or_else(|| {
            self.step_error("structural induction hypothesis expects an immediate recursive field")
        })?;
        let actual = self.capture_pure_algebraic_witness(argument)?;
        if actual.algebraic_type != expected.algebraic_type
            || !matches!((&actual.node, &expected.node),
            (crate::kernel::AlgebraicTermNode::Variable(actual), crate::kernel::SpecAlgebraicExpressionNode::Variable(expected)) if actual == expected)
        {
            return Err(self.step_error(
                "structural induction hypothesis expects the original immediate recursive field",
            ));
        }
        let substitution = structural_induction_hypothesis_substitution(
            parameters,
            &setup.parameter,
            hypothesis,
            arguments,
        )?;
        let mut surface_premises = Vec::new();
        for requirement in &setup.surface_requires {
            let premise = substitute_click_proposition(requirement, &substitution)
                .map_err(ClickError::new)?;
            if !surface_premises.contains(&premise) {
                surface_premises.push(premise);
            }
        }
        let kernel_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "structural induction premise"))
            .collect::<Result<Vec<_>, _>>()?;
        let surface_conclusion = substitute_click_proposition(&setup.surface_goal, &substitution)
            .map_err(ClickError::new)?;
        let conclusion =
            self.lower_surface_proposition(&surface_conclusion, "structural induction conclusion")?;
        let implication = kernel_premises
            .iter()
            .rev()
            .fold(conclusion.clone(), |body, premise| {
                let body = crate::kernel::stated_loadable_span_guards(premise)
                    .into_iter()
                    .rev()
                    .fold(body, |body, guard| {
                        Proposition::Implies(Box::new(guard), Box::new(body))
                    });
                Proposition::Implies(Box::new(premise.clone()), Box::new(body))
            });
        Ok(PureStructuralInductionApplication {
            kernel_premises,
            surface_premises,
            implication,
            conclusion,
        })
    }

    /// The ordinary match's checked constructor equation specializes the
    /// original theorem requirements without replaying the proof prefix.
    pub(in crate::surface::proof) fn structural_case_equality(
        &self,
        source: &ContractExpression,
        arm: &ProofInductionArm,
    ) -> ClickProposition {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        let setup = context
            .induction_setup
            .as_ref()
            .expect("structural declaration");
        let parameter = setup
            .structural_parameters
            .as_ref()
            .expect("structural parameters")
            .iter()
            .find(|p| p.name() == setup.parameter)
            .expect("checked parameter");
        let ClickType::Algebraic(algebraic_type) = parameter.click_type() else {
            unreachable!()
        };
        let constructor = ContractExpression::AlgebraicConstructor {
            algebraic_type: algebraic_type.clone(),
            variant: arm.variant.clone(),
            arguments: arm
                .bindings
                .iter()
                .map(|name| ContractExpression::Binding(name.clone()))
                .collect(),
        };
        ClickProposition::Comparison {
            left: source.clone(),
            operator: ComparisonOperator::Equal,
            right: constructor,
        }
    }

    /// Preserve constructor-specific goals inside the arm and return to the
    /// original scrutinee spelling before running a shared continuation.
    pub(in crate::surface::proof) fn refine_structural_case_goal(
        &self,
        source: &ContractExpression,
        arm: &ProofInductionArm,
        reverse: bool,
    ) -> Result<Self, ClickError> {
        if self
            .goal()
            .is_none_or(|goal| matches!(normalize_proposition(goal), NormalizedProposition::True))
        {
            return Ok(self.clone());
        }
        let mut equality = self.structural_case_equality(source, arm);
        if reverse && let ClickProposition::Comparison { left, right, .. } = &mut equality {
            std::mem::swap(left, right);
        }
        if self
            .surface_goal()
            .and_then(|goal| rewrite_click_proposition_by_surface_equality(goal, &equality))
            .is_none()
        {
            return Ok(self.clone());
        }
        let mut transition = self.apply_pure_rewrite(&equality)?;
        transition.clear_existential_projection();
        let state = self.publish_checked_transition(transition)?;
        let mut proof = self.with_kernel_state(state);
        if reverse {
            // Expansion moves the shared continuation into each arm. Retain
            // this already checked rewrite so replay reaches that same goal.
            proof.node = ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::Rewrite(equality)),
            );
        }
        Ok(proof)
    }

    /// Constructor coverage and fresh field identities come from the ordinary
    /// kernel match. Publish only the IH instances for this written arm's
    /// immediate fields, at the theorem's fixed remaining parameters.
    pub(in crate::surface::proof) fn enter_structural_induction_case(
        &self,
        source: &ContractExpression,
        arm: &ProofInductionArm,
    ) -> Result<Self, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Ok(self.clone());
        };
        let setup = context
            .induction_setup
            .as_ref()
            .expect("selected structural declaration");
        let parameters = setup
            .structural_parameters
            .as_ref()
            .expect("structural parameters");
        let parameter_index = parameters
            .iter()
            .position(|p| p.name() == setup.parameter)
            .expect("checked parameter");
        let root = setup
            .structural_root
            .as_ref()
            .expect("checked structural parameter");
        let mut algebraic_values = BTreeMap::new();
        for name in &arm.bindings {
            if let Some(value) = self.local_algebraic_values().get(name)
                && value.algebraic_type == root.algebraic_type
            {
                algebraic_values.insert(name.clone(), value.clone());
            }
        }
        let recursive_bindings = algebraic_values.keys().cloned().collect::<Vec<_>>();
        let mut locals = self.state().locals().clone();
        locals.structural_induction_setup = Some(Arc::new(PureStructuralInductionBranchSetup {
            hypothesis: setup.hypothesis.clone(),
            parameter_index,
            algebraic_values,
        }));
        let entered = self.with_kernel_state(self.state.with_locals(locals));
        let mut facts = entered.facts().clone();
        let mut added = Vec::new();
        let equality = entered.structural_case_equality(source, arm);
        for requirement in &setup.surface_requires {
            if let Some(specialized) =
                rewrite_click_proposition_by_surface_equality(requirement, &equality)
            {
                let premise = entered
                    .lower_surface_proposition(&specialized, "constructor theorem requirement")?;
                facts = facts.with_kernel_checked_fact(premise.clone());
                added.push(premise);
            }
        }
        for name in recursive_bindings {
            let instance = entered.structural_induction_instance(
                &setup.hypothesis,
                &[ContractExpression::Binding(name)],
            )?;
            facts = facts.with_kernel_checked_fact(instance.implication.clone());
            added.push(instance.implication);
        }
        let transition = entered.checked_fact_transition(
            entered.state().locals().clone(),
            facts,
            false,
            added.clone(),
            added,
        );
        let state = entered.publish_checked_transition(transition)?;
        Ok(entered.with_kernel_state(state))
    }
}
