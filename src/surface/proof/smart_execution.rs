//! Smart execution search, fact transport, and theorem selection.

use super::proof_object::StepUntilTarget;
use super::*;
use std::collections::BTreeSet;

impl<'a> Proof<'a> {
    /// The guarantees of a theorem application as the caller would write
    /// them: each `ensures` of the applied theorem with the application's
    /// arguments substituted for its parameters, in declaration order.
    ///
    /// This spells conclusions; it establishes nothing. The caller retains
    /// one only after matching it against a fact the checked application
    /// added, so an application this cannot spell yields no conclusions
    /// rather than an error. A generic theorem is spelled only in a pure
    /// theorem proof, where its type instance is inferred from the
    /// arguments alone.
    pub(in crate::surface::proof) fn theorem_application_surface_conclusions(
        &self,
        application: &TheoremApplication,
    ) -> Vec<ClickProposition> {
        let Some((theorem, substitutions)) = self.theorem_application_instance(application) else {
            return Vec::new();
        };
        theorem
            .ensures()
            .iter()
            .filter_map(|ensure| match ensure.ensure() {
                Ensure::Proposition(conclusion) => substitute_click_proposition(
                    &crate::surface::proof::theorem_application::observe_machine_parameters(
                        conclusion,
                        theorem.parameters(),
                        &substitutions,
                    ),
                    &substitutions,
                )
                .ok(),
                _ => None,
            })
            .collect()
    }

    /// The theorem `application` names, instantiated, and its parameters'
    /// substitutions by the application's written arguments. A generic
    /// theorem is instantiated only in a pure theorem proof, where its type
    /// instance is inferred from the arguments alone.
    pub(super) fn theorem_application_instance(
        &self,
        application: &TheoremApplication,
    ) -> Option<(TheoremDefinition, BTreeMap<String, ContractExpression>)> {
        let written = application;
        let application = self.resolve_theorem_application(application).ok()?;
        let theorem_environment = match self.context.as_ref() {
            ProofContext::Pure(context) => context.theorem_environment,
            ProofContext::FixedState(context) => context.theorem_environment,
            ProofContext::Execution(context) => context.theorem_environment,
        };
        let theorem = theorem_environment.get(&application.name)?;
        let theorem = if theorem.type_parameters().is_empty() {
            theorem.clone()
        } else {
            let ProofContext::Pure(context) = self.context.as_ref() else {
                return None;
            };
            let state = ExecutionState::at_point(&context.theorem_context.point);
            let recorded_states = RecordedStates::new();
            let algebraic_values = application
                .arguments
                .iter()
                .flat_map(contract_expression_referenced_names)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .filter_map(|name| {
                    self.known_algebraic_value(&name)
                        .cloned()
                        .or_else(|| {
                            self.structural_induction_setup()?
                                .algebraic_values
                                .get(&name)
                                .cloned()
                        })
                        .map(|value| (name, value))
                })
                .collect();
            let application_context = TheoremApplicationContext {
                parameters: ParameterBinding::default(),
                values: &context.theorem_context.values,
                array_refs: &context.theorem_context.array_refs,
                algebraic_values: &algebraic_values,
                pre_state: &state,
                post_state: &state,
                result: None,
                recorded_states: &recorded_states,
                integer_values: &context.theorem_context.integer_values,
                pointer_element_widths: BTreeMap::new(),
            };
            let Ok(theorem) = instantiate_generic_theorem_application_definition(
                theorem,
                &application,
                self.facts().assumptions(),
                &application_context,
                context.spec_definitions,
            ) else {
                return None;
            };
            theorem
        };
        if theorem.parameters().len() != application.arguments.len() {
            return None;
        }
        // The written arguments, not the resolved ones: resolution replaces
        // a `match` arm's C binding by its kernel value, which has no
        // spelling.
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(written.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        Some((theorem, substitutions))
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/smart_execution.rs");
}

// Discovery methods are deliberately not methods of Proof.

// Source spelling adapters for the kernel ProofSearch interface.
mod history_equalities;
mod search;

#[path = "driver/theorems.rs"]
mod driver;
